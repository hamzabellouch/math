import OAI.NumberTheory.Ostmann.Characters.TemplateGraphCore

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def Layout.IsRegular (T : Layout) (j : ℕ) (i : T.Slot) : Prop :=
  T.eligible i ∧ (T.role i=.word ∨ ∃l,j≤l ∧ T.role i=.pivot l)

theorem step_regular_cases (T : Layout) (j : ℕ) (i : (T.step j).Slot)
    (hi : (T.step j).IsRegular (j+1) i) :
    ∃q:{q:T.Slot // T.IsCopied j q},∃t:Bool,
      i=.inl (q,t) ∧ T.IsRegular j q.val := by
  cases i with
  | inl q =>
    refine ⟨q.1,q.2,rfl,q.1.property.1,?_⟩
    rcases hi.2 with hw | ⟨l,hl,hp⟩
    · exact Or.inl hw
    · exact Or.inr ⟨l,by omega,hp⟩
  | inr q =>
    exfalso
    apply q.property.2
    rcases hi.2 with hw | ⟨l,hl,hp⟩
    · exact word_copied T j q.val hi.1 hw
    · exact future_pivot_copied T j l hl q.val hi.1 hp

theorem graph_regular (k : ℕ) : ∀j,j≤k → ∀i:(schedule k j).Slot,
    (schedule k j).IsRegular j i → ∀z,z≠i → graph k j i z=(rowSign k j i:ℤ) := by
  intro j
  induction j with
  | zero =>
    intro hj i hi z hz
    simp only [graph,ite_eq_right hz.symm,rowSign,Units.val_one]
  | succ j ih =>
    intro hj i hi z hz
    obtain ⟨q,t,rfl,hq⟩ := step_regular_cases (schedule k j) j i hi
    rw [graph_succ k j hj]
    simpa only [rowSign,Units.val_mul,copyUnit_coe] using
      graphStep_regular (schedule k j) j (pivotSlot k j hj) (graph k j) q (rowSign k j q.val)
        (ih (by omega) q.val hq) t z hz

theorem futurePivot_rowSign (k : ℕ) : ∀j l,j≤l → ∀i:(schedule k j).Slot,
    (schedule k j).IsPivot l i → rowSign k j i=1 := by
  intro j
  induction j with
  | zero => intro l hj i hi; rfl
  | succ j ih =>
    intro l hj i hi
    cases i with
    | inl q =>
      have ht : q.2=true := by
        rcases hi.1 with hw | ⟨r,hr,ht⟩
        · have he : Role.pivot l=Role.word := hi.2.symm.trans hw
          contradiction
        · exact ht
      have ho : (schedule k j).IsPivot l q.1.val := ⟨q.1.property.1,hi.2⟩
      simp only [rowSign,ht,copyUnit,ite_true,one_mul,ih l (by omega) q.1.val ho]
    | inr q =>
      exact False.elim (q.property.2
        (future_pivot_copied (schedule k j) j l hj q.val hi.1 hi.2))

@[simp] theorem pivotSlot_rowSign (k j : ℕ) (hj : j<k) :
    rowSign k j (pivotSlot k j hj).val=1 :=
  futurePivot_rowSign k j j le_rfl _ (pivotSlot k j hj).property

private theorem anchor_ne_regular (T : Layout) (j l : ℕ) (big : Bool)
    {a i:T.Slot} (ha:T.role a=.anchor l big) (hi:T.IsRegular j i) : a≠i := by
  intro he
  subst i
  rcases hi.2 with hw | ⟨r,_,hp⟩
  · rw [ha] at hw; contradiction
  · rw [ha] at hp; contradiction

theorem futureAnchor_regular_entry (k : ℕ) : ∀j,j≤k → ∀l,j≤l → ∀big,
    ∀a:(schedule k j).Slot,(schedule k j).eligible a → (schedule k j).role a=.anchor l big →
    ∀i:(schedule k j).Slot,(schedule k j).IsRegular j i →
      graph k j a i=(rowSign k j i:ℤ) := by
  intro j
  induction j with
  | zero =>
    intro hj l hjl big a hae har i hi
    simp only [graph,ite_eq_right (anchor_ne_regular _ 0 l big har hi),rowSign,Units.val_one]
  | succ j ih =>
    intro hj l hjl big a hae har i hi
    obtain ⟨q,t,rfl,hq⟩ := step_regular_cases (schedule k j) j i hi
    cases a with
    | inl a =>
      exact False.elim ((future_anchor_outside (schedule k j) j l hjl big a.1.val har).2 a.1.property)
    | inr a =>
      rw [graph_succ k j hj]
      change copySign t * graph k j a.val q.val = _
      rw [ih (by omega) l (by omega) big a.val hae har q.val hq]
      simp only [rowSign,Units.val_mul,copyUnit_coe]

end Ostmann.Characters.Template

end

end OAI
