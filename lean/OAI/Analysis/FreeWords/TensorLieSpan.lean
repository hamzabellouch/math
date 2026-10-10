import Mathlib
import OAI.Analysis.FreeWords.TensorLieKernel

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators

noncomputable section

def positionMatrix {r d : ℕ} (π : Equiv.Perm (Fin r)) :
    Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ :=
  fun a b => if b = a ∘ π then 1 else 0

def labelCount {r d : ℕ} (a : Fin r → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter (fun s => a s=i)).card

theorem labelCount_pos_iff {r d : ℕ} (a : Fin r → Fin d) (i : Fin d) :
    0 < labelCount a i ↔ ∃ s, a s=i := by
  classical
  simp [labelCount,Finset.card_pos,Finset.Nonempty]

theorem LieInvariant.count_eq {r d : ℕ} {T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ}
    (hT : LieInvariant T) {a b : Fin r → Fin d} (hne : T a b ≠ 0) (i : Fin d) :
    labelCount a i=labelCount b i := by
  classical
  have hl : ∀ s, (if a s=i then T (Function.update a s i) b else 0) =
      (if a s=i then T a b else 0) := by
    intro s
    split_ifs with hs
    · rw [← hs,Function.update_eq_self]
    · rfl
  have hr : ∀ s, (if b s=i then T a (Function.update b s i) else 0) =
      (if b s=i then T a b else 0) := by
    intro s
    split_ifs with hs
    · rw [← hs,Function.update_eq_self]
    · rfl
  have he := hT i i a b
  simp only [hl,hr,← Finset.sum_filter] at he
  have he' : (labelCount a i : ℂ)*T a b = (labelCount b i : ℂ)*T a b := by
    simpa [labelCount] using he
  exact_mod_cast mul_right_cancel₀ hne he'

theorem orbit_of_labelCount_eq {r d : ℕ} (a b : Fin r → Fin d)
    (ha : Function.Injective a) (hcount : ∀ i, labelCount a i=labelCount b i) :
    ∃ π : Equiv.Perm (Fin r), b=a ∘ π := by
  classical
  have hf : ∀ s, ∃ t, a t=b s := by
    intro s
    apply (labelCount_pos_iff a (b s)).mp
    rw [hcount]
    exact (labelCount_pos_iff b (b s)).mpr ⟨s,rfl⟩
  choose f hf using hf
  have hsur : Function.Surjective f := by
    intro t
    have hh : 0 < labelCount b (a t) := by
      rw [← hcount]
      exact (labelCount_pos_iff a (a t)).mpr ⟨t,rfl⟩
    obtain ⟨s,hs⟩ := (labelCount_pos_iff b (a t)).mp hh
    exact ⟨s,ha ((hf s).trans hs)⟩
  refine ⟨Equiv.ofBijective f hsur.bijective_of_finite,?_⟩
  funext s
  exact (hf s).symm

theorem update_exchange {ι α : Type*} [DecidableEq ι] (a b : ι → α) (s : ι) (i j : α) :
    (a s=i ∧ b=Function.update a s j) ↔
      (b s=j ∧ a=Function.update b s i) := by
  constructor <;> rintro ⟨h,rfl⟩
  · constructor
    · simp
    · simp [Function.update_idem,← h]
  · constructor
    · simp
    · simp [Function.update_idem,← h]

theorem positionMatrix_lieInvariant {r d : ℕ} (π : Equiv.Perm (Fin r)) :
    LieInvariant (positionMatrix (d := d) π) := by
  classical
  intro i j a b
  conv_rhs => rw [← Equiv.sum_comp π.symm]
  apply Finset.sum_congr rfl
  intro s _
  have hc : Function.update a s j ∘ π = Function.update (a ∘ π) (π.symm s) j := by
    simpa using Function.update_comp_eq_of_injective a π.injective (π.symm s) j
  have he := update_exchange (a ∘ π) b (π.symm s) i j
  simp only [Function.comp_apply,Equiv.apply_symm_apply] at he
  simp only [positionMatrix,hc,← ite_and]
  have he' : (a s=i ∧ b=Function.update (a ∘ π) (π.symm s) j) ↔
      (b (π.symm s)=j ∧ Function.update b (π.symm s) i=a ∘ π) := by
    simpa only [eq_comm] using he
  simp only [he']

theorem LieInvariant.sub {r d : ℕ} {S T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ}
    (hS : LieInvariant S) (hT : LieInvariant T) : LieInvariant (S-T) := by
  classical
  intro i j a b
  have hh (p : Prop) [Decidable p] (x y : ℂ) :
      (if p then x-y else 0)=(if p then x else 0)-(if p then y else 0) := by
    split_ifs <;> simp
  simp only [Matrix.sub_apply,hh,Finset.sum_sub_distrib]
  rw [hS i j a b,hT i j a b]

theorem position_sum_lieInvariant {r d : ℕ} (c : Equiv.Perm (Fin r) → ℂ) :
    LieInvariant (∑ π, c π • positionMatrix (d := d) π) := by
  classical
  intro i j a b
  have hh (p : Prop) [Decidable p] (f : Equiv.Perm (Fin r) → ℂ) :
      (if p then ∑ π, c π*f π else 0)=∑ π, c π*(if p then f π else 0) := by
    split_ifs <;> simp
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  simp_rw [hh]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  simp only [← Finset.mul_sum]
  rw [positionMatrix_lieInvariant π i j a b]

theorem lie_label_span {r d : ℕ} (hrd : r ≤ d)
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ) (hT : LieInvariant T)
    (hlabel : ∀ (g : Equiv.Perm (Fin d)) a b, T (g ∘ a) (g ∘ b)=T a b) :
    ∃ c : Equiv.Perm (Fin r) → ℂ, T=∑ π, c π • positionMatrix π := by
  classical
  let a₀ : Fin r → Fin d := Fin.castLE hrd
  have ha₀ : Function.Injective a₀ := Fin.castLE_injective hrd
  let c : Equiv.Perm (Fin r) → ℂ := fun π => T a₀ (a₀ ∘ π)
  let S : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ := ∑ π, c π • positionMatrix π
  have hrow (b : Fin r → Fin d) : T a₀ b=S a₀ b := by
    by_cases ho : ∃ π : Equiv.Perm (Fin r), b=a₀ ∘ π
    · obtain ⟨π,rfl⟩ := ho
      have he (σ : Equiv.Perm (Fin r)) : a₀ ∘ π=a₀ ∘ σ ↔ π=σ := by
        constructor
        · intro hh
          apply Equiv.ext
          intro s
          exact ha₀ (congrFun hh s)
        · rintro rfl; rfl
      simp [S,Matrix.sum_apply,positionMatrix,he,c]
    · have hz : T a₀ b=0 := by
        by_contra hne
        exact ho (orbit_of_labelCount_eq a₀ b ha₀ (hT.count_eq hne))
      simp [S,Matrix.sum_apply,positionMatrix,hz,show ∀ π : Equiv.Perm (Fin r), b ≠ a₀ ∘ π from fun π hh => ho ⟨π,hh⟩]
  have hSl (g : Equiv.Perm (Fin d)) (a b : Fin r → Fin d) : S (g ∘ a) (g ∘ b)=S a b := by
    dsimp only [S]
    simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro π _
    have hh : g ∘ b=(g ∘ a) ∘ π ↔ b=a ∘ π := by
      constructor
      · intro he
        funext s
        exact g.injective (congrFun he s)
      · rintro rfl; rfl
    simp only [positionMatrix,hh]
  have hz : T-S=0 := by
    apply lieInvariant_eq_zero_of_injective_rows hrd (T-S) (hT.sub (position_sum_lieInvariant c))
    intro a ha b
    obtain ⟨g,hg⟩ := Equiv.Perm.exists_extending_pair a₀ a ha₀ ha
    have hga : g ∘ a₀=a := funext hg
    have hgb : g ∘ (g.symm ∘ b)=b := by ext; simp
    have ht := hlabel g a₀ (g.symm ∘ b)
    have hs := hSl g a₀ (g.symm ∘ b)
    rw [hga,hgb] at ht hs
    change T a b-S a b=0
    rw [ht,hs,hrow,sub_self]
  exact ⟨c,sub_eq_zero.mp hz⟩

end

end KKWeingarten
end

end OAI
