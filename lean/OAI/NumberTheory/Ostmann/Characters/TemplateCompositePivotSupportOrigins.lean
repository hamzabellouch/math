import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

structure SampleOrigins (k j : ℕ) (ι : Type*) where
  origin : (schedule k j).Slot → Option ι
  missing : ∀ i, origin i = none → ∃ l, j ≤ l ∧ (schedule k j).IsPivot l i

namespace SampleOrigins
variable {k j : ℕ} {ι : Type*}

def root (k J : ℕ) : SampleOrigins k J (schedule k J).Slot where
  origin := some
  missing := by intro i hi; cases hi

def child (o : SampleOrigins k (j+1) ι) (b : Bool) : SampleOrigins k j ι where
  origin i := if hp : (schedule k j).IsPivot j i then none
    else if hc : (schedule k j).IsCopied j i then o.origin (.inl (⟨i,hc⟩,b))
    else o.origin (.inr ⟨i,hp,hc⟩)
  missing := by
    intro i hn
    by_cases hp : (schedule k j).IsPivot j i
    · exact ⟨j,le_rfl,hp⟩
    · by_cases hc : (schedule k j).IsCopied j i
      · simp only [dite_eq_right hp,dite_eq_left hc] at hn
        obtain ⟨l,hl,hp'⟩ := o.missing (.inl (⟨i,hc⟩,b)) hn
        exact ⟨l,Nat.le_of_succ_le hl,hc.1,hp'.2⟩
      · simp only [dite_eq_right hp,dite_eq_right hc] at hn
        obtain ⟨l,hl,hp'⟩ := o.missing (.inr ⟨i,hp,hc⟩) hn
        exact ⟨l,Nat.le_of_succ_le hl,hp'⟩

theorem outside_exists (o : SampleOrigins k (j+1) ι)
    (i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i}) :
    ∃ a, o.origin (.inr i) = some a := by
  cases he : o.origin (.inr i) with
  | some a => exact ⟨a,rfl⟩
  | none =>
    obtain ⟨l,hl,hp⟩ := o.missing (.inr i) he
    exact False.elim (i.property.2
      (future_pivot_copied (schedule k j) j l hl i.val hp.1 hp.2))

def outside (o : SampleOrigins k (j+1) ι)
    (i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i}) : ι :=
  Classical.choose (o.outside_exists i)

theorem origin_outside (o : SampleOrigins k (j+1) ι)
    (i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i}) :
    o.origin (.inr i) = some (o.outside i) := Classical.choose_spec (o.outside_exists i)

def Matches (o : SampleOrigins k j ι) (ξ : ι → ℤ) (x : State k j) : Prop :=
  ∀ i a, o.origin i = some a → x i = ξ a

theorem root_matches (k J : ℕ) (x : State k J) : (root k J).Matches x x := by
  intro i a h
  cases Option.some.inj h
  rfl

theorem Matches.child {o : SampleOrigins k (j+1) ι} {ξ : ι → ℤ} {x : State k (j+1)}
    (hm : o.Matches ξ x) (b : Bool) (P : ℤ) :
    (o.child b).Matches ξ (childState k j b x P) := by
  intro i a ha
  change (o.child b).origin i = some a at ha
  by_cases hp : (schedule k j).IsPivot j i
  · simp only [SampleOrigins.child,dite_eq_left hp] at ha
    cases ha
  · by_cases hc : (schedule k j).IsCopied j i
    · simp only [SampleOrigins.child,dite_eq_right hp,dite_eq_left hc] at ha
      simpa only [childState,dite_eq_right hp,dite_eq_left hc] using hm _ a ha
    · simp only [SampleOrigins.child,dite_eq_right hp,dite_eq_right hc] at ha
      simpa only [childState,dite_eq_right hp,dite_eq_right hc] using hm _ a ha

theorem Matches.outside {o : SampleOrigins k (j+1) ι} {ξ : ι → ℤ} {x : State k (j+1)}
    (hm : o.Matches ξ x)
    (i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i}) :
    x (.inr i) = ξ (o.outside i) := hm _ _ (o.origin_outside i)

end SampleOrigins
end Ostmann.Characters.Template

end

end OAI
