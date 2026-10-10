import OAI.Combinatorics.BalancedRyser.Incidence.AlignedFreshIncidence
import OAI.Combinatorics.BalancedRyser.Local.AlignedUsedObservable

namespace OAI

namespace Balanced.Local.AlignedGlobal

open TupleAlignment RootChildPartition
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem uniform_coordinate_line_probability_le {I : Type*} [Fintype I]
    [DecidableEq I] (i : I) (S : Line F) (l : (I → F) → Line F)
    (hl : ∀ x t, l (Function.update x i t) = l x)
    (f : F → Point F) (hf : Function.Injective f) (hS : ∀ t, OnLine (f t) S) :
    ((PMF.uniformOfFintype (I → F)).toOuterMeasure
      {x | l x ≠ S ∧ OnLine (f (x i)) (l x)}).toReal ≤
      1 / (Fintype.card F : ℝ) := by
  rw [FiniteUniformFibers.probability_eq_sum, ← Fintype.expect_eq_sum_div_card,
    ← DependencyExtraction.expect_coordinate_refresh i]
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  simp_rw [hl, Function.update_self]
  have h := LocalFiberBounds.nonTarget_line_union_probability_le S {l x} f hf hS
  simp only [Finset.mem_singleton, exists_eq_left, Finset.card_singleton,
    Nat.cast_one] at h
  rw [FiniteUniformFibers.probability_eq_sum, ← Fintype.expect_eq_sum_div_card] at h
  convert h using 1; first
  | rfl
  | (apply Finset.expect_congr rfl; intro t _; split_ifs <;> rfl)

theorem generatedZero_free {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F) (ij : FreeIndex P R) :
    prescribedPoint P a bits (generatedZero P hκ R hD a ha bits p x) ij.1 =
      ((linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm (x ij)).1 :=
  generated_free P hκ R hD a ha bits p (x, fun _ _ => 0) ij

theorem generatedZero_fresh_incidence_le {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (ij : FreeIndex P R)
    (l : (FreeIndex P R → F) → Line F)
    (hl : ∀ x t, l (Function.update x ij t) = l x) :
    ((PMF.uniformOfFintype (FreeIndex P R → F)).toOuterMeasure
      {x | l x ≠ lineThrough (a.1 ij.1.1) p ∧
        OnLine (prescribedPoint P a bits (generatedZero P hκ R hD a ha bits p x) ij.1)
          (l x)}).toReal ≤ 1 / (Fintype.card F : ℝ) := by
  let f : F → Point F := fun t =>
    ((linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm t).1
  have heq : {x | l x ≠ lineThrough (a.1 ij.1.1) p ∧
      OnLine (prescribedPoint P a bits (generatedZero P hκ R hD a ha bits p x) ij.1) (l x)} =
      {x | l x ≠ lineThrough (a.1 ij.1.1) p ∧ OnLine (f (x ij)) (l x)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [generatedZero_free P hκ R hD a ha bits p x ij]
  rw [heq]
  apply uniform_coordinate_line_probability_le ij _ l hl f
  · intro t u h
    exact (linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm.injective
      (Subtype.ext h)
  · intro t
    exact ((linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm t).2

end
end Balanced.Local.AlignedGlobal

end OAI
