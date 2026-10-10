import OAI.MeasureTheory.Falconer.Estimates.ClassRecombination

namespace OAI

/-! # Original class masses do not introduce a class-count loss -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem retained_classes_bad_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [SFinite ν]
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (f : CellPath d → List ℕ) (F : Finset (List ℕ)) (hF : F ⊆ L.image f)
    (hpos : ∀ T ∈ F, classMeasure Q μ L f T univ ≠ 0)
    (B : List ℕ → Set (Space d × Space d)) (hB : ∀ T ∈ F, MeasurableSet (B T))
    {ε : ℝ≥0∞} (hsmall : ∀ T ∈ F, ((normalizedClass Q μ L f T).prod ν) (B T) ≤ ε) :
    (μ.prod ν) (⋃ T ∈ F, (leafUnion Q (classLeaves L f T) ×ˢ univ) ∩ B T) ≤ ε := by
  apply (measure_biUnion_finset_le F _).trans
  calc
    _ ≤ ∑ T ∈ F, classMeasure Q μ L f T univ*ε := Finset.sum_le_sum
      (fun T hT => class_original_pair_bad_mass Q μ ν L f T (hpos T hT) (B T) (hB T hT) (hsmall T hT))
    _ = (∑ T ∈ F, classMeasure Q μ L f T univ)*ε := (Finset.sum_mul ..).symm
    _ ≤ 1*ε := mul_le_mul' (retained_class_mass_sum_le_one Q hQ μ hL f F hF) le_rfl
    _ = ε := one_mul ε

end Falconer.Regularization

end OAI
