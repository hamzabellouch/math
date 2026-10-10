import OAI.MeasureTheory.Falconer.Estimates.ClassRecombination
import OAI.MeasureTheory.Falconer.Shells.EndpointWeightedDistance

namespace OAI

/-! # Exact distance-law weights of restrictions to original classes -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem endpointWeightedDistance_smul (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν]
    (a b : ℝ≥0∞) (M P s : ℝ) (B C : Space d → Space d → ℝ) :
    endpointWeightedDistance (a • μ) (b • ν) M P s B C =
      (a*b) • endpointWeightedDistance μ ν M P s B C := by
  unfold endpointWeightedDistance
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
    withDensity_smul_measure,Measure.map_smul _ (by fun_prop)]

namespace Regularization

theorem normalizedClass_finite (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (L : Finset (CellPath d)) (f : CellPath d → List ℕ) (T : List ℕ) :
    IsFiniteMeasure (normalizedClass Q μ L f T) := by
  by_cases hT : classMeasure Q μ L f T univ = 0
  · have hz : classMeasure Q μ L f T = 0 := Measure.measure_univ_eq_zero.mp hT
    simp only [normalizedClass,hz,smul_zero]
    infer_instance
  · let : IsProbabilityMeasure (normalizedClass Q μ L f T) := normalizedClass_probability Q μ L f T hT
    infer_instance

theorem sourceClass_finite (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (N B : ℕ) (p : CellPath d) : IsFiniteMeasure (sourceClass Q μ N B p) :=
  normalizedClass_finite Q μ _ _ _

theorem restrict_class_eq_mass_smul (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (T : List ℕ) (hT : classMeasure Q μ L f T univ ≠ 0)
    (A : Set (Space d)) (hA : MeasurableSet A) :
    μ.restrict (A ∩ leafUnion Q (classLeaves L f T)) =
      classMeasure Q μ L f T univ • (normalizedClass Q μ L f T).restrict A := by
  rw [← Measure.restrict_restrict hA]
  change (classMeasure Q μ L f T).restrict A = _
  conv_lhs => rw [classMeasure_eq_mass_smul Q μ L f T hT,Measure.restrict_smul]

theorem original_class_endpoint_distance
    (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (L₁ L₂ : Finset (CellPath d)) (f₁ f₂ : CellPath d → List ℕ) (T U : List ℕ)
    (hT : classMeasure Q₁ μ L₁ f₁ T univ ≠ 0)
    (hU : classMeasure Q₂ ν L₂ f₂ U univ ≠ 0)
    (A D : Set (Space d)) (hA : MeasurableSet A) (hD : MeasurableSet D)
    (B C : Space d → Space d → ℝ) :
    endpointWeightedDistance
      (μ.restrict (A ∩ leafUnion Q₁ (classLeaves L₁ f₁ T)))
      (ν.restrict (D ∩ leafUnion Q₂ (classLeaves L₂ f₂ U))) 1 1 1 B C =
      (classMeasure Q₁ μ L₁ f₁ T univ * classMeasure Q₂ ν L₂ f₂ U univ) •
        endpointWeightedDistance ((normalizedClass Q₁ μ L₁ f₁ T).restrict A)
          ((normalizedClass Q₂ ν L₂ f₂ U).restrict D) 1 1 1 B C := by
  let : IsProbabilityMeasure (normalizedClass Q₁ μ L₁ f₁ T) :=
    normalizedClass_probability Q₁ μ L₁ f₁ T hT
  let : IsProbabilityMeasure (normalizedClass Q₂ ν L₂ f₂ U) :=
    normalizedClass_probability Q₂ ν L₂ f₂ U hU
  rw [restrict_class_eq_mass_smul Q₁ μ L₁ f₁ T hT A hA,
    restrict_class_eq_mass_smul Q₂ ν L₂ f₂ U hU D hD,
    endpointWeightedDistance_smul]

end Regularization
end Falconer

end OAI
