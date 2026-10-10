import OAI.MeasureTheory.Falconer.Measures.StartingMeasures
import OAI.MeasureTheory.Falconer.Slicing.SliceNormalization

namespace OAI

/-! # Positive original restrictions preserve all projected Frostman bounds -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

noncomputable def positiveRestriction (μ : ProbabilityMeasure (Space d))
    (A : Set (Space d)) (hA : 0 < (μ : Measure (Space d)) A) : ProbabilityMeasure (Space d) :=
  normalizedSliceLaw ((μ : Measure (Space d)).restrict A) (by simpa using hA.ne')

theorem positiveRestriction_eq (μ : ProbabilityMeasure (Space d))
    (A : Set (Space d)) (hA : 0 < (μ : Measure (Space d)) A) :
    (positiveRestriction μ A hA : Measure (Space d)) =
      ENNReal.ofReal (((μ : Measure (Space d)) A).toReal⁻¹) • (μ : Measure (Space d)).restrict A := by
  rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hA.ne' (measure_ne_top _ _)),
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp only [positiveRestriction,normalizedSliceLaw,Measure.restrict_apply_univ]
  rfl

theorem positiveRestriction_support (μ : ProbabilityMeasure (Space d))
    (A : Set (Space d)) (hA : 0 < (μ : Measure (Space d)) A) (hclosed : IsClosed A) :
    (positiveRestriction μ A hA : Measure (Space d)).support ⊆ A := by
  apply Measure.support_subset_of_isClosed hclosed
  change (positiveRestriction μ A hA : Measure (Space d)) Aᶜ = 0
  rw [positiveRestriction_eq,Measure.smul_apply,Measure.restrict_apply hclosed.measurableSet.compl,
    compl_inter_self,measure_empty,smul_zero]

theorem positiveRestriction_absolutelyContinuous (μ : ProbabilityMeasure (Space d))
    (A : Set (Space d)) (hA : 0 < (μ : Measure (Space d)) A) :
    (positiveRestriction μ A hA : Measure (Space d)) ≪ (μ : Measure (Space d)) := by
  rw [positiveRestriction_eq]
  exact Measure.smul_absolutelyContinuous.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem positiveRestriction_projected_frostman (μ : ProbabilityMeasure (Space d))
    (A : Set (Space d)) (hA : 0 < (μ : Measure (Space d)) A)
    (P : Space d →L[ℝ] Space m) {s C : ℝ}
    (hfrost : FrostmanBallBound ((μ : Measure (Space d)).map P) s C) :
    FrostmanBallBound ((positiveRestriction μ A hA : Measure (Space d)).map P) s
      (((μ : Measure (Space d)) A).toReal⁻¹*C) := by
  intro x r hr
  rw [positiveRestriction_eq,Measure.map_smul _ P.continuous.measurable.aemeasurable,
    Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ENNReal.ofReal (((μ : Measure (Space d)) A).toReal⁻¹) * ENNReal.ofReal (C*r^s) :=
      mul_le_mul_right ((Measure.map_mono Measure.restrict_le_self P.continuous.measurable _).trans
        (hfrost x r hr)) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end Falconer

end OAI
