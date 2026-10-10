import OAI.Geometry.CylinderCovering.Rational.DictionaryStatementDefinitions
import OAI.Geometry.CylinderCovering.Rational.CostDictionary
import OAI.Geometry.CylinderCovering.Rational.Realization

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RationalDictionary

theorem centeredTetrahedron_eq_reference :
    RationalSimilarity.centeredTetrahedron = SlopeRational.referenceTetrahedron := by
  ext z
  constructor
  · rintro ⟨t, hz, ht₁, ht₂, hx, hy⟩
    exact ⟨t, ht₁, ht₂, hx, hy, hz⟩
  · rintro ⟨t, ht₁, ht₂, hx, hy, hz⟩
    exact ⟨t, hz, ht₁, ht₂, hx, hy⟩

theorem centeredFirstSweep_eq_lowerSweep (d eps q : ℝ) :
    centeredFirstSweep d eps q = SlopeRational.lowerSweep d eps q := by
  ext z
  rw [SlopeRational.lowerSweep_mem_iff]
  rfl

theorem centeredSecondSweep_eq_upperSweep (d eps q : ℝ) :
    centeredSecondSweep d eps q = SlopeRational.upperSweep d eps q := by
  ext z
  rw [SlopeRational.upperSweep_mem_iff]
  rfl

theorem centeredWeight_eq_physicalWeight (d eps : ℝ) (p : Plane) :
    centeredWeight d eps p = SlopeRational.physicalScale *
      RuledApproximation.physicalWeight SlopeRational.physicalScale
        (eps • SlopeRational.field d p) := by
  unfold centeredWeight RuledApproximation.physicalWeight SlopeRational.field
  simp only [PiLp.smul_apply, smul_eq_mul]
  change c0 / Real.sqrt (1 + eps ^ 2 *
      (SlopeRational.a d (p 0) (p 1) ^ 2 + c0 ^ 2 * SlopeRational.b d (p 0) (p 1) ^ 2)) =
    c0 * (1 / Real.sqrt (1 + (eps * SlopeRational.a d (p 0) (p 1)) ^ 2 +
      c0 ^ 2 * (eps * SlopeRational.b d (p 0) (p 1)) ^ 2))
  rw [mul_one_div]
  congr 2
  ring

theorem centeredCost_eq_weightedCost (d eps q : ℝ) :
    centeredCost d eps q = SlopeRational.weightedCost d eps q := by
  unfold centeredCost SlopeRational.weightedCost
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (centeredWeight_eq_physicalWeight d eps)

theorem actual_coordinate_identity {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) :
    RationalSimilarity.phi '' RationalSimilarity.uncenteredTetrahedron =
      SlopeRational.referenceTetrahedron ∧
    RationalSimilarity.phi '' uncenteredFirstSweep d0 eta0 k =
      SlopeRational.lowerSweep (centeredRegularization d0) (centeredTilt d0 k)
        (centeredPadding eta0 k) ∧
    RationalSimilarity.phi '' uncenteredSecondSweep d0 eta0 k =
      SlopeRational.upperSweep (centeredRegularization d0) (centeredTilt d0 k)
        (centeredPadding eta0 k) ∧
    SlopeRational.weightedCost (centeredRegularization d0) (centeredTilt d0 k)
      (centeredPadding eta0 k) = uncenteredCost d0 eta0 k / 8 ∧
    centeredPadding eta0 k = centeredMargin d0 eta0 * centeredTilt d0 k ^ 2 ∧
    ∀ S : Set Space,
      (Measure.euclideanHausdorffMeasure 2 (RationalSimilarity.phi '' S)).toReal =
        (1 / 8 : ℝ) * (Measure.euclideanHausdorffMeasure 2 S).toReal := by
  refine ⟨?_, ?_, ?_, ?_,
    centeredPadding_eq_margin_mul_tilt_sq (by linarith) eta0 k,
    RationalSimilarity.phi_area⟩
  · rw [RationalSimilarity.phi_image_tetrahedron, centeredTetrahedron_eq_reference]
  · rw [phi_image_firstSweep hd eta0 k, centeredFirstSweep_eq_lowerSweep]
  · rw [phi_image_secondSweep hd eta0 k, centeredSecondSweep_eq_upperSweep]
  · rw [← centeredCost_eq_weightedCost]
    exact cost_dictionary hd eta0 k

theorem coordinate_cost_dictionary : CoordinateCostStatement := by
  intro d0 hd eta0 k
  exact actual_coordinate_identity hd eta0 k

end RationalDictionary

end

end OAI
