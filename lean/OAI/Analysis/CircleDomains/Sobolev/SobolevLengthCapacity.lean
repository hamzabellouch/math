import OAI.Analysis.CircleDomains.Sobolev.SobolevCapacityCover
import OAI.Analysis.CircleDomains.Sobolev.SquareAverageL2

namespace OAI

/-! The local planar capacity estimate needed for the Sobolev graph proof.
Its constant is fixed; all energy is the actual distributional energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_unit_length_capacity {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (huL2 : MemLp (fun p => u (euclideanPlaneCoordinates.symm p)) 2 volume)
    {A : Set (ℝ × ℝ)} (hA : A ⊆ closedBall 0 1)
    (hone : ∀ c ∈ A, 1 ≤ u (euclideanPlaneCoordinates.symm c)) :
    lengthContent A ≤ 131072 *
      (ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
        coordinateSobolevEnergy V univ) := by
  by_cases hs : (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) ≤ 1
  · exact (locally_sobolev_lengthContent_le hu hw hLp hone
      (fun c _ => abs_unitSquareAverage_le_half huL2 hs c)).trans
        (mul_le_mul' le_rfl (le_add_of_nonneg_left (by positivity)))
  · have hb : lengthContent A ≤ 2 := by
      apply (measure_mono hA).trans
      simpa using lengthContent_closedBall_le (0 : ℝ × ℝ) 1
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) := by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (le_of_not_ge hs))
    have h2 : (2 : ℝ≥0∞) ≤ 131072 *
        (ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
          coordinateSobolevEnergy V univ) := by
      calc
        2 ≤ (131072 : ℝ≥0∞) := by norm_num
        _ = 131072*1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul' le_rfl (h1.trans (le_add_of_nonneg_right (by positivity)))
    exact hb.trans h2

end CircleDomainRigidity

end

end OAI
