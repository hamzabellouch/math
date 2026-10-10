import OAI.Geometry.NodalSets.Elliptic.RealGlobalL2Multiplier
import OAI.Geometry.NodalSets.Elliptic.RealTransportDerivatives

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_compact_gradient_multiplier_bound {n : ℕ} (theta : Coord n → ℝ)
    (ht : ContDiff ℝ ∞ theta) (hc : HasCompactSupport theta) :
    ∃ B > 0, ∀ (u : Coord n → ℝ), MemLp u 2 volume →
      (∀ j : Fin n, MemLp (fun x ↦ coordPartial theta x j*u x) 2 volume) ∧
      (∑ j : Fin n, ∫ x, (coordPartial theta x j*u x)^2) ≤ B*(∫ x, (u x)^2) := by
  let L (j : Fin n) : RealEuclideanL2 n →L[ℝ] RealEuclideanL2 n :=
    realGlobalCompactMap hc (fun x ↦ coordPartial theta x j)
      (real_coordPartial_smooth theta ht j).continuous (tsupport_fderiv_apply_subset ℝ (Pi.single j 1))
  let B : ℝ := 1+∑ j : Fin n, ‖L j‖^2
  refine ⟨B,by dsimp [B]; positivity,fun u hu ↦ ?_⟩
  have hrep (j : Fin n) : (L j (hu.toLp u) : Coord n → ℝ) =ᵐ[volume]
      fun x ↦ coordPartial theta x j*u x :=
    realGlobalCompactMap_ae hc _ (real_coordPartial_smooth theta ht j).continuous
      (tsupport_fderiv_apply_subset ℝ (Pi.single j 1)) _ _ hu.coeFn_toLp
  have hj (j : Fin n) : (∫ x, (coordPartial theta x j*u x)^2) ≤ ‖L j‖^2*(∫ x, (u x)^2) := by
    rw [← real_L2_norm_sq_rep _ _ (hrep j),← real_toLp_norm_sq u hu]
    have hn := (L j).le_opNorm (hu.toLp u)
    nlinarith [norm_nonneg (L j (hu.toLp u)),mul_nonneg (norm_nonneg (L j)) (norm_nonneg (hu.toLp u))]
  refine ⟨fun j ↦ (memLp_congr_ae (hrep j)).mp (Lp.memLp _),?_⟩
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hj j)
  rw [← Finset.sum_mul] at hs
  have hi : 0 ≤ ∫ x, (u x)^2 := integral_nonneg (fun _ ↦ sq_nonneg _)
  dsimp only [B]
  nlinarith

end
end Yau

end OAI
