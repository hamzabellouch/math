import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.IsometricRieszPairing
import OAI.Analysis.RieszRectifiability.Foundations.CappedTransform
import OAI.Analysis.RieszRectifiability.Kernel.FarRieszTransform

namespace OAI

/-!
# Local Riesz transforms under linear isometries

Linear isometries commute with restriction to localization balls and preserve the
scalar capped kernels and far transforms. These identities transfer local transform
calculations between intrinsic plane coordinates and the ambient Euclidean space.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem linearIsometry_restrict_ball {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n)) (a : Ambient n) (R : ℝ) :
    (μ.map L).restrict (ball (L a) R) = (μ.restrict (ball a R)).map L := by
  have hpre : L ⁻¹' ball (L a) R = ball a R := by
    ext x
    simp only [mem_preimage, mem_ball, L.dist_map]
  rw [Measure.restrict_map L.continuous.measurable measurableSet_ball, hpre]

theorem scalarCappedRieszKernel_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (e : Ambient n) (ε : ℝ) (x y : Ambient n) :
    scalarCappedRieszKernel m (L e) ε (L x, L y) = scalarCappedRieszKernel m e ε (x, y) := by
  have heq : cappedRieszKernel m ε (L x, L y) = L (cappedRieszKernel m ε (x, y)) := by
    simp only [cappedRieszKernel, cappedInverseDistancePow, L.dist_map, map_smul, map_sub]
  rw [scalarCappedRieszKernel, heq, L.inner_map_map]
  rfl

theorem scalarCappedTransform_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (e : Ambient n) (ε : ℝ) (f : Ambient d → ℝ) (x : Ambient n) :
    scalarCappedTransform m (μ.map L) (L e) ε f (L x) =
      scalarCappedTransform m μ e ε (fun y => f (L y)) x := by
  unfold scalarCappedTransform
  rw [L.isometry.isClosedEmbedding.measurableEmbedding.integral_map]
  simp only [scalarCappedRieszKernel_linearIsometry]

theorem scalarCappedTransform_ball_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (e a : Ambient n) (R ε : ℝ) (x : Ambient n) :
    scalarCappedTransform m ((μ.map L).restrict (ball (L a) R)) (L e) ε (fun _ => 1) (L x) =
      scalarCappedTransform m (μ.restrict (ball a R)) e ε (fun _ => 1) x := by
  rw [linearIsometry_restrict_ball, scalarCappedTransform_linearIsometry]

theorem scalarFarRieszTransform_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (e a : Ambient n) (R : ℝ) (x : Ambient n) :
    scalarFarRieszTransform m (μ.map L) (L e) (L a) R (L x) =
      scalarFarRieszTransform m μ e a R x := by
  have hext : L ⁻¹' closedExterior (L a) R = closedExterior a R := by
    ext y
    simp only [mem_preimage, closedExterior, mem_ofPred_eq, L.dist_map]
  unfold scalarFarRieszTransform
  rw [Measure.restrict_map L.continuous.measurable (closedExterior_measurable (L a) R),
    hext, L.isometry.isClosedEmbedding.measurableEmbedding.integral_map]
  simp only [kernel_linearIsometry, ← map_sub, L.inner_map_map]

end

end RieszRectifiability

end OAI
