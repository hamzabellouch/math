import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSliceProjection

namespace OAI

/-! The planar frame estimate on arbitrary full L2 slices. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem split_planar_frame_bound {D : ℝ} {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ z, ∑ i, (planarCoefficient (u i) f z)^2) ≤
      (1+m*localizedOverlapBound D)*(∫ p, f p^2) := by
  have hp : MemLp f 2 ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using hf
  have hi : Integrable (fun z : ℝ => ∑ i, (planarCoefficient (u i) f z)^2) :=
    integrable_finsetSum _ (fun i _ => (planarCoefficient_contraction (u i) f hf).1.integrable_sq)
  have hraw := hp.integrable_sq.integral_prod_right
  have hbound : ∀ᵐ z : ℝ, (∑ i, (planarCoefficient (u i) f z)^2) ≤
      (1+m*localizedOverlapBound D)*(∫ r : PlanarPosition, f (r,z)^2) := by
    filter_upwards [split_memLp_planar_slices f hf] with z hz
    exact planar_modes_frame_bound u hsep (fun r => f (r,z)) hz
  have h := integral_mono_ae hi (hraw.const_mul (1+m*localizedOverlapBound D)) hbound
  rw [integral_const_mul,← integral_prod_symm _ hp.integrable_sq] at h
  simpa only [Measure.volume_eq_prod] using h

end ContinuumCoulomb

end

end OAI
