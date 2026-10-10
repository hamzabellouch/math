import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCompactL2

namespace OAI

/-! A smooth drift with common compact spatial support has the required
strong time regularity on every finite interval. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set Filter
open scoped Topology ContDiff

def planeTemporalDerivative (F : ℝ → Plane → ℝ) (t : ℝ) (x : Plane) : ℝ :=
  fderiv ℝ (Function.uncurry F) (t, x) (1, 0)

theorem planeTemporalDerivative_smooth {F : ℝ → Plane → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (Function.uncurry (planeTemporalDerivative F)) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem planeTemporalDerivative_hasDerivAt {F : ℝ → Plane → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (t : ℝ) (x : Plane) :
    HasDerivAt (fun r => F r x) (planeTemporalDerivative F t x) t := by
  have hh := (hF.differentiable (by simp) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact hh

theorem planeTemporalDerivative_zero {F : ℝ → Plane → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) {K : Set Plane}
    (hz : ∀ t x, x ∉ K → F t x = 0) (t : ℝ) {x : Plane} (hx : x ∉ K) :
    planeTemporalDerivative F t x = 0 := by
  have he : (fun r => F r x) = fun _ => (0 : ℝ) := funext (fun r => hz r x hx)
  have hd := planeTemporalDerivative_hasDerivAt hF t x
  rw [he] at hd
  exact (hasDerivAt_const t (0 : ℝ)).unique hd |>.symm

theorem compact_family_c1L2 {F : ℝ → Plane → ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) {K : Set Plane} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F t x = 0) (T : ℝ) :
    PlaneC1L2 F (planeTemporalDerivative F) (Icc 0 T) := by
  let G := planeTemporalDerivative F
  have hG : Continuous (Function.uncurry G) := (planeTemporalDerivative_smooth hF).continuous
  have hzG : ∀ t x, x ∉ K → G t x = 0 := fun t _ hx => planeTemporalDerivative_zero hF hz t hx
  obtain ⟨bF, hiF, hbF⟩ := compact_family_square_envelope hF.continuous hK hz T
  obtain ⟨bG, hiG, hbG⟩ := compact_family_square_envelope hG hK hzG T
  have hcF : SquareDistanceContinuousOn F (Icc 0 T) :=
    squareDistanceContinuousOn_of_envelope
      (fun t _ => hF.continuous.comp (continuous_const.prodMk continuous_id))
      (fun x => (hF.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn) hiF hbF
  have hcG : SquareDistanceContinuousOn G (Icc 0 T) :=
    squareDistanceContinuousOn_of_envelope
      (fun t _ => hG.comp (continuous_const.prodMk continuous_id))
      (fun x => (hG.comp (continuous_id.prodMk continuous_const)).continuousOn) hiG hbG
  have hd : PlaneStrongDerivativeOn F G (Icc 0 T) :=
    strongDerivativeOn_of_envelope (convex_Icc 0 T)
      (fun t _ => hF.continuous.comp (continuous_const.prodMk continuous_id))
      (fun t _ => hG.comp (continuous_const.prodMk continuous_id))
      (fun t _ x => (planeTemporalDerivative_hasDerivAt hF t x).hasDerivWithinAt) hiG hbG
  exact planeC1L2_of_square_estimates
    (fun t _ => compact_family_memLp hF.continuous hK hz t)
    (fun t _ => compact_family_memLp hG hK hzG t) hcF hcG hd

end ForcedComputation.VelocityDetector

end

end OAI
