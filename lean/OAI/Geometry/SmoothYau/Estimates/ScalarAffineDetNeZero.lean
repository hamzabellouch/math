import Mathlib
import OAI.Geometry.SmoothYau.DifferentialEq.LocalDiffeomorphismDetNeZero
import OAI.Geometry.SmoothYau.Smoothness.CutoffPullbackLinear

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma scalarAffine_det_ne_zero (p : E) {r : ℝ} (hr : r ≠ 0) (x : E) :
    (fderiv ℝ (fun y : E => p + r • y) x).det ≠ 0 := by
  have hd : HasFDerivAt (fun y : E => p + r • y) (r • ContinuousLinearMap.id ℝ E) x := by
    simpa only [Pi.smul_apply, id_eq] using ((hasFDerivAt_id x).const_smul r).const_add p
  rw [hd.fderiv]
  change LinearMap.det (r • (LinearMap.id : E →ₗ[ℝ] E)) ≠ 0
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  exact pow_ne_zero _ hr

def sobolevAffineCutoff (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (p : E) (r : ℝ) (k : ℕ) :
    FourierSobolevSpace E ℂ (2 * (k : ℝ)) →L[ℂ]
      FourierSobolevSpace E ℂ (2 * (k : ℝ)) :=
  sobolevCutoffPullback η hηc hη (fun y => p + r • y) (by fun_prop) k

lemma sobolevAffineCutoff_representative (η : E → ℂ) (hηc : HasCompactSupport η)
    (hη : ContDiff ℝ ∞ η) (p : E) {r : ℝ} (hr : r ≠ 0)
    (k : ℕ) (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (u : FourierSobolevSpace E ℂ (2 * (k : ℝ))) (x : E) :
    sobolevRepresentative hs (sobolevAffineCutoff η hηc hη p r k u) x =
      η x * sobolevRepresentative hs u (p + r • x) := by
  obtain ⟨J, hJ⟩ := compact_jacobian_bound hηc (show ContDiff ℝ ∞ (fun y : E => p + r • y) by fun_prop)
    (fun y _ => scalarAffine_det_ne_zero p hr y)
  apply sobolevRepresentative_cutoffPullback η hηc hη _ _ _ J hJ k hs u x
  intro y _ z _ he
  exact (smul_right_injective E hr) (add_left_cancel he)

end YauCounterexamples


end

end OAI
