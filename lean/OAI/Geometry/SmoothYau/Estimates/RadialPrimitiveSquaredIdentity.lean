import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ProfilePeriodizeEventuallyZero

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
namespace YauCounterexamples

lemma radialPrimitive_squared_identity {β : ℝ → ℝ} (hβ : Continuous β) (s : ℝ) :
    radialPrimitive β (s^2) = ∫ t in (0:ℝ)..s, 2*t*β (t^2) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun z => radialPrimitive β (z^2)) (2*t*β (t^2)) t := by
    intro t
    convert (radialPrimitive_hasDeriv β hβ (t^2)).comp t ((hasDerivAt_id t).pow 2) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hi : IntervalIntegrable (fun t : ℝ => 2*t*β (t^2)) volume 0 s :=
    ((continuous_const.mul continuous_id).mul (hβ.comp (continuous_id.pow 2))).intervalIntegrable 0 s
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa [radialPrimitive] using hh.symm

lemma radialSquaredBase_true_radius {β : ℝ → ℝ} (hβ : Continuous β) (b : ℝ)
    (x : ProfilePlane) :
    radialPrimitive β b + radialSquaredBase β b x =
      ∫ t in (0:ℝ)..Real.sqrt (x.1^2+x.2^2), 2*t*β (t^2) := by
  rw [← radialPrimitive_squared_identity hβ]
  rw [Real.sq_sqrt (by positivity)]
  simp [radialSquaredBase]

end YauCounterexamples

end

end OAI
