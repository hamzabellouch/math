import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorPrefixExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularForce

namespace OAI

/-! The evaluator selects a finite clocked program from the zeroth time
approximation. Locality of the residual certifies every mixed derivative. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter
open scoped ContDiff Topology

theorem triangularVelocity_congr_germ {a b : ℝ → Plane → Plane}
    {g h : ℝ → Plane → ℝ} {y : SpaceTime}
    (ha : Function.uncurry a =ᶠ[𝓝 (y.1, horizontalLinear y.2)] Function.uncurry b)
    (hg : Function.uncurry g =ᶠ[𝓝 (y.1, horizontalLinear y.2)] Function.uncurry h) :
    triangularVelocity a g =ᶠ[𝓝 y] triangularVelocity b h := by
  have hc : Continuous (fun z : SpaceTime => (z.1, horizontalLinear z.2)) :=
    continuous_fst.prodMk (horizontalLinear.continuous.comp continuous_snd)
  have ha' := ha.comp_tendsto hc.continuousAt
  have hg' := hg.comp_tendsto hc.continuousAt
  filter_upwards [ha', hg'] with z hz₁ hz₂
  change a z.1 (horizontalLinear z.2) = b z.1 (horizontalLinear z.2) at hz₁
  change g z.1 (horizontalLinear z.2) = h z.1 (horizontalLinear z.2) at hz₂
  simp only [triangularVelocity, triangularLift, hz₁, hz₂]

theorem detectorForce_prefix_germ {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H)
    (hV : ContDiff ℝ ∞ (Function.uncurry (planarSlice H)))
    (C L N : ℕ) (y : SpaceTime) (hN : y.1 + 1 ≤ (N : ℝ)) :
    detectorForce (planarSlice H) C L =ᶠ[𝓝 y] (forcePrefixExpression H C L N).val := by
  have ha := detectorDrift_prefix_germ (planarSlice H) C L N
    (y.1, horizontalLinear y.2) hN
  have hh := detectorSource_prefix_germ C L N (y.1, horizontalLinear y.2) hN
  have hzero : Function.uncurry (fun _ : ℝ => fun _ : Plane => (0 : ℝ)) =ᶠ[
      𝓝 (y.1, horizontalLinear y.2)] Function.uncurry (fun _ : ℝ => fun _ : Plane => (0 : ℝ)) :=
    Filter.EventuallyEq.rfl
  have hazero : Function.uncurry (fun _ : ℝ => fun _ : Plane => (0 : Plane)) =ᶠ[
      𝓝 (y.1, horizontalLinear y.2)] Function.uncurry (fun _ : ℝ => fun _ : Plane => (0 : Plane)) :=
    Filter.EventuallyEq.rfl
  rw [forcePrefixExpression_value hH hT, detectorForce,
    triangularForce_eq_residual (detectorDrift_smooth hV C L)]
  exact (residual_eventuallyEq (triangularVelocity_congr_germ ha hzero) 1).add
    (triangularVelocity_congr_germ hazero hh)

def forcePrefixLength (q : ℚ) : ℕ := ⌈q + 2⌉₊

theorem forcePrefixLength_bound {t : ℝ} (q : ℚ) (hq : |t - (q : ℝ)| ≤ 1) :
    t + 1 ≤ (forcePrefixLength q : ℝ) := by
  have hc : (q : ℝ) + 2 ≤ (forcePrefixLength q : ℝ) := by
    exact_mod_cast (Nat.le_ceil (q + 2))
  linarith [(abs_le.mp hq).2]

def evaluateDetectorForce (H : FieldExpr) (hH : H.Valid) (C L : ℕ)
    (α : List (Fin 4)) (a : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  let N := forcePrefixLength (a 0).1
  (forcePrefixExpression H C L N).evaluate (forcePrefixExpression_valid hH C L N)
    α a ε hε

theorem evaluateDetectorForce_spec {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H)
    (hV : ContDiff ℝ ∞ (Function.uncurry (planarSlice H)))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → RationalSpaceTime)
    {y : SpaceTime} (ha : IsFastName a y) (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (detectorForce (planarSlice H) C L) α y -
      rationalVector (evaluateDetectorForce H hH C L α a ε hε)‖ ≤ (ε : ℝ) := by
  have ht : |y.1 - ((a 0).1 : ℝ)| ≤ 1 := by
    have h := (norm_fst_le (y - rationalPoint (a 0))).trans (ha 0)
    simpa only [Prod.fst_sub, rationalPoint, Real.norm_eq_abs,
      errorTolerance, pow_zero, inv_one] using h
  have hg := detectorForce_prefix_germ hH hT hV C L (forcePrefixLength (a 0).1) y
    (forcePrefixLength_bound _ ht)
  rw [(mixedDerivative_eventuallyEq hg α).self_of_nhds]
  exact ClockedVector.evaluate_spec (forcePrefixExpression_valid hH C L _) α a ha ε hε

def detectorForceBound (H : FieldExpr) (C L : ℕ) (α : List (Fin 4)) (T : ℚ) : ℚ :=
  (forcePrefixExpression H C L (forcePrefixLength T)).bound α (|T| + 2)

theorem detectorForceBound_nonneg (H : FieldExpr) (C L : ℕ)
    (α : List (Fin 4)) (T : ℚ) : 0 ≤ detectorForceBound H C L α T :=
  ClockedVector.bound_nonneg _ _ _

theorem detectorForceBound_spec {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H)
    (hV : ContDiff ℝ ∞ (Function.uncurry (planarSlice H)))
    (C L : ℕ) (α : List (Fin 4)) (T : ℚ) {y : SpaceTime}
    (ht : 0 ≤ y.1) (hT' : y.1 ≤ (T : ℝ)) :
    ‖mixedDerivative (detectorForce (planarSlice H) C L) α y‖ ≤
      (detectorForceBound H C L α T : ℝ) := by
  have hc : (T : ℝ) + 2 ≤ (forcePrefixLength T : ℝ) := by
    exact_mod_cast (Nat.le_ceil (T + 2))
  have hN : y.1 + 1 ≤ (forcePrefixLength T : ℝ) := by linarith
  have hg := detectorForce_prefix_germ hH hT hV C L (forcePrefixLength T) y hN
  rw [(mixedDerivative_eventuallyEq hg α).self_of_nhds]
  apply ClockedVector.val_bound (forcePrefixExpression_valid hH C L _) α (|T| + 2)
  rw [abs_of_nonneg ht, Rat.cast_add, Rat.cast_abs, Rat.cast_ofNat,
    abs_of_nonneg (by positivity)]
  exact hT'.trans ((le_abs_self (T : ℝ)).trans (by linarith))

end ForcedComputation.VelocityDetector

end

end OAI
