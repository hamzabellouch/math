import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingFiniteExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingSourceExpression
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicForceEvaluation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularForce
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StartupEffective

namespace OAI

/-! Evaluation of the prescribed whole-plane force from finite names. Only
a finite initial segment of the complete guarded graph is inspected. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set Filter
open scoped ContDiff Topology

theorem prefixCode_germ (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ D K : ℚ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (N : ℕ) (y : SpaceTime) (hN : y.1 + 2 ≤ (N : ℝ)) :
    triangularVelocity (expandingDrift M hM blank m σ D K) (fun _ _ => 0) =ᶠ[𝓝 y]
      (prefixCode M hM blank m σ D K N).val := by
  have hs : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hk : (0 : ℝ) ≤ K := by exact_mod_cast hK
  have htime : ∀ᶠ z : SpaceTime in 𝓝 y, z.1 < y.1 + 1 :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds (by simp)
  filter_upwards [htime] with z hz
  rw [prefixCode_val]
  have he := expandingDrift_eq_prefix M hM blank m hs hd hk (y.1+1) N
    (by linarith) hz.le
  simp only [triangularVelocity, triangularLift, zero_smul, add_zero, he]

def expandingPrefixLength (q : ℚ) : ℕ := ⌈q + 3⌉₊

theorem expandingPrefixLength_bound {t : ℝ} (q : ℚ) (hq : |t - (q : ℝ)| ≤ 1) :
    t + 2 ≤ (expandingPrefixLength q : ℝ) := by
  have hc : (q : ℝ) + 3 ≤ (expandingPrefixLength q : ℝ) := by
    exact_mod_cast (Nat.le_ceil (q + 3))
  linarith [(abs_le.mp hq).2]

def evaluateExpandingForce (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ) (σ D K : ℚ)
    (p : Fin 2 → ℚ) (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  let c := prefixCode M hM blank m σ D K (expandingPrefixLength (b 0).1)
  NonperiodicResidual.evaluate c α a b (ε/2) (by positivity) +
    (verticalSourceCode p).evaluate α b (ε/2) (by positivity)

theorem evaluateExpandingForce_spec (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ D K : ℚ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (p : Fin 2 → ℚ) (α : List (Fin 4)) {ν : ℝ} {a : ℕ → ℚ}
    (ha : IsFastRealName a ν) {y : SpaceTime} {b : ℕ → RationalSpaceTime}
    (hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (triangularForce ν (expandingDrift M hM blank m σ D K)
        (unitImpulse (fun j => (p j : ℝ)))) α y -
      rationalVector (evaluateExpandingForce M hM blank m σ D K p α a b ε hε)‖ ≤
      (ε : ℝ) := by
  let c := prefixCode M hM blank m σ D K (expandingPrefixLength (b 0).1)
  have ht : |y.1 - ((b 0).1 : ℝ)| ≤ 1 := by
    have h := (norm_fst_le (y - rationalPoint (b 0))).trans (hb 0)
    simpa only [Prod.fst_sub, rationalPoint, Real.norm_eq_abs,
      errorTolerance, pow_zero, inv_one] using h
  have hg := prefixCode_germ M hM blank m hσ hD hK _ y
    (expandingPrefixLength_bound _ ht)
  have hs : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hk : (0 : ℝ) ≤ K := by exact_mod_cast hK
  have hsource : (verticalSourceCode p).val =
      triangularVelocity (fun _ _ => 0) (unitImpulse (fun j => (p j : ℝ))) := by
    funext z
    rw [verticalSourceCode_val]
    simp only [triangularVelocity, triangularLift, map_zero, zero_add]
  rw [triangularForce_eq_residual (expandingDrift_smooth M hM blank m hs hd hk),
    ← hsource, mixedDerivative_add
      (residual_smooth (triangularVelocity_smooth
        (expandingDrift_smooth M hM blank m hs hd hk) contDiff_const) ν)
      (verticalSourceCode p).smooth]
  have he := (mixedDerivative_eventuallyEq (residual_eventuallyEq hg ν) α).self_of_nhds
  change ‖mixedDerivative (residual ν (triangularVelocity
      (expandingDrift M hM blank m σ D K) (fun _ _ => 0))) α y +
      mixedDerivative (verticalSourceCode p).val α y -
      rationalVector (evaluateExpandingForce M hM blank m σ D K p α a b ε hε)‖ ≤ (ε : ℝ)
  rw [he]
  let q := NonperiodicResidual.evaluate c α a b (ε/2) (by positivity)
  let r := (verticalSourceCode p).evaluate α b (ε/2) (by positivity)
  have hq := NonperiodicResidual.evaluate_spec c α ha hb (ε/2) (by positivity)
  have hr := (verticalSourceCode p).evaluate_spec α b hb (ε/2) (by positivity)
  have hcast : rationalVector (q + r) = rationalVector q + rationalVector r := by
    ext j
    simp [rationalVector]
  change ‖mixedDerivative (residual ν c.val) α y +
    mixedDerivative (verticalSourceCode p).val α y - rationalVector (q+r)‖ ≤ _
  rw [hcast]
  calc
    _ = ‖(mixedDerivative (residual ν c.val) α y - rationalVector q) +
        (mixedDerivative (verticalSourceCode p).val α y - rationalVector r)‖ := by
      congr 1
      abel
    _ ≤ ‖mixedDerivative (residual ν c.val) α y - rationalVector q‖ +
        ‖mixedDerivative (verticalSourceCode p).val α y - rationalVector r‖ := norm_add_le _ _
    _ ≤ (ε : ℝ)/2 + (ε : ℝ)/2 := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using add_le_add hq hr
    _ = (ε : ℝ) := by ring

end ForcedComputation.ExpandingDetector

end

end OAI
