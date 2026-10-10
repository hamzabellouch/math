import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorProgram
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorViscosityProgram

namespace OAI

/-! The general input-oracle detector at a named positive viscosity.
The spatial force has two viscosity factors, while its scalar source has
one; each additional time derivative contributes one further factor. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CompactProgram
open ShearFlows
open scoped ContDiff

def unitForceName {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (b : ℕ → RationalSpaceTime) : ℕ → RationalVector :=
  fun n => evaluateUnitForce hV o C L α b (ClockedExpr.dyadic n) (ClockedExpr.dyadic_pos n)

theorem unitForceName_spec {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (hb : IsFastName b y) :
    IsFastVectorName (unitForceName hV o C L α b) (mixedDerivative (detectorForce V C L) α y) := by
  intro n
  simpa only [unitForceName, ClockedExpr.dyadic_cast] using
    evaluateUnitForce_spec hV o C L α b hb (ClockedExpr.dyadic n) (ClockedExpr.dyadic_pos n)

def viscosityBalls {V : ℝ → Plane → Plane} {ν : ℝ} {y : SpaceTime}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hb : IsFastName b y) (n : ℕ) (j : Fin 3) : QBall :=
  ((realNameBall a n).pow (α.count 0 + if j = 2 then 1 else 2)).mul
    (vectorNameBall (unitForceName hV o C L α (scaleTimeName a b ha hb)) n j)

theorem viscosityBalls_contains {V : ℝ → Plane → Plane} {ν : ℝ} {y : SpaceTime}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hb : IsFastName b y) (n : ℕ) (j : Fin 3) :
    (viscosityBalls hV o C L α a b ha hb n j).Contains
      (mixedDerivative (detectorViscosityForce V C L ν) α y j) := by
  rw [mixedDerivative_detectorViscosityForce V hV]
  exact QBall.contains_mul (QBall.contains_pow (realNameBall_contains ha n) _)
    (vectorNameBall_contains (unitForceName_spec hV o C L α
      (scaleTimeName_spec a b ha hb)) n j)

theorem viscosityBalls_converges {V : ℝ → Plane → Plane} {ν : ℝ} {y : SpaceTime}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hb : IsFastName b y) (j : Fin 3) :
    QBall.Converges (fun n => viscosityBalls hV o C L α a b ha hb n j)
      (mixedDerivative (detectorViscosityForce V C L ν) α y j) := by
  rw [mixedDerivative_detectorViscosityForce V hV]
  exact ((realNameBall_converges ha).pow _).mul
    (vectorNameBall_converges (unitForceName_spec hV o C L α
      (scaleTimeName_spec a b ha hb)) j)

def evaluateViscosityForce {V : ℝ → Plane → Plane} {ν : ℝ} {y : SpaceTime}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  evaluateVectorBalls (viscosityBalls hV o C L α a b ha hb) ε
    (vectorBallReady_exists (viscosityBalls_converges hV o C L α a b ha hb) hε)

theorem evaluateViscosityForce_spec {V : ℝ → Plane → Plane} {ν : ℝ} {y : SpaceTime}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (detectorViscosityForce V C L ν) α y -
      rationalVector (evaluateViscosityForce hV o C L α a b ha hb ε hε)‖ ≤ (ε : ℝ) :=
  evaluateVectorBalls_spec _ (viscosityBalls_converges hV o C L α a b ha hb)
    (viscosityBalls_contains hV o C L α a b ha hb) ε hε

def viscosityForceBound {V : ℝ → Plane → Plane} (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (T : ℚ) : ℚ :=
  viscosityBound a ^ (α.count 0 + 2) * unitForceBound o C L α (viscosityBound a * |T|)

theorem viscosityForceBound_spec {V : ℝ → Plane → Plane} {ν : ℝ} (hν : 0 < ν)
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (components V))
    (C L : ℕ) (α : List (Fin 4)) {a : ℕ → ℚ} (ha : IsFastRealName a ν)
    (T : ℚ) {y : SpaceTime} (ht : 0 ≤ y.1) (htT : y.1 ≤ (T : ℝ)) :
    ‖mixedDerivative (detectorViscosityForce V C L ν) α y‖ ≤
      (viscosityForceBound o C L α a T : ℝ) := by
  have hB : (1 : ℝ) ≤ (viscosityBound a : ℝ) := by exact_mod_cast viscosityBound_ge_one a
  have hn : ν ≤ (viscosityBound a : ℝ) := (le_abs_self ν).trans (viscosityBound_spec ha)
  have ht' : ν * y.1 ≤ (viscosityBound a * |T| : ℚ) := by
    push_cast
    exact mul_le_mul hn (htT.trans (le_abs_self _)) ht (by linarith)
  have hf := unitForceBound_spec hV o C L α (viscosityBound a * |T|)
    (y := (ν * y.1, y.2)) (mul_nonneg hν.le ht) ht'
  have hfn : (0 : ℝ) ≤ unitForceBound o C L α (viscosityBound a * |T|) := by
    exact_mod_cast unitForceBound_nonneg o C L α (viscosityBound a * |T|)
  apply (pi_norm_le_iff_of_nonneg (by
    dsimp only [viscosityForceBound]
    push_cast
    exact mul_nonneg (pow_nonneg (by linarith) _) hfn)).mpr
  intro j
  rw [mixedDerivative_detectorViscosityForce V hV, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg hν.le _)]
  have hk : α.count 0 + (if j = 2 then 1 else 2) ≤ α.count 0 + 2 := by
    split_ifs <;> omega
  have hp : ν ^ (α.count 0 + if j = 2 then 1 else 2) ≤
      (viscosityBound a : ℝ) ^ (α.count 0 + 2) :=
    (pow_le_pow_left₀ hν.le hn _).trans (pow_le_pow_right₀ hB hk)
  have hh := (norm_le_pi_norm
    (mixedDerivative (detectorForce V C L) α (ν * y.1, y.2)) j).trans hf
  simpa only [viscosityForceBound, Rat.cast_mul, Rat.cast_pow, Real.norm_eq_abs] using
    mul_le_mul hp hh (abs_nonneg _) (pow_nonneg (by linarith) _)

end ForcedComputation.VelocityDetector.CompactProgram

end

end OAI
