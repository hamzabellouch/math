import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorForceProgram
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorForceScaling
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ProductNames

namespace OAI

/-! The finite detector program at a named viscosity. Rational interval
products certify every output component, including all time derivatives. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

def detectorForceName (H : FieldExpr) (hH : H.Valid) (C L : ℕ)
    (α : List (Fin 4)) (b : ℕ → RationalSpaceTime) : ℕ → RationalVector := fun n =>
  evaluateDetectorForce H hH C L α b ((2 : ℚ) ^ (-(n : ℤ))) (by positivity)

theorem detectorForceName_spec {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H)
    (hV : ContDiff ℝ ∞ (Function.uncurry (planarSlice H)))
    (C L : ℕ) (α : List (Fin 4)) {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (hb : IsFastName b y) :
    IsFastVectorName (detectorForceName H hH C L α b)
      (mixedDerivative (detectorForce (planarSlice H) C L) α y) := by
  intro n
  have he := evaluateDetectorForce_spec hH hT hV C L α b hb
    ((2 : ℚ) ^ (-(n : ℤ))) (by positivity)
  simpa [detectorForceName, errorTolerance] using he

def viscosityForceBalls {ν : ℝ} {y : SpaceTime} (H : FieldExpr) (hH : H.Valid)
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hb : IsFastName b y) (n : ℕ) (j : Fin 3) : QBall :=
  ((realNameBall a n).pow (α.count 0 + if j = 2 then 1 else 2)).mul
    (vectorNameBall (detectorForceName H hH C L α (scaleTimeName a b ha hb)) n j)

theorem viscosityForceBalls_contains {ν : ℝ} {y : SpaceTime}
    {H : FieldExpr} (hH : H.Valid) (hT : SpatialExpression.NoTime H)
    (hV : ContDiff ℝ ∞ (Function.uncurry (planarSlice H)))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hb : IsFastName b y) (n : ℕ) (j : Fin 3) :
    (viscosityForceBalls H hH C L α a b ha hb n j).Contains
      (mixedDerivative (detectorViscosityForce (planarSlice H) C L ν) α y j) := by
  rw [mixedDerivative_detectorViscosityForce _ hV]
  exact QBall.contains_mul (QBall.contains_pow (realNameBall_contains ha n) _)
    (vectorNameBall_contains (detectorForceName_spec hH hT hV C L α
      (scaleTimeName_spec a b ha hb)) n j)

theorem viscosityForceBalls_converges {ν : ℝ} {y : SpaceTime}
    {H : FieldExpr} (hH : H.Valid) (hT : SpatialExpression.NoTime H)
    (hV : ContDiff ℝ ∞ (Function.uncurry (planarSlice H)))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hb : IsFastName b y) (j : Fin 3) :
    QBall.Converges (fun n => viscosityForceBalls H hH C L α a b ha hb n j)
      (mixedDerivative (detectorViscosityForce (planarSlice H) C L ν) α y j) := by
  rw [mixedDerivative_detectorViscosityForce _ hV]
  exact ((realNameBall_converges ha).pow _).mul
    (vectorNameBall_converges (detectorForceName_spec hH hT hV C L α
      (scaleTimeName_spec a b ha hb)) j)

def evaluateDetectorViscosityForce {ν : ℝ} {y : SpaceTime}
    (H : FieldExpr) (hH : H.Valid) (hT : SpatialExpression.NoTime H)
    (hV : ContDiff ℝ ∞ (Function.uncurry (planarSlice H)))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  evaluateVectorBalls (viscosityForceBalls H hH C L α a b ha hb) ε
    (vectorBallReady_exists (viscosityForceBalls_converges hH hT hV C L α a b ha hb) hε)

theorem evaluateDetectorViscosityForce_spec {ν : ℝ} {y : SpaceTime}
    {H : FieldExpr} (hH : H.Valid) (hT : SpatialExpression.NoTime H)
    (hV : ContDiff ℝ ∞ (Function.uncurry (planarSlice H)))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (detectorViscosityForce (planarSlice H) C L ν) α y -
      rationalVector (evaluateDetectorViscosityForce H hH hT hV C L α a b ha hb ε hε)‖ ≤
        (ε : ℝ) :=
  evaluateVectorBalls_spec _ (viscosityForceBalls_converges hH hT hV C L α a b ha hb)
    (viscosityForceBalls_contains hH hT hV C L α a b ha hb) ε hε

def viscosityBound (a : ℕ → ℚ) : ℚ := |a 0| + 1

theorem viscosityBound_ge_one (a : ℕ → ℚ) : 1 ≤ viscosityBound a := by
  dsimp [viscosityBound]
  linarith [abs_nonneg (a 0)]

theorem viscosityBound_spec {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν) :
    |ν| ≤ (viscosityBound a : ℝ) := by
  have he := ha 0
  simp only [errorTolerance, pow_zero, inv_one] at he
  have h := abs_add_le (ν - (a 0 : ℝ)) (a 0)
  rw [sub_add_cancel] at h
  simp only [viscosityBound, Rat.cast_add, Rat.cast_abs, Rat.cast_one]
  linarith

def detectorViscosityBound (H : FieldExpr) (C L : ℕ) (α : List (Fin 4))
    (a : ℕ → ℚ) (T : ℚ) : ℚ :=
  viscosityBound a ^ (α.count 0 + 2) *
    detectorForceBound H C L α (viscosityBound a * |T|)

theorem detectorViscosityBound_spec {ν : ℝ} (hν : 0 < ν) {H : FieldExpr}
    (hH : H.Valid) (hT : SpatialExpression.NoTime H)
    (hV : ContDiff ℝ ∞ (Function.uncurry (planarSlice H)))
    (C L : ℕ) (α : List (Fin 4)) {a : ℕ → ℚ} (ha : IsFastRealName a ν)
    (T : ℚ) {y : SpaceTime} (ht : 0 ≤ y.1) (htT : y.1 ≤ (T : ℝ)) :
    ‖mixedDerivative (detectorViscosityForce (planarSlice H) C L ν) α y‖ ≤
      (detectorViscosityBound H C L α a T : ℝ) := by
  have hB : (1 : ℝ) ≤ (viscosityBound a : ℝ) := by
    exact_mod_cast viscosityBound_ge_one a
  have hn : ν ≤ (viscosityBound a : ℝ) :=
    (le_abs_self ν).trans (viscosityBound_spec ha)
  have ht' : ν * y.1 ≤ (viscosityBound a * |T| : ℚ) := by
    push_cast
    exact mul_le_mul hn (htT.trans (le_abs_self _)) ht (by linarith)
  have hf := detectorForceBound_spec hH hT hV C L α (viscosityBound a * |T|)
    (y := (ν * y.1, y.2))
    (mul_nonneg hν.le ht) ht'
  have hfn : (0 : ℝ) ≤ detectorForceBound H C L α (viscosityBound a * |T|) := by
    exact_mod_cast detectorForceBound_nonneg H C L α (viscosityBound a * |T|)
  apply (pi_norm_le_iff_of_nonneg (by
    dsimp only [detectorViscosityBound]
    push_cast
    exact mul_nonneg (pow_nonneg (by linarith) _) hfn)).mpr
  intro j
  rw [mixedDerivative_detectorViscosityForce _ hV, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg hν.le _)]
  have hk : α.count 0 + (if j = 2 then 1 else 2) ≤ α.count 0 + 2 := by
    split_ifs <;> omega
  have hp : ν ^ (α.count 0 + if j = 2 then 1 else 2) ≤
      (viscosityBound a : ℝ) ^ (α.count 0 + 2) :=
    (pow_le_pow_left₀ hν.le hn _).trans (pow_le_pow_right₀ hB hk)
  have hv : |mixedDerivative (detectorForce (planarSlice H) C L) α
      (ν * y.1, y.2) j| ≤ (detectorForceBound H C L α (viscosityBound a * |T|) : ℝ) :=
    (norm_le_pi_norm _ j).trans hf
  simpa only [detectorViscosityBound, Rat.cast_mul, Rat.cast_pow] using
    mul_le_mul hp hv (abs_nonneg _) (pow_nonneg (by linarith) _)

end ForcedComputation.VelocityDetector

end

end OAI
