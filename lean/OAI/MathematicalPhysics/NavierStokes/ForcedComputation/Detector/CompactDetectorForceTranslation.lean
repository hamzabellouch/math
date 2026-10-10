import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorGeneral
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorNames
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorViscosity

namespace OAI

/-! Translation of the prescribed full force.  The coordinate formulas
also give a finite evaluator for every effective center, by translating
the input oracle and the evaluation point in opposite directions. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CompactCenter
open ShearFlows
open scoped ContDiff BigOperators

def shiftVector (δ : Plane) : Space := atHeight δ 0
def shiftSpaceTime (δ : Plane) : SpaceTime := (0, shiftVector δ)
def translateVelocity (δ : Plane) (U : Velocity) : Velocity :=
  fun y => U (y + shiftSpaceTime δ)

theorem horizontal_shift (δ : Plane) (x : Space) :
    horizontalLinear (x + shiftVector δ) = horizontalLinear x + δ := by
  ext j
  fin_cases j <;> rfl

theorem components_translated (δ : Plane) (V : ℝ → Plane → Plane) :
    CompactProgram.components (translateField δ V) =
      CompactNames.inputShift (CompactProgram.components V) (shiftSpaceTime δ) := by
  funext j y
  change V y.1 (horizontal y.2 + δ) j =
    V (y.1 + 0) (horizontal (y.2 + shiftVector δ)) j
  rw [add_zero, ← horizontalLinear_eq y.2,
    ← horizontalLinear_eq (y.2 + shiftVector δ), horizontal_shift]

theorem mixedDerivative_translated (δ : Plane) (U : Velocity) (α : List (Fin 4)) :
    mixedDerivative (translateVelocity δ U) α = translateVelocity δ (mixedDerivative U α) := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext y
    change fderiv ℝ (mixedDerivative (translateVelocity δ U) α) y (spaceTimeDirection j) = _
    rw [ih]
    change fderiv ℝ (fun z => mixedDerivative U α (z + shiftSpaceTime δ)) y
      (spaceTimeDirection j) = _
    rw [fderiv_comp_add_right]
    rfl

theorem vectorLaplacian_translated (δ : Plane) (a : Plane → Plane) (x : Plane) :
    planarVectorLaplacian (fun y => a (y + δ)) x = planarVectorLaplacian a (x + δ) := by
  unfold planarVectorLaplacian
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun z => fderiv ℝ (fun y => a (y + δ)) z (PlanarHamiltonian.basis j)) =
      (fun z => fderiv ℝ a (z + δ) (PlanarHamiltonian.basis j)) := by
    funext z
    rw [fderiv_comp_add_right]
  rw [he]
  have hf := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun z => fderiv ℝ a z (PlanarHamiltonian.basis j)) (x := x) δ
  exact congrArg (fun D : Plane →L[ℝ] Plane => D (PlanarHamiltonian.basis j)) hf

theorem planarResidual_translated (δ : Plane) (a : ℝ → Plane → Plane)
    (ν t : ℝ) (x : Plane) :
    planarResidual ν (translateField δ a) t x = planarResidual ν a t (x + δ) := by
  unfold planarResidual
  rw [translated_fderiv]
  have hlap : planarVectorLaplacian (translateField δ a t) x =
      planarVectorLaplacian (a t) (x + δ) := by
    change planarVectorLaplacian (fun y => a t (y + δ)) x = _
    exact vectorLaplacian_translated δ (a t) x
  rw [hlap]
  rfl

theorem triangularForce_translated (δ : Plane) (a : ℝ → Plane → Plane)
    (h : ℝ → Plane → ℝ) (ν : ℝ) :
    triangularForce ν (translateField δ a) (translateField δ h) =
      translateVelocity δ (triangularForce ν a h) := by
  funext y
  simp only [triangularForce, triangularLift, planarResidual_translated, translateField,
    translateVelocity, shiftSpaceTime, Prod.fst_add, Prod.snd_add, add_zero, horizontal_shift]

theorem centeredForce_translated (V : ℝ → Plane → Plane) (p : Plane) (C L : ℕ) (ν : ℝ) :
    centeredForce V p C L ν =
      translateVelocity (-centerShift p)
        (detectorViscosityForce (translateField (centerShift p) V) C L ν) := by
  unfold centeredForce centeredDrift centeredSource detectorViscosityForce
  have ha : viscosityDrift ν
      (translateField (-centerShift p) (detectorDrift (translateField (centerShift p) V) C L)) =
      translateField (-centerShift p)
        (viscosityDrift ν (detectorDrift (translateField (centerShift p) V) C L)) := rfl
  have hh : viscositySource ν (translateField (-centerShift p) (detectorSource C L)) =
      translateField (-centerShift p) (viscositySource ν (detectorSource C L)) := rfl
  rw [ha, hh]
  exact triangularForce_translated (-centerShift p)
    (viscosityDrift ν (detectorDrift (translateField (centerShift p) V) C L))
    (viscositySource ν (detectorSource C L)) ν

theorem centeredForce_mixed (V : ℝ → Plane → Plane) (p : Plane) (C L : ℕ) (ν : ℝ)
    (α : List (Fin 4)) : mixedDerivative (centeredForce V p C L ν) α =
      translateVelocity (-centerShift p)
        (mixedDerivative (detectorViscosityForce (translateField (centerShift p) V) C L ν) α) := by
  rw [centeredForce_translated, mixedDerivative_translated]

def negatePoint (q : RationalSpaceTime) : RationalSpaceTime := (-q.1, fun j => -q.2 j)
def negateName (b : ℕ → RationalSpaceTime) : ℕ → RationalSpaceTime := fun n => negatePoint (b n)

theorem rationalPoint_negate (q : RationalSpaceTime) : rationalPoint (negatePoint q) = -rationalPoint q := by
  apply Prod.ext
  · exact Rat.cast_neg _
  · ext j
    exact Rat.cast_neg _

theorem negateName_spec {b : ℕ → RationalSpaceTime} {z : SpaceTime} (hb : IsFastName b z) :
    IsFastName (negateName b) (-z) := by
  intro n
  rw [negateName, rationalPoint_negate, neg_sub_neg, norm_sub_rev]
  exact hb n

theorem shiftSpaceTime_neg (δ : Plane) : shiftSpaceTime (-δ) = -shiftSpaceTime δ := by
  apply Prod.ext
  · simp [shiftSpaceTime]
  · ext j
    fin_cases j <;> simp [shiftSpaceTime, shiftVector, atHeight]

def translatedInputOracle {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (CompactProgram.components V))
    (p : Plane) (b : ℕ → RationalSpaceTime) (hb : IsFastName b (shiftSpaceTime (centerShift p))) :
    PlanarJetOracle (CompactProgram.components (translateField (centerShift p) V)) :=
  (components_translated (centerShift p) V).symm ▸
    CompactNames.shiftedOracle o (CompactProgram.components_smooth hV) hb

def evaluateCenteredForce {V : ℝ → Plane → Plane} {ν : ℝ} {y : SpaceTime}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (CompactProgram.components V))
    (p : Plane) (b : ℕ → RationalSpaceTime) (hb : IsFastName b (shiftSpaceTime (centerShift p)))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (c : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hc : IsFastName c y) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  CompactProgram.evaluateViscosityForce (translated_smooth (centerShift p) hV)
    (translatedInputOracle hV o p b hb) C L α a (CompactNames.addName c (negateName b)) ha
    (CompactNames.addName_spec hc (negateName_spec hb)) ε hε

theorem evaluateCenteredForce_spec {V : ℝ → Plane → Plane} {ν : ℝ} {y : SpaceTime}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (CompactProgram.components V))
    (p : Plane) (b : ℕ → RationalSpaceTime) (hb : IsFastName b (shiftSpaceTime (centerShift p)))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (c : ℕ → RationalSpaceTime)
    (ha : IsFastRealName a ν) (hc : IsFastName c y) (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (centeredForce V p C L ν) α y -
      rationalVector (evaluateCenteredForce hV o p b hb C L α a c ha hc ε hε)‖ ≤ (ε : ℝ) := by
  rw [centeredForce_mixed]
  change ‖mixedDerivative (detectorViscosityForce (translateField (centerShift p) V) C L ν) α
    (y + shiftSpaceTime (-centerShift p)) - _‖ ≤ _
  rw [shiftSpaceTime_neg]
  exact CompactProgram.evaluateViscosityForce_spec (translated_smooth (centerShift p) hV)
    (translatedInputOracle hV o p b hb) C L α a _ ha
    (CompactNames.addName_spec hc (negateName_spec hb)) ε hε

def centeredForceBound {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (CompactProgram.components V))
    (p : Plane) (b : ℕ → RationalSpaceTime) (hb : IsFastName b (shiftSpaceTime (centerShift p)))
    (C L : ℕ) (α : List (Fin 4)) (a : ℕ → ℚ) (T : ℚ) : ℚ :=
  CompactProgram.viscosityForceBound (translatedInputOracle hV o p b hb) C L α a T

theorem centeredForceBound_spec {V : ℝ → Plane → Plane} {ν : ℝ} (hν : 0 < ν)
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (o : PlanarJetOracle (CompactProgram.components V))
    (p : Plane) (b : ℕ → RationalSpaceTime) (hb : IsFastName b (shiftSpaceTime (centerShift p)))
    (C L : ℕ) (α : List (Fin 4)) {a : ℕ → ℚ} (ha : IsFastRealName a ν)
    (T : ℚ) {y : SpaceTime} (ht : 0 ≤ y.1) (hT : y.1 ≤ (T : ℝ)) :
    ‖mixedDerivative (centeredForce V p C L ν) α y‖ ≤
      (centeredForceBound hV o p b hb C L α a T : ℝ) := by
  rw [centeredForce_mixed]
  apply CompactProgram.viscosityForceBound_spec hν (translated_smooth (centerShift p) hV)
    (translatedInputOracle hV o p b hb) C L α ha T
  · simpa only [shiftSpaceTime, Prod.fst_add, add_zero] using ht
  · simpa only [shiftSpaceTime, Prod.fst_add, add_zero] using hT

end ForcedComputation.VelocityDetector.CompactCenter

end

end OAI
