import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CompactDetectorEvaluation

namespace OAI

/-! Arbitrary effective centers are handled by fast names.  A translated
input oracle is compiled from the original oracle and the center name;
translation does not change its global derivative bounds. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CompactNames
open ShearFlows Filter
open scoped ContDiff Topology

def addPoint (q r : RationalSpaceTime) : RationalSpaceTime :=
  (q.1 + r.1, fun j => q.2 j + r.2 j)

theorem rationalPoint_add (q r : RationalSpaceTime) :
    rationalPoint (addPoint q r) = rationalPoint q + rationalPoint r := by
  apply Prod.ext
  · exact Rat.cast_add _ _
  · ext j
    exact Rat.cast_add _ _

def addName (a b : ℕ → RationalSpaceTime) : ℕ → RationalSpaceTime :=
  fun n => addPoint (a (n + 1)) (b (n + 1))

theorem addName_spec {a b : ℕ → RationalSpaceTime} {x y : SpaceTime}
    (ha : IsFastName a x) (hb : IsFastName b y) : IsFastName (addName a b) (x + y) := by
  intro n
  rw [addName, rationalPoint_add]
  have he : x + y - (rationalPoint (a (n + 1)) + rationalPoint (b (n + 1))) =
      (x - rationalPoint (a (n + 1))) + (y - rationalPoint (b (n + 1))) := by abel
  rw [he]
  calc
    _ ≤ ‖x - rationalPoint (a (n + 1))‖ + ‖y - rationalPoint (b (n + 1))‖ := norm_add_le _ _
    _ ≤ errorTolerance (n + 1) + errorTolerance (n + 1) := add_le_add (ha _) (hb _)
    _ = errorTolerance n := by
      unfold errorTolerance
      rw [pow_succ]
      have hp : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      ring

def rationalShiftName (q : RationalSpaceTime) (b : ℕ → RationalSpaceTime) :
    ℕ → RationalSpaceTime := fun n => addPoint q (b n)

theorem rationalShiftName_spec (q : RationalSpaceTime) {b : ℕ → RationalSpaceTime}
    {z : SpaceTime} (hb : IsFastName b z) :
    IsFastName (rationalShiftName q b) (rationalPoint q + z) := by
  intro n
  rw [rationalShiftName, rationalPoint_add]
  simpa only [add_sub_add_left_eq_sub] using hb n

def inputShift (F : PlanarComponents) (z : SpaceTime) : PlanarComponents :=
  fun j y => F j (y + z)

theorem inputShift_smooth {F : PlanarComponents} (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (z : SpaceTime) (j : Fin 2) : ContDiff ℝ ∞ (inputShift F z j) :=
  (hF j).comp (contDiff_id.add contDiff_const)

theorem componentJet_shift (F : PlanarComponents) (z : SpaceTime)
    (α : List (Fin 4)) (j : Fin 2) :
    componentJet (inputShift F z) α j = fun y => componentJet F α j (y + z) := by
  induction α with
  | nil => rfl
  | cons k α ih =>
    funext y
    change fderiv ℝ (componentJet (inputShift F z) α j) y (spaceTimeDirection k) = _
    rw [ih, fderiv_comp_add_right]
    rfl

theorem coordinate_clock (y : SpaceTime) : clockedPoint .coord y = y := by
  exact Prod.ext rfl rfl

def shiftedEnclosure {F : PlanarComponents} (o : PlanarJetOracle F)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) (b : ℕ → RationalSpaceTime)
    (α : List (Fin 4)) (j : Fin 2) (q : RationalSpaceTime) (n : ℕ) : QBall :=
  ⟨DetectorExpr.evaluate o hF (.input .coord α j) trivial
    (rationalShiftName q b) (ClockedExpr.dyadic n) (ClockedExpr.dyadic_pos n),
    ClockedExpr.dyadic n⟩

theorem shiftedEnclosure_contains {F : PlanarComponents} (o : PlanarJetOracle F)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) {b : ℕ → RationalSpaceTime} {z : SpaceTime}
    (hb : IsFastName b z) (α : List (Fin 4)) (j : Fin 2) (q : RationalSpaceTime) (n : ℕ) :
    (shiftedEnclosure o hF b α j q n).Contains
      (componentJet (inputShift F z) α j (rationalPoint q)) := by
  rw [componentJet_shift]
  have h := DetectorExpr.evaluate_spec o hF (e := .input .coord α j) trivial
    (rationalShiftName q b) (rationalShiftName_spec q hb)
    (ClockedExpr.dyadic n) (ClockedExpr.dyadic_pos n)
  simpa only [shiftedEnclosure, QBall.Contains, DetectorExpr.val, coordinate_clock] using h

def shiftedOracle {F : PlanarComponents} (o : PlanarJetOracle F)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) {b : ℕ → RationalSpaceTime} {z : SpaceTime}
    (hb : IsFastName b z) : PlanarJetOracle (inputShift F z) where
  bound := o.bound
  bound_nonneg := o.bound_nonneg
  jet_bound := by
    intro α j y
    rw [componentJet_shift]
    exact o.jet_bound α j (y + z)
  enclose := shiftedEnclosure o hF b
  enclose_contains := shiftedEnclosure_contains o hF hb
  enclose_converges := by
    intro α j q
    apply QBall.converges_of_contains (shiftedEnclosure_contains o hF hb α j q)
    exact ClockedExpr.dyadic_tendsto

end ForcedComputation.VelocityDetector.CompactNames

end

end OAI
