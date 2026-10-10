import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarForcing
import OAI.Computability.QuantumFactoring.BitStackRationals
import OAI.Computability.QuantumFactoring.BitStackProcedures

namespace OAI

/-! Exact rational evaluation of the actual compact planar forcing.
Only rational arithmetic and a sign test occur. -/

namespace ContinuumCoulomb.PlanarForcingProgram
open ExactQuantumFactoring.BitStackProgram

def position (q : ℚ × ℚ) : PlanarPosition := WithLp.toLp 2 ![(q.1 : ℝ), (q.2 : ℝ)]

def value (q : ℚ × ℚ) : ℚ := max (1 - (q.1 ^ 2 + q.2 ^ 2)) 0 ^ 16

theorem position_norm_sq (q : ℚ × ℚ) :
    ‖position q‖ ^ 2 = (q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, position, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]

theorem value_cast (q : ℚ × ℚ) : (value q : ℝ) = planarForcing (position q) := by
  rw [planarForcing, positivePartSixteen, position_norm_sq]
  unfold value
  push_cast
  rfl

noncomputable def program : Procedure (prodCode ratCode ratCode) ratCode value := by
  let x := Procedure.first ratCode ratCode
  let y := Procedure.second ratCode ratCode
  let xsq := Procedure.ratMul.comp (x.pair x)
  let ysq := Procedure.ratMul.comp (y.pair y)
  let squareSum := Procedure.ratAdd.comp (xsq.pair ysq)
  let one := Procedure.constant (prodCode ratCode ratCode) ratCode (1 : ℚ)
  let zero := Procedure.constant (prodCode ratCode ratCode) ratCode (0 : ℚ)
  let z := Procedure.ratSub.comp (one.pair squareSum)
  let negative := Procedure.intSign.comp (Procedure.ratNum.comp z)
  let positive := Procedure.conditional negative zero z
  let second := Procedure.ratMul.comp (positive.pair positive)
  let fourth := Procedure.ratMul.comp (second.pair second)
  let eighth := Procedure.ratMul.comp (fourth.pair fourth)
  let sixteenth := Procedure.ratMul.comp (eighth.pair eighth)
  exact sixteenth.congrFun (by
    intro q
    simp only [Function.comp_apply, Rat.num_neg, decide_eq_true_eq]
    unfold value
    simp only [pow_two]
    split_ifs with h
    · rw [max_eq_right (le_of_lt h)]
      norm_num
    · rw [max_eq_left (le_of_not_gt h)]
      ring)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime (prodCode ratCode ratCode) ratCode value := program.toTM2

end ContinuumCoulomb.PlanarForcingProgram

end OAI
