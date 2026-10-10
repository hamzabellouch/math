import OAI.Combinatorics.YoungDiagram.LiteralCapacity
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace OAI

/- Explicit real-floor identification; no rounding premise. -/
namespace ArithmeticTensorSquares.Capacity
lemma integer_division_is_floor (h d : Nat) :
    Int.floor (((h : ℝ)-(d : ℝ))/2) = ((h : Int)-(d : Int))/2 := by
  let z : Int := (h : Int)-(d : Int)
  have hlo : 2*(z/2) ≤ z := by omega
  have hhi : z < 2*(z/2+1) := by omega
  apply (Int.floor_eq_iff).2
  constructor
  · have hh : (2 : ℝ)*(z/2 : Int) ≤ (h : ℝ)-(d : ℝ) := by
      have hlo' : 2*(z/2) ≤ (h : Int)-(d : Int) := hlo
      exact_mod_cast hlo'
    linarith
  · have hh : (h : ℝ)-(d : ℝ) < (2 : ℝ)*((z/2 : Int)+1) := by
      have hhi' : (h : Int)-(d : Int) < 2*(z/2+1) := hhi
      exact_mod_cast hhi'
    linarith

lemma attachment_term_real_floor (h d : Nat) :
    max 0 (Int.floor (((h : ℝ)-(d : ℝ))/2)) = (((h-d)/2 : Nat) : Int) := by
  rw [integer_division_is_floor]
  exact attachment_term_eq h d
end ArithmeticTensorSquares.Capacity

end OAI
