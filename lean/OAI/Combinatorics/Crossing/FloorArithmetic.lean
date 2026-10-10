import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace OAI

namespace Zarankiewicz

def axisPairs (r : ℕ) : ℕ := (r/2) * ((r-1)/2)

theorem square_quarter_even (r : ℕ) : (2*r)*(2*r)/4 = r*r := by
  rw [show (2*r)*(2*r) = r*r*4 by ring, Nat.mul_div_left _ (by decide : 0<4)]

theorem square_quarter_odd (r : ℕ) : (2*r+1)*(2*r+1)/4 = r*r+r := by
  rw [show (2*r+1)*(2*r+1) = 1+(r*r+r)*4 by ring,
    Nat.add_mul_div_right _ _ (by decide : 0<4)]
  omega

theorem axisPairs_even (r : ℕ) : axisPairs (2*r) = r*(r-1) := by
  unfold axisPairs
  have h₁ : 2*r/2 = r := by omega
  have h₂ : (2*r-1)/2 = r-1 := by omega
  rw [h₁,h₂]

theorem axisPairs_odd (r : ℕ) : axisPairs (2*r+1) = r*r := by
  unfold axisPairs
  have h₁ : (2*r+1)/2 = r := by omega
  have h₂ : (2*r+1-1)/2 = r := by omega
  rw [h₁,h₂]

theorem diagonal_floor_identity (m : ℕ) :
    2*axisPairs m + m + 2*(m*m/4) = m*m := by
  have hm : m = 2*(m/2) ∨ m = 2*(m/2)+1 := by omega
  rcases hm with hm | hm
  · generalize m/2 = r at hm
    subst m
    rw [axisPairs_even, square_quarter_even]
    cases r with
    | zero => simp
    | succ r => simp only [Nat.add_sub_cancel]; ring
  · generalize m/2 = r at hm
    subst m
    rw [axisPairs_odd, square_quarter_odd]
    ring

end Zarankiewicz

end OAI
