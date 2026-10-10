import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

namespace NCHitting

theorem choose_twice_add {s : ℕ} (hs : 0 < s) :
    (2*s).choose 2 + s = 2*s^2 := by
  rw [Nat.choose_two_right]
  have he : (2*s)*(2*s-1) = (s*(2*s-1))*2 := by ring
  rw [he, Nat.mul_div_left _ (by decide)]
  calc
    s*(2*s-1)+s = s*((2*s-1)+1) := by ring
    _ = s*(2*s) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ 2*s)]
    _ = 2*s^2 := by ring

theorem multiplicity_dimension_bound {n s m : ℕ}
    (hn : 0 < n) (hs : 0 < s) (hm : m ≤ 2*s) :
    (n-1)*m.choose 2 + m ≤ 2*n*s^2 := by
  by_cases h1 : n = 1
  · subst n
    simp only [Nat.sub_self, zero_mul, zero_add, mul_one]
    have hsq : s ≤ s*s := Nat.le_mul_of_pos_right s hs
    calc
      m ≤ 2*s := hm
      _ ≤ 2*(s*s) := Nat.mul_le_mul_left 2 hsq
      _ = 2*s^2 := by ring
  · have hn2 : 2 ≤ n := by omega
    have hc : m.choose 2 ≤ (2*s).choose 2 := Nat.choose_le_choose 2 hm
    calc
      (n-1)*m.choose 2 + m ≤ n*((2*s).choose 2)+2*s :=
        Nat.add_le_add (Nat.mul_le_mul (Nat.sub_le _ _) hc) hm
      _ ≤ n*((2*s).choose 2)+n*s :=
        Nat.add_le_add_left (Nat.mul_le_mul_right s hn2) _
      _ = n*((2*s).choose 2+s) := by ring
      _ = n*(2*s^2) := by rw [choose_twice_add hs]
      _ = 2*n*s^2 := by ring

end NCHitting

end OAI
