import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Factorial dilation and square arithmetic reductions
-/

section

/-! Arithmetic in the permutation-product step of Lemma `lem:universal`.
The input `s` is the natural sum of arbitrary multiplicity entries. No
geometric existence or incidence statement is encoded in these lemmas. -/
namespace Nagata.Workers.W14

/-- A violating multiplicity sum is positive when the degree and point count are positive. -/
theorem multiplicity_sum_pos {r d s : ℕ} (hr : 0 < r) (hd : 0 < d)
    (h : (d : ℝ) * Real.sqrt r ≤ s) : 0 < s := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs' : (0 : ℝ) < s :=
    lt_of_lt_of_le (mul_pos hd' (Real.sqrt_pos.2 hr')) h
  exact_mod_cast hs'

/-- The scalar ratio estimate underlying symmetrization. -/
theorem symmetrized_ratio_le {r d s : ℕ} (hs : 0 < s)
    (h : (d : ℝ) * Real.sqrt r ≤ s) :
    (r : ℝ) * d / s ≤ Real.sqrt r := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  apply (div_le_iff₀ hs').2
  calc
    (r : ℝ) * d = Real.sqrt r * ((d : ℝ) * Real.sqrt r) := by
      calc
        (r : ℝ) * d = (d : ℝ) * (Real.sqrt r * Real.sqrt r) := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg r)]
          exact mul_comm _ _
        _ = _ := by ac_rfl
    _ ≤ Real.sqrt r * s := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)

/-- Cancel the factorial that occurs in every point's multiplicity. -/
theorem factorial_ratio_eq {r d s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ((r.factorial * d : ℕ) : ℝ) / (((r - 1).factorial * s : ℕ) : ℝ) =
      (r : ℝ) * d / s := by
  have hf : ((r - 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (r - 1))
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [← Nat.mul_factorial_pred hr.ne']
  push_cast
  apply (div_eq_div_iff (mul_ne_zero hf hs') hs').2
  simp only [mul_assoc, mul_comm, mul_left_comm]

/-- Exact positive degree and common multiplicity produced by the permutation product. -/
theorem factorial_symmetrization {r d s : ℕ} (hr : 0 < r) (hd : 0 < d)
    (h : (d : ℝ) * Real.sqrt r ≤ s) :
    0 < r.factorial * d ∧ 0 < (r - 1).factorial * s ∧
      ((r.factorial * d : ℕ) : ℝ) / (((r - 1).factorial * s : ℕ) : ℝ) ≤
        Real.sqrt r := by
  have hs := multiplicity_sum_pos hr hd h
  refine ⟨Nat.mul_pos (Nat.factorial_pos _) hd,
    Nat.mul_pos (Nat.factorial_pos _) hs, ?_⟩
  rw [factorial_ratio_eq hr hs]
  exact symmetrized_ratio_le hs h

/-- Taking common positive powers preserves the degree to multiplicity ratio. -/
theorem common_power_ratio (d m N : ℕ) (hN : 0 < N) :
    ((N * d : ℕ) : ℝ) / ((N * m : ℕ) : ℝ) = (d : ℝ) / m := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  exact mul_div_mul_left _ _ hN'

end Nagata.Workers.W14

end

section

namespace Nagata.Workers.W14

/-- For nonsquare point counts a rational homogeneous slope cannot equal the boundary. -/
theorem ratio_ne_sqrt_of_nonsquare (r d m : ℕ) (hr : ¬ IsSquare r) :
    (d : ℝ) / m ≠ Real.sqrt r := by
  intro heq
  apply hr
  apply Rat.isSquare_natCast_iff.mp
  refine ⟨(d : ℚ) / m, ?_⟩
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [heq]
  exact (Real.mul_self_sqrt (Nat.cast_nonneg r)).symm

/-- Consequently a weak homogeneous bound is strict for nonsquare `r`. -/
theorem ratio_lt_sqrt_of_nonsquare {r d m : ℕ} (hr : ¬ IsSquare r)
    (h : (d : ℝ) / m ≤ Real.sqrt r) : (d : ℝ) / m < Real.sqrt r :=
  lt_of_le_of_ne h (ratio_ne_sqrt_of_nonsquare r d m hr)

/-- The two numerical exclusions put the homogeneous slope in the elliptic range. -/
theorem elliptic_ratio_range {r d m : ℕ} (hr : ¬ IsSquare r) (hm : 0 < m)
    (hlow : 3 * m < d) (hhigh : (d : ℝ) / m ≤ Real.sqrt r) :
    3 < (d : ℝ) / m ∧ (d : ℝ) / m < Real.sqrt r := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨(lt_div_iff₀ hm').2 ?_, ratio_lt_sqrt_of_nonsquare hr hhigh⟩
  exact_mod_cast hlow

end Nagata.Workers.W14

end

section

/-! Arithmetic of the square branch, with the equality case retained. -/
namespace Nagata.Workers.W14

/-- The positive square root of a natural square is its natural root. -/
theorem sqrt_nat_square (k : ℕ) : Real.sqrt ((k * k : ℕ) : ℝ) = k := by
  rw [Nat.cast_mul, Real.sqrt_mul_self (Nat.cast_nonneg k)]

/-- An equality with a natural square root is equivalent to equality of squares. -/
theorem sqrt_nat_eq_iff (r k : ℕ) : Real.sqrt (r : ℝ) = k ↔ r = k * k := by
  constructor
  · intro h
    have hs := Real.mul_self_sqrt (Nat.cast_nonneg r)
    rw [h] at hs
    exact_mod_cast hs.symm
  · rintro rfl
    exact sqrt_nat_square k

/-- A square point count at least ten has root at least four. -/
theorem square_root_ge_four {r k : ℕ} (hr : 10 ≤ r) (hk : r = k * k) : 4 ≤ k := by
  by_contra h
  have hk3 : k ≤ 3 := Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
  have hs : k * k ≤ 9 := by nlinarith
  omega

/-- For a positive denominator the weak square bound is exactly the integral bound. -/
theorem square_ratio_le_iff {r k d m : ℕ} (hk : r = k * k) (hm : 0 < m) :
    (d : ℝ) / m ≤ Real.sqrt r ↔ d ≤ k * m := by
  rw [(sqrt_nat_eq_iff r k).2 hk]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hmR]
  norm_cast

end Nagata.Workers.W14

end

end OAI
