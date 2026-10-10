import OAI.NumberTheory.Ostmann.QuadraticCenter.RationalPhaseBlock

namespace OAI

/-! # Uniform harmonic control of an arbitrarily translated frequency grid -/

namespace Ostmann

open scoped BigOperators

private theorem centered_grid_separation (q : ℕ) [NeZero q] (α : ℝ)
    (i j : Fin q) (hij : i ≠ j) :
    1 / (2 * (q : ℝ)) ≤
      |(α + (i.val : ℝ) / q - (round (α + (i.val : ℝ) / q) : ℤ)) -
        (α + (j.val : ℝ) / q - (round (α + (j.val : ℝ) / q) : ℤ))| := by
  let z : ℤ := (i.val : ℤ) - j.val -
    (q : ℤ) * (round (α + (i.val : ℝ) / q) - round (α + (j.val : ℝ) / q))
  have hz : z ≠ 0 := by
    intro hz
    have he := congrArg (fun t : ℤ => (t : ZMod q)) hz
    simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, sub_zero, Int.cast_zero] at he
    have he' := congrArg ZMod.val (sub_eq_zero.mp he)
    apply hij
    apply Fin.ext
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using he'
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have heq : (z : ℝ) = (q : ℝ) *
      ((α + (i.val : ℝ) / q - (round (α + (i.val : ℝ) / q) : ℤ)) -
        (α + (j.val : ℝ) / q - (round (α + (j.val : ℝ) / q) : ℤ))) := by
    dsimp [z]
    push_cast
    field_simp [hq.ne']
    ring
  have habs : (1 : ℝ) ≤ |(z : ℝ)| := by
    have hp : (0 : ℤ) < |z| := abs_pos.mpr hz
    have hh : (1 : ℤ) ≤ |z| := by omega
    exact_mod_cast hh
  rw [heq, abs_mul, abs_of_pos hq] at habs
  apply (div_le_iff₀ (by positivity : 0 < 2 * (q : ℝ))).mpr
  nlinarith

/-- No Diophantine approximation of the offset `α` is required. A closest
frequency costs `N`; all remaining frequencies cost the harmonic sum. -/
theorem uniform_phase_grid_bound (q : ℕ) [NeZero q] (α : ℝ) (N : ℕ) :
    (∑ i : Fin q, ‖∑ n ∈ Finset.range N,
      realAdditivePhase (α + (i.val : ℝ) / q) ^ n‖) ≤
      2 * ((N : ℝ) + q * (1 + Real.log q)) := by
  classical
  let f : Fin q → ℝ := fun i => α + (i.val : ℝ) / q - (round (α + (i.val : ℝ) / q) : ℤ)
  let w : Fin q → ℝ := fun i => ‖∑ n ∈ Finset.range N,
    realAdditivePhase (α + (i.val : ℝ) / q) ^ n‖
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hb := separated_phase_weight_sum Finset.univ f w q N hq (Nat.cast_nonneg N)
    (fun i _ => abs_sub_round _) (fun i _ j _ hij => centered_grid_separation q α i j hij)
    (fun i _ => norm_nonneg _)
    (fun i _ => (linear_phase_sum_distance_bound (α + (i.val : ℝ) / q) N).1)
    (fun i _ => (linear_phase_sum_distance_bound (α + (i.val : ℝ) / q) N).2)
  rw [phase_bin_sum_eq] at hb
  exact hb.trans (by
    have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log q) (Nat.cast_nonneg q)
    dsimp [w] at hb ⊢
    linarith)

end Ostmann

end OAI
