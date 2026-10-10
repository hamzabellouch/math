import OAI.NumberTheory.Ostmann.QuadraticSieve.NonsquareJacobiCharacter

namespace OAI

/-! # Initial sums of nonprincipal periodic characters -/

namespace Ostmann

open scoped BigOperators

private theorem sum_range_periodic_blocks (f : ℕ → ℝ) (q : ℕ)
    (hp : Function.Periodic f q) (hz : ∑ a ∈ Finset.range q, f a = 0)
    (k r : ℕ) : ∑ a ∈ Finset.range (k * q + r), f a = ∑ a ∈ Finset.range r, f a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * q + r = q + (k * q + r) by ring, Finset.sum_range_add, hz, zero_add]
    have hp' (a : ℕ) : f (q + a) = f a := by simpa only [Nat.add_comm] using hp a
    simpa only [hp'] using ih

theorem periodic_zero_sum_range_bound (f : ℕ → ℝ) (q : ℕ) (hq : 0 < q)
    (hp : Function.Periodic f q) (hz : ∑ a ∈ Finset.range q, f a = 0)
    (hb : ∀ a, |f a| ≤ 1) (N : ℕ) : |∑ a ∈ Finset.range N, f a| ≤ q := by
  have he : N / q * q + N % q = N := by simpa only [Nat.mul_comm] using Nat.div_add_mod N q
  rw [← he, sum_range_periodic_blocks f q hp hz]
  calc
    _ ≤ ∑ a ∈ Finset.range (N % q), |f a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.range (N % q), (1 : ℝ) := Finset.sum_le_sum (fun a _ => hb a)
    _ = (N % q : ℕ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt N hq).le

theorem nonprincipal_character_sum_range_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) (N : ℕ) :
    |∑ a ∈ Finset.range N, χ (a : ZMod q)| ≤ q := by
  apply periodic_zero_sum_range_bound (fun a => χ (a : ZMod q)) q
    (Nat.pos_of_ne_zero (NeZero.ne q))
  · intro a
    simp
  · have hsum : ∑ a : Fin q, χ ((a.val : ℕ) : ZMod q) = 0 := by
      have he := (ZMod.finEquiv q).toEquiv.sum_comp (fun a => χ a)
      have heq (a : Fin q) : (ZMod.finEquiv q).toEquiv a = (a.val : ZMod q) := by
        cases q with
        | zero => exact Fin.elim0 a
        | succ q =>
          apply Fin.ext
          exact (Nat.mod_eq_of_lt a.isLt).symm
      simp_rw [heq] at he
      exact he.trans (MulChar.sum_eq_zero_of_ne_one hχ)
    exact (Fin.sum_univ_eq_sum_range (fun a => χ (a : ZMod q)) q).symm.trans hsum
  · intro a
    simpa only [Real.norm_eq_abs] using χ.norm_le_one (a : ZMod q)

/-- The nonsquare term in the original odd-modulus Jacobi moment has a
uniform initial-sum bound, with no analytic hypothesis. -/
theorem nonsquare_jacobi_sum_range_bound (n N : ℕ) (hn : 0 < n)
    (hns : ¬IsSquare n) :
    |∑ a ∈ Finset.range N, if Odd a then realJacobi n a else 0| ≤ 8 * n := by
  obtain ⟨χ, hχ, hv⟩ := exists_nonsquare_jacobi_character n hn hns
  let : NeZero (8 * n) := ⟨by omega⟩
  simpa only [hv, Nat.cast_mul, Nat.cast_ofNat] using
    nonprincipal_character_sum_range_bound (8 * n) χ hχ N

end Ostmann

end OAI
