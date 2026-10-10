import OAI.NumberTheory.Ostmann.ZeroDensity.ResidueRieszFinite
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothPrimePowerRemoval

namespace OAI

/-! # Removing higher prime powers from sharp residue sums -/

namespace Ostmann

open scoped BigOperators

theorem residue_mangoldt_prime_difference (q a n : ℕ) :
    |residueMangoldtWeight q a n - primeProgressionLog q a n| ≤
      if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0 := by
  have he : ((n : ZMod q) = (a : ZMod q)) ↔ Nat.ModEq q n a := by
    rw [ZMod.natCast_eq_natCast_iff]
  by_cases hp : n.Prime
  · rw [residueMangoldtWeight, primeProgressionLog, ArithmeticFunction.vonMangoldt_apply_prime hp]
    by_cases hn : Nat.ModEq q n a
    · simp [hp, hn, he.mpr hn]
    · simp [hp, hn, mt he.mp hn]
  · rw [residueMangoldtWeight, primeProgressionLog]
    simp only [hp, false_and, ↓reduceIte, sub_zero, not_false_eq_true]
    split_ifs <;> simp [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      ArithmeticFunction.vonMangoldt_nonneg]

theorem residuePsi_prime_error (q a : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    |residuePsi q a X - primeProgressionTheta q a X| ≤
      2 * Real.sqrt X * Real.log X := by
  have hzero : (if ¬Nat.Prime 0 then ArithmeticFunction.vonMangoldt 0 else 0) = (0 : ℝ) := by simp
  calc
    _ = |∑ n ∈ Finset.Icc 0 ⌊X⌋₊,
      (residueMangoldtWeight q a n - primeProgressionLog q a n)| := by
        rw [Finset.sum_sub_distrib]; rfl
    _ ≤ ∑ n ∈ Finset.Icc 0 ⌊X⌋₊,
      |residueMangoldtWeight q a n - primeProgressionLog q a n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 0 ⌊X⌋₊,
      if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0 :=
        Finset.sum_le_sum (fun n _ => residue_mangoldt_prime_difference q a n)
    _ = ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬n.Prime),
      ArithmeticFunction.vonMangoldt n := by
        rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), hzero, zero_add,
          Finset.sum_filter]
    _ = Chebyshev.psi X - Chebyshev.theta X := nonprime_mangoldt_sum X
    _ ≤ _ := (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hX)

theorem primeProgressionLog_bounds (q a n : ℕ) :
    0 ≤ primeProgressionLog q a n ∧
      primeProgressionLog q a n ≤ residueMangoldtWeight q a n := by
  by_cases hp : n.Prime ∧ Nat.ModEq q n a
  · have he : (n : ZMod q) = (a : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff n a q).mpr hp.2
    rw [primeProgressionLog, ite_eq_left hp, residueMangoldtWeight, ite_eq_left he,
      ArithmeticFunction.vonMangoldt_apply_prime hp.1]
    exact ⟨Real.log_nonneg (by exact_mod_cast hp.1.one_le), le_rfl⟩
  · rw [primeProgressionLog, ite_eq_right hp]
    exact ⟨le_rfl, residueMangoldtWeight_nonneg q a n⟩

theorem primeProgressionTheta_bounds (q a : ℕ) (X : ℝ) :
    0 ≤ primeProgressionTheta q a X ∧ primeProgressionTheta q a X ≤ residuePsi q a X := by
  constructor
  · exact Finset.sum_nonneg (fun n _ => (primeProgressionLog_bounds q a n).1)
  · exact Finset.sum_le_sum (fun n _ => (primeProgressionLog_bounds q a n).2)

end Ostmann

end OAI
