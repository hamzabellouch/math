import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterLiftBounds

namespace OAI

/-! # The actual integer-lift factorial moments used for common centers -/

namespace Ostmann

open scoped BigOperators

private def intervalMatchingLiftEquiv (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ)
    {r : ℕ} (e : Fin r ↪ P) (H : ℕ) :
    {n : (Finset.Ico (-(H : ℤ)) (H + 1)) //
      ∀ i, e i ∈ matchingPrimeSubtype P a t n.1} ≃ integerLiftSet P a t e H where
  toFun n := ⟨n.1.1, Finset.mem_filter.mpr ⟨n.1.2,
    fun i => (Finset.mem_filter.mp (n.2 i)).2⟩⟩
  invFun n := ⟨⟨n.1, (Finset.mem_filter.mp n.2).1⟩,
    fun i => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp n.2).2 i⟩⟩
  left_inv n := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv n := by apply Subtype.ext; rfl

/-- The lower-order moment upper bound follows from counting residue-class
lifts of each ordered distinct prime tuple. -/
theorem interval_factorial_moment_le (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (a : ℤ) (t : ℕ → ℤ) (r H Z : ℕ) (hZ : 0 < Z) (hmin : ∀ p ∈ P, Z ≤ p) :
    (∑ n : (Finset.Ico (-(H : ℤ)) (H + 1)),
      ((matchingPrimes P a t n.1).card.descFactorial r : ℝ)) ≤
    (P.card.descFactorial r : ℝ) * ((2 * (H : ℝ) + 1) / (Z : ℝ) ^ r + 1) := by
  classical
  let S := fun n : (Finset.Ico (-(H : ℤ)) (H + 1)) => matchingPrimeSubtype P a t n.1
  have hcount (e : Fin r ↪ P) :
      (Fintype.card {n : (Finset.Ico (-(H : ℤ)) (H + 1)) // ∀ i, e i ∈ S n} : ℝ) ≤
        (2 * (H : ℝ) + 1) / (Z : ℝ) ^ r + 1 := by
    rw [Fintype.card_congr (intervalMatchingLiftEquiv P a t e H), Fintype.card_coe]
    have h := card_integerLiftSet_le_uniform P hprime a t e H Z hZ hmin
    have hc := Rat.cast_le (K := ℝ).mpr h
    push_cast at hc
    exact hc
  calc
    _ = ∑ e : Fin r ↪ P,
        (Fintype.card {n : (Finset.Ico (-(H : ℤ)) (H + 1)) // ∀ i, e i ∈ S n} : ℝ) := by
      have h := sum_matching_factorials S r
      dsimp [S] at h
      simp only [card_matchingPrimeSubtype] at h
      exact_mod_cast h
    _ ≤ ∑ _e : Fin r ↪ P, ((2 * (H : ℝ) + 1) / (Z : ℝ) ^ r + 1) :=
      Finset.sum_le_sum fun e _ => hcount e
    _ = _ := by simp; ring

/-- A supplied family of witnessed tuples gives the high moment directly. -/
theorem interval_factorial_moment_ge (P : Finset ℕ) (a : ℤ) (t : ℕ → ℤ) (r H : ℕ)
    (E : Finset (Fin r ↪ P))
    (hlift : ∀ e ∈ E, ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
      ∀ i, ((e i).1 : ℤ) ∣ n - a * t (e i).1) :
    (E.card : ℝ) ≤ ∑ n : (Finset.Ico (-(H : ℤ)) (H + 1)),
      ((matchingPrimes P a t n.1).card.descFactorial r : ℝ) := by
  classical
  have h := card_tuples_le_sum_matching_factorials
    (fun n : (Finset.Ico (-(H : ℤ)) (H + 1)) => matchingPrimeSubtype P a t n.1) r E
    (fun e he => by
      obtain ⟨n, hn, hni⟩ := hlift e he
      exact ⟨⟨n, hn⟩, fun i => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hni i⟩⟩)
  simp only [card_matchingPrimeSubtype] at h
  exact_mod_cast h

/-- The interval length supplies the prime-intersection logarithmic budget. -/
theorem liftInterval_log_difference (H K : ℕ) (V : ℝ)
    (hbudget : Real.log (2 * (H : ℝ)) < (K + 1 : ℕ) * V)
    (n m : ℤ) (hn : n ∈ Finset.Ico (-(H : ℤ)) (H + 1))
    (hm : m ∈ Finset.Ico (-(H : ℤ)) (H + 1)) (hne : n ≠ m) :
    Real.log ((n - m).natAbs : ℝ) < (K + 1 : ℕ) * V := by
  have hn' := Finset.mem_Ico.mp hn
  have hm' := Finset.mem_Ico.mp hm
  have hd : (n - m).natAbs ≤ 2 * H := by omega
  have hp : (0 : ℝ) < (n - m).natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hd' : ((n - m).natAbs : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hd
  exact (Real.log_le_log hp hd').trans_lt hbudget

end Ostmann

end OAI
