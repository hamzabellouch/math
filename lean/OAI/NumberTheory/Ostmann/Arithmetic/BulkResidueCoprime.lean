import OAI.NumberTheory.Ostmann.ZeroDensity.BulkProgressionCutoff

namespace OAI

/-! # CRT coprimality for the actual frequency and spectator moduli -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem bulkResidueModuli_pairwise {I : Type*} (r : ℕ) (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hcop : ∀ i, r.Coprime (p i)) :
    Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)) := by
  intro i j hij
  rcases i with u | i <;> rcases j with v | j
  · cases u
    cases v
    exact False.elim (hij rfl)
  · exact hcop j
  · exact (hcop i).symm
  · apply (Nat.coprime_primes (hp i) (hp j)).mpr
    exact fun he => hij (congrArg Sum.inr (hinj he))

theorem bulkResidueModuli_pairwise_of_lt {I : Type*} (r : ℕ) (hr : 0 < r)
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hrp : ∀ i, r < p i) :
    Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)) := by
  apply bulkResidueModuli_pairwise r p hp hinj
  intro i
  exact ((hp i).coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hr (hrp i))).symm

theorem bulkResidueModulus_positive {I : Type*} [Fintype I] (r : ℕ) (hr : 0 < r)
    (p : I → ℕ) (hp : ∀ i, 0 < p i) : 0 < ∏ i, bulkResidueModuli r p i := by
  apply Finset.prod_pos
  intro i _
  rcases i with u | i
  · exact hr
  · exact hp i

/-- The split-prime lower range eventually exceeds every fixed-depth
frequency modulus; this supplies the cross-block CRT coprimality. -/
theorem frequency_modulus_lt_spectators (F K a : ℝ)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ (m r : ℕ) (p : Fin m → ℕ),
      (m : ℝ) ≤ K * L → (r : ℝ) ≤ Real.exp (F * m) →
      (∀ i, Real.exp (Real.exp (a * L)) ≤ (p i : ℝ)) → ∀ i, r < p i := by
  filter_upwards [arithmetic_exponent_absorption 0 a 0 (F * K + 1) 1 1 ha ha ha (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro m r p hm hr hp i
  have hL0 : 0 ≤ L := by linarith
  have hexp : F * K * L < Real.exp (a * L) := by
    simp only [zero_mul, Real.exp_zero, mul_one, pow_one] at hrate
    nlinarith [mul_nonneg (mul_nonneg hF hK) hL0]
  have hri : (r : ℝ) < p i :=
    (hr.trans (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hm hF]))).trans_lt
      ((Real.exp_lt_exp.mpr hexp).trans_le (hp i))
  exact_mod_cast hri

end Ostmann

end OAI
