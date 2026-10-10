import OAI.NumberTheory.Ostmann.Construction.MatchedHarmonicPrior
import OAI.NumberTheory.Ostmann.Construction.MatchedGraphQuotient

namespace OAI

/-! # Exact counterpart-prior extraction before the external-pivot sum -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def counterpartRoleUnary {n : ℕ} (Q : Fin n → Finset ℕ)
    (e : Equiv.Perm (Fin n)) (ν : Fin n → ℕ → ℂ) (i : Fin n) (p : ℕ) : ℂ :=
  (if p ∈ Q (e.symm i) then 1 else 0) * ν i p

theorem counterpartRoleUnary_norm {n : ℕ} (Q : Fin n → Finset ℕ)
    (e : Equiv.Perm (Fin n)) (ν : Fin n → ℕ → ℂ)
    (hν : ∀ i p, ‖ν i p‖ ≤ 1) (i : Fin n) (p : ℕ) :
    ‖counterpartRoleUnary Q e ν i p‖ ≤ 1 := by
  unfold counterpartRoleUnary
  split_ifs
  · simpa only [one_mul] using hν i p
  · simp only [zero_mul, norm_zero, zero_le_one]

theorem counterpartRole_finiteEdgeWeight {n : ℕ} (P : Finset ℕ)
    (Q : Fin n → Finset ℕ) (e : Equiv.Perm (Fin n))
    (E : Fin n → Fin n → ℕ → ℕ → ℂ) (ν : Fin n → ℕ → ℂ) (x : Fin n → P) :
    ((∏ i, counterpartRoleFactor P Q e i (x i) : ℝ) : ℂ) *
        finiteEdgeWeight E ν (fun i => (x i : ℕ)) =
      finiteEdgeWeight E (counterpartRoleUnary Q e ν) (fun i => (x i : ℕ)) := by
  simp only [Complex.ofReal_prod, finiteEdgeWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [counterpartRoleFactor, counterpartRoleUnary]
  split_ifs <;> simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul]

/-- This equality factors out the harmonic normalizer and the reciprocal
product scale before any external integer is summed. -/
theorem matched_harmonic_correlation_eq {n : ℕ} (P : Finset ℕ)
    (Q : Fin n → Finset ℕ) (e : Equiv.Perm (Fin n))
    (μ : (Fin n → P) → ℝ) (G : (Fin n → P) → ℂ)
    (X : ℝ) (hX : X ≠ 0) :
    (∑ x, (μ x : ℂ) *
      (productPrior (fun i => primeSubsetPrior P (Q i)) (fun i => x (e i)) : ℂ) * G x) =
      (((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * X⁻¹ : ℝ) : ℂ) *
        ∑ x, (μ x : ℂ) * ((X / (∏ i, (x i : ℝ)) : ℝ) : ℂ) *
          ((∏ i, counterpartRoleFactor P Q e i (x i) : ℝ) : ℂ) * G x := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [matched_harmonic_prior]
  have he (C H R : ℝ) : C * H⁻¹ * R = (C * X⁻¹) * (X / H) * R := by
    rw [div_eq_mul_inv]
    calc
      _ = C * (X⁻¹ * X) * H⁻¹ * R := by rw [inv_mul_cancel₀ hX]; ring
      _ = _ := by ring
  rw [he]
  push_cast
  ring

/-- The actual two-prior correlation has the already-extracted small factor.
Its hypothesis is the normalized ratio bound supplied by FullPrimeRatioPair. -/
theorem matched_harmonic_correlation_bound {n : ℕ} (P : Finset ℕ)
    (Q : Fin n → Finset ℕ) (e : Equiv.Perm (Fin n))
    (μ : (Fin n → P) → ℝ) (G : (Fin n → P) → ℂ)
    (X δ : ℝ) (hX : 0 < X)
    (hbound : ‖∑ x, (μ x : ℂ) * ((X / (∏ i, (x i : ℝ)) : ℝ) : ℂ) *
      ((∏ i, counterpartRoleFactor P Q e i (x i) : ℝ) : ℂ) * G x‖ ≤ δ) :
    ‖∑ x, (μ x : ℂ) *
      (productPrior (fun i => primeSubsetPrior P (Q i)) (fun i => x (e i)) : ℂ) * G x‖ ≤
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * X⁻¹ * δ := by
  rw [matched_harmonic_correlation_eq P Q e μ G X hX.ne', norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end Ostmann

end OAI
