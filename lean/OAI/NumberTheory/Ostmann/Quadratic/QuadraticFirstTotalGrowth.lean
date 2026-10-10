import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdSecondGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstCorrectionIdentity

namespace OAI

/-! # Every original first-transform correction, with all four signs retained -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_first_total_growth {ξ ε δ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D ≤ R → 0 < K →
      ∀ J : ℝ, 1 ≤ J → ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (v z.2) *
          quadraticFirstSecondCorrections M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J‖ ≤
        A * (2 * D : ℝ) * quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
          ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) *
            (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v := by
  classical
  have ha (a : quadraticPoissonSigns) := quadratic_gcd_second_growth h hξ hξ' hε hδ
    quadraticSieveWeight (a : ℤ) (quadraticPoissonSigns_abs a.property)
  choose A hA hbound using ha
  let C := 1 + ∑ a : quadraticPoissonSigns, A a
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun a (_ : a ∈ (Finset.univ : Finset quadraticPoissonSigns)) => (hA a).le)
    change 0 < 1 + (∑ a : quadraticPoissonSigns, A a)
    linarith only [this]
  refine ⟨C, hC, ?_⟩
  intro M R D K hM hR hD ho hDR hK J hJ v hv
  let T := quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
    ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) *
      (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (mul_nonneg
      (quadraticCorrectionScalar_nonneg zero_le_one (by positivity) (by linarith) _ _ _ _)
      (Real.rpow_nonneg (by positivity) _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [quadratic_first_correction_identity]
  calc
    _ ≤ ∑ e ∈ (2 * D).divisors, ∑ a : quadraticPoissonSigns,
        ‖quadraticGcdSecondTotal quadraticSieveWeight (a : ℤ)
          (quadraticPoissonSigns_abs a.property) M ((R : ℝ) / D) J R D e K ((e : ℤ) * a) v v‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e _
      rw [norm_mul]
      have he : ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
      exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
        (by simpa only [one_mul] using norm_sum_le (Finset.univ : Finset quadraticPoissonSigns) _)
    _ ≤ ∑ e ∈ (2 * D).divisors, ∑ a : quadraticPoissonSigns, A a * T := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro a _
      simpa only [T, mul_assoc] using hbound a M J (by exact_mod_cast hM) hJ
        R D e K hR hD ho hDR (Nat.pos_of_mem_divisors he) hK ((e : ℤ) * a) v hv
    _ = ((2 * D).divisors.card : ℝ) * ((∑ a : quadraticPoissonSigns, A a) * T) := by
      simp only [← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (2 * D : ℝ) * (C * T) := by
      apply mul_le_mul
      · exact_mod_cast Nat.card_divisors_le_self (2 * D)
      · apply mul_le_mul_of_nonneg_right _ hT
        change (∑ a : quadraticPoissonSigns, A a) ≤ 1 + (∑ a : quadraticPoissonSigns, A a)
        linarith
      · exact mul_nonneg (Finset.sum_nonneg fun a _ => (hA a).le) hT
      · positivity
    _ = _ := by dsimp [T]; ring

end Ostmann

end OAI
