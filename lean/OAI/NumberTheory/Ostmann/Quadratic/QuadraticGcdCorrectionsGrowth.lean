import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstTotalGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallTotalGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdCorrectionAssembly

namespace OAI

/-! # All original gcd corrections are bounded by the current sieve exponent -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_corrections_first_small (M R D K : ℕ) (J : ℝ) (v : ℕ → ℂ) :
    quadraticGcdMomentCorrections M R K D J v =
      (∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (v z.2) *
        quadraticFirstSecondCorrections M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J) -
      quadraticGcdSmallTotal M J R D K v v := by
  unfold quadraticGcdMomentCorrections quadraticGcdSmallTotal
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem quadratic_gcd_corrections_growth {ξ ε δ : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ M R D K : ℕ, 0 < M → 0 < R → Squarefree D → Odd D → D ≤ R → 0 < K →
      ∀ J : ℝ, 1 ≤ J → ∀ v : ℕ → ℂ, (∀ n < R, v n = 0) →
        ‖quadraticGcdMomentCorrections M R K D J v‖ ≤
          A * (2 * D : ℝ) *
            (quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
                ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J) +
              quadraticSmallCorrectionScalar 1 ε ξ M J (2 * D) (quadraticGcdBlockSize R D)
                ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J)) *
                  (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨A₁, hA₁, hf⟩ := quadratic_first_total_growth h hξ hξ' hε hδ
  obtain ⟨A₂, hA₂, hs⟩ := quadratic_small_total_growth h hξ hξ' hε hδ
  refine ⟨A₁ + A₂, by positivity, ?_⟩
  intro M R D K hM hR hD ho hDR hK J hJ v hv
  have hfirst := hf M R D K hM hR hD ho hDR hK J hJ v hv
  have hsmall := hs M J (by exact_mod_cast hM) hJ R D K hR hD ho hK v
  let F := quadraticCorrectionScalar 1 ε ξ M J (quadraticGcdBlockSize R D)
    ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J)
  let S := quadraticSmallCorrectionScalar 1 ε ξ M J (2 * D) (quadraticGcdBlockSize R D)
    ((2 * quadraticGcdBlockSize R D) ^ 2) K (quadraticSecondWindow J)
  let P := (2 * D : ℝ) * (2 * (R : ℝ)) ^ δ * quadraticSieveEnergy (2 * R) v
  have hF : 0 ≤ F := quadraticCorrectionScalar_nonneg zero_le_one (by positivity) (by linarith) _ _ _ _
  have hS : 0 ≤ S := quadraticSmallCorrectionScalar_nonneg zero_le_one (by positivity) (by linarith) _ _ _ _ _
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [quadratic_gcd_corrections_first_small]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ A₁ * F * P + A₂ * S * P := by
      apply add_le_add
      · convert hfirst using 1; dsimp [F, P]; ring
      · convert hsmall using 1; dsimp [S, P]; ring
    _ ≤ (A₁ + A₂) * (F + S) * P := by
      nlinarith only [mul_nonneg (mul_nonneg hA₁.le hS) hP,
        mul_nonneg (mul_nonneg hA₂.le hF) hP]
    _ = _ := by dsimp [F, S, P]; ring

end Ostmann

end OAI
