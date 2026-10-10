import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondMomentError
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMomentMainComparison
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoughCoreBound

namespace OAI

/-! # The original rough moment after both Poisson transformations -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticMomentCorrections (M R K : ℕ) (J : ℝ) (v : ℕ → ℂ) : ℂ :=
  quadraticGcdRemainder (2 * R) v (fun D z => if z.1 = z.2 then 0 else
    quadraticFirstSecondCorrections M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J -
      ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
        (jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
          quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b)

noncomputable def quadraticOffDiagonalMain (M N K : ℕ) (v : ℕ → ℂ) : ℂ :=
  quadraticGcdRemainder N v (fun D z => if z.1 = z.2 then 0 else
    quadraticPairMainDifference M D (quadraticPairKernel z.1 z.2) K)

theorem quadratic_rough_second_decomposition (M R K : ℕ) (J : ℝ) (v : ℕ → ℂ) :
    quadraticRoughOffDiagonalCore M (2 * R) K J v =
      quadraticOffDiagonalMain M (2 * R) K v + quadraticMomentCorrections M R K J v +
        quadraticSecondMomentError M R K J v := by
  unfold quadraticRoughOffDiagonalCore quadraticOffDiagonalMain quadraticMomentCorrections
    quadraticSecondMomentError quadraticGcdRemainder
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : z.1 = z.2
  · simp only [hz, ite_true, mul_zero, add_zero]
  · simp only [hz, ite_false]
    rw [quadratic_small_pair_core_main, quadratic_first_second_kernel_split]
    unfold quadraticPairMainDifference
    ring

theorem quadratic_rough_second_bound {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R K : ℕ, 1 ≤ M → 1 ≤ R →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 →
      2 * (2 * (R : ℝ)) ^ 2 * (((M : ℝ) * (2 * R)) ^ δ) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ v : ℕ → ℂ, (∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0) →
      quadraticRoughEnergy M (2 * R) K v ≤
        (3 * M + C / (((M : ℝ) * R) ^ P)) * quadraticSieveEnergy (2 * R) v +
          ‖quadraticOffDiagonalMain M (2 * R) K v‖ +
          ‖quadraticMomentCorrections M R K (((M : ℝ) * (2 * R)) ^ δ) v‖ := by
  obtain ⟨C₁, hC₁, h₁⟩ := quadratic_rough_core_bound hδ P
  obtain ⟨C₂, hC₂, h₂⟩ := quadratic_second_moment_arbitrary_power hδ P
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro M R K hM hR hK hcut v hsupp
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hprod : (0 : ℝ) < (M : ℝ) * R := by positivity
  have hbase : (M : ℝ) * R ≤ (M : ℝ) * (2 * R) := by nlinarith [hprod]
  have hpow : ((M : ℝ) * R) ^ P ≤ ((M : ℝ) * (2 * R)) ^ P :=
    pow_le_pow_left₀ hprod.le hbase P
  have hK' : (K : ℝ) ≤ ((M : ℝ) * (2 * R)) ^ 3 :=
    hK.trans (pow_le_pow_left₀ hprod.le hbase 3)
  have hcut' : 2 * (((2 * R : ℕ) : ℝ)) ^ 2 * (((M : ℝ) * (2 * R : ℕ)) ^ δ) ≤
      (M : ℝ) * ((K : ℝ) + 1) := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcut
  have hf := h₁ M (2 * R) K hM (by omega) (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hK') hcut' v
  have hj : ((M : ℝ) * R) ^ δ ≤ ((M : ℝ) * (2 * R)) ^ δ :=
    Real.rpow_le_rpow hprod.le hbase hδ.le
  have hs := h₂ M R K hM hR hK _ hj v hsupp
  have hn : ‖quadraticRoughOffDiagonalCore M (2 * R) K (((M : ℝ) * (2 * R)) ^ δ) v‖ ≤
      ‖quadraticOffDiagonalMain M (2 * R) K v‖ +
      ‖quadraticMomentCorrections M R K (((M : ℝ) * (2 * R)) ^ δ) v‖ +
      ‖quadraticSecondMomentError M R K (((M : ℝ) * (2 * R)) ^ δ) v‖ := by
    rw [quadratic_rough_second_decomposition]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have he : 0 ≤ quadraticSieveEnergy (2 * R) v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdiv : C₁ / (((M : ℝ) * (2 * R)) ^ P) ≤ C₁ / (((M : ℝ) * R) ^ P) :=
    div_le_div_of_nonneg_left hC₁.le (pow_pos hprod P) hpow
  have hc := mul_le_mul_of_nonneg_right hdiv he
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hf
  have hsum : (C₁ + C₂) / (((M : ℝ) * R) ^ P) =
      C₁ / (((M : ℝ) * R) ^ P) + C₂ / (((M : ℝ) * R) ^ P) := by ring
  rw [hsum]
  nlinarith

theorem quadratic_rough_main_correction_bound {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (P : ℕ) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ M R K : ℕ, 1 ≤ M → 1 ≤ R → 0 < K →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 →
      2 * (2 * (R : ℝ)) ^ 2 * (((M : ℝ) * (2 * R)) ^ δ) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ T : ℕ → ℝ, (∀ D ∈ Finset.Icc 1 (2 * R), 0 ≤ T D) →
      (∀ D ∈ Finset.Icc 1 (2 * R), Squarefree D → Odd D →
        QuadraticSieveBound (K * D ^ 2) (2 * R) (T D)) →
      ∀ v : ℕ → ℂ, (∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0) →
      quadraticRoughEnergy M (2 * R) K v ≤
        (3 * M + C₁ / (((M : ℝ) * R) ^ P) + C₂ * Real.sqrt M *
          (∑ D ∈ Finset.Icc 1 (2 * R), quadraticMainComparisonCost ε (2 * R) D K (T D))) *
            quadraticSieveEnergy (2 * R) v +
          ‖quadraticMomentCorrections M R K (((M : ℝ) * (2 * R)) ^ δ) v‖ := by
  obtain ⟨C₁, hC₁, h₁⟩ := quadratic_rough_second_bound hδ P
  obtain ⟨C₂, hC₂, h₂⟩ := quadratic_off_diagonal_main_comparison ε hε
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro M R K hM hR hK hK' hcut T hT hbound v hsupp
  have hf := h₁ M R K hM hR hK' hcut v hsupp
  have hm := h₂ M (2 * R) K (by omega) hK T hT hbound v
  change ‖quadraticOffDiagonalMain M (2 * R) K v‖ ≤ _ at hm
  nlinarith

end Ostmann

end OAI
