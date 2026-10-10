import OAI.NumberTheory.DirichletL.CubicSieve.FrequencyShell

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicDualCoefficient {n : Type*} (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (j : n) : ℂ :=
  star (a j * gaussTwo (cols j) (hc j).2) / (‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ)

lemma cubicDualCoefficient_norm_sq {n : Type*}
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ) (j : n) :
    ‖cubicDualCoefficient cols hc a j‖ ^ 2 = ‖a j‖ ^ 2 / (Ideal.absNorm (cols j) : ℝ) := by
  simp only [cubicDualCoefficient, norm_div, norm_star, norm_mul, gaussTwo_norm_one _ (hc j),
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_pow,
    primaryGenerator_norm_sq _ (hc j).2]

lemma cubicDualCoefficient_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (N : ℝ) (hN : 0 < N) (hcols : ∀ j, N / 2 ≤ (Ideal.absNorm (cols j) : ℝ)) :
    (∑ j, ‖cubicDualCoefficient cols hc a j‖ ^ 2) ≤ (2 / N) * ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [cubicDualCoefficient_norm_sq]
  calc
    _ ≤ ‖a j‖ ^ 2 / (N / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (hcols j)
    _ = _ := by field_simp

def cubicDualRow {n : Type*} [Fintype n] (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (h : O) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
      ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ))) *
      (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
      paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) else 0

lemma cubicDualRow_eq_gram {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (h : O) :
    cubicDualRow cols hc a W M h =
      ∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
        star (cubicRow (cols j) h * cubicDualCoefficient cols hc a j) *
          (cubicRow (cols k) h * cubicDualCoefficient cols hc a k) else 0) *
        paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
          ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) := by
  unfold cubicDualRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [isCoprime_comm (x := cols k) (y := cols j)]
  by_cases hcop : IsCoprime (cols j) (cols k)
  · rw [ite_eq_left hcop, ite_eq_left hcop]
    have hscale : (Ideal.absNorm (cols k) : ℝ) * (Ideal.absNorm (cols j) : ℝ) =
        (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) := mul_comm _ _
    rw [hscale]
    congr 1
    simp only [cubicDualCoefficient, star_mul, star_div₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  · simp only [ite_eq_right hcop, zero_mul]

lemma cubicRow_zero_of_ne_one (I : Ideal O) (hI : Admissible I) (hI1 : I ≠ 1) :
    cubicRow I 0 = 0 := by
  have hI_top : I ≠ ⊤ := by simpa only [Ideal.one_eq_top] using hI1
  have hcop : ¬ IsCoprime I (Ideal.span {(0 : O)}) := by
    simpa only [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_zero, sup_bot_eq] using hI_top
  have h := idealSymbol_cube_mask I 0 hI.2
  rw [ite_eq_right hcop] at h
  exact eq_zero_of_pow_eq_zero h

end
end SevenEighths.CubicSieve

end OAI
