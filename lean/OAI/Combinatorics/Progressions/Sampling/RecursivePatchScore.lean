import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchRankPadding

namespace OAI

section

namespace Erdos3.PolynomialPatch
open scoped BigOperators

theorem score_mono_target {σ Ω : Type*} [Fintype Ω] {s d : ℕ}
    (P : PolynomialPatch σ s d) (t : Ω → σ → ℝ) (f : Ω → ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    (𝔼 u, (f u - b) * P.value (t u)) ≤ 𝔼 u, (f u - a) * P.value (t u) := by
  apply Finset.expect_le_expect
  intro u _
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left hab _) (P.value_mem_Icc _).1

theorem recursive_discount_score {σ Ω : Type*} [Fintype Ω] {s d D n : ℕ}
    (P : PolynomialPatch σ s d) (t : Ω → σ → ℝ) (f : Ω → ℝ)
    (hs : 1 ≤ s) (hd : d ≤ D) {Λ δ ε score : ℝ}
    (hΛ : 0 ≤ Λ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hn : n ≤ s + 1)
    (hbudget : ((s + 1 : ℕ) : ℝ) * δ ≤ ε)
    (hscore : score ≤ 𝔼 u, (f u - (1 - δ) ^ n * Λ) * P.value (t u)) :
    score ≤ 𝔼 u, (f u - (1 - ε) * Λ) * (P.padRank hs hd).value (t u) := by
  simp only [padRank_value]
  exact hscore.trans (P.score_mono_target t f
    (recursive_density_discount_scaled hΛ hδ hn hbudget))

theorem recursive_discount_prod_score {σ Ω ι : Type*} [Fintype Ω] {s d : ℕ}
    (P : PolynomialPatch σ s d) (t : Ω → σ → ℝ) (f : Ω → ℝ)
    (passages : Finset ι) (discount : ι → ℝ) {Λ δ ε score : ℝ}
    (hΛ : 0 ≤ Λ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hcount : passages.card ≤ s + 1)
    (hbudget : ((s + 1 : ℕ) : ℝ) * δ ≤ ε)
    (hdiscount : ∀ i ∈ passages, discount i ∈ Set.Icc (0 : ℝ) δ)
    (hscore : score ≤ 𝔼 u,
      (f u - (∏ i ∈ passages, (1 - discount i)) * Λ) * P.value (t u)) :
    score ≤ 𝔼 u, (f u - (1 - ε) * Λ) * P.value (t u) :=
  hscore.trans (P.score_mono_target t f (mul_le_mul_of_nonneg_right
    (recursive_density_discount_prod passages discount hδ hcount hbudget hdiscount) hΛ))

end Erdos3.PolynomialPatch

end

end OAI
