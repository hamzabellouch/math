import OAI.NumberTheory.CubicMoment.Estimates.BilinearKernelIdentity
import OAI.NumberTheory.CubicMoment.Estimates.BipartiteEnergy

namespace OAI

/-! Quantitative removal of the shared-prime terms in the factored model. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_modelOverlap_le (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (u : ℝ) {A L : ℝ} (hA : 0 < A) (hL : 0 < L)
    (hP : ∀ a ∈ P, A ≤ norm a) (hB : ∀ b ∈ B, L ≤ norm b) :
    ‖modelOverlap P B α β u‖ ≤ cStar*A^(-1/6:ℝ)*L^(-1/6:ℝ)*
      ∑ a ∈ P, ∑ b ∈ B, if ¬IsCoprime a b then ‖α a‖*‖β b‖ else 0 := by
  unfold modelOverlap
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  by_cases hcop : IsCoprime a b
  · simp only [hcop,ite_true,not_true_eq_false,ite_false,norm_zero,mul_zero,le_refl]
  · simp only [hcop,ite_false,not_false_eq_true,ite_true,norm_mul,norm_pow,
      norm_normTwist,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos cStar_pos,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have hm : ‖(idealMoebius a:ℂ)‖^2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_idealMoebius_le_one a) 2
    have hpa : norm a^(-1/6:ℝ) ≤ A^(-1/6:ℝ) :=
      Real.rpow_le_rpow_of_nonpos hA (hP a ha) (by norm_num)
    have hpb : norm b^(-1/6:ℝ) ≤ L^(-1/6:ℝ) :=
      Real.rpow_le_rpow_of_nonpos hL (hB b hb) (by norm_num)
    have hcs := cStar_pos
    have hna := norm_nonneg a
    have hnb := norm_nonneg b
    calc
      _ ≤ cStar*‖α a‖*‖β b‖*1*A^(-1/6:ℝ)*L^(-1/6:ℝ) := by gcongr
      _ = _ := by ring

lemma modelOverlap_norm_sq_le (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (u : ℝ) {A L Y D : ℝ} (hA : 0 < A) (hL : 0 < L) (hY : 0 ≤ Y) (hD : 0 < D)
    (hP : ∀ a ∈ P, a ≠ 0 ∧ A ≤ norm a ∧ norm a ≤ Y)
    (hB : ∀ b ∈ B, primary b ∧ Squarefree b ∧ L ≤ norm b) (n : ℕ)
    (hn : ∀ b ∈ B, (primaryPrimeFactors b).card ≤ n)
    (hrough : ∀ b ∈ B, ∀ p ∈ primaryPrimeFactors b, D ≤ norm p) :
    ‖modelOverlap P B α β u‖^2 ≤
      (cStar*A^(-1/6:ℝ)*L^(-1/6:ℝ))^2*
      (((B.card:ℝ)*∑ a ∈ P, ‖α a‖^2)*
        ((n:ℝ)*(18*Y/D)*∑ b ∈ B, ‖β b‖^2)) := by
  have hh := norm_modelOverlap_le P B α β u hA hL
    (fun a ha => (hP a ha).2.1) (fun b hb => (hB b hb).2.2)
  have he := noncoprime_bipartite_energy P B α β hY hD
    (fun a ha => ⟨(hP a ha).1,(hP a ha).2.2⟩)
    (fun b hb => ⟨(hB b hb).1,(hB b hb).2.1⟩) n hn hrough
  apply (pow_le_pow_left₀ (_root_.norm_nonneg _) hh 2).trans
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left he (sq_nonneg _)

end CubicFirstMoment

end

end OAI
