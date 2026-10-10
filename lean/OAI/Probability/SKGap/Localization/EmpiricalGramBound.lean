import Mathlib
import OAI.Probability.SKGap.Entropy.WeightedMomentComparison
import OAI.Probability.SKGap.Gaussian.ScalarMomentGram
import OAI.Probability.SKGap.Gaussian.ConditionalGramTail
import OAI.Probability.SKGap.Localization.GramUniformRobust

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

lemma gramCoordinates_bound {d s L : ℝ} (hs : 0 < s) (hL : 1 ≤ L)
    (hd : (1+|d|)/s ≤ L) (y : ℝ) (r : Fin 3) :
    |gramCoordinates d s y r| ≤ L*(1+|y|) := by
  have hLy : L ≤ L*(1+|y|) := by nlinarith [mul_nonneg (by linarith : 0 ≤ L) (abs_nonneg y)]
  fin_cases r
  · simpa [gramCoordinates] using hL.trans hLy
  · simpa [gramCoordinates] using (abs_tanh_lt_one y).le.trans (hL.trans hLy)
  · simp only [gramCoordinates,Matrix.cons_val,Fin.reduceFinMk,abs_div,abs_of_pos hs]
    apply (div_le_div_of_nonneg_right (abs_sub y d) hs.le).trans
    calc
      _ ≤ ((1+|d|)/s)*(1+|y|) := by
        rw [div_mul_eq_mul_div,div_le_div_iff_of_pos_right hs]
        nlinarith [mul_nonneg (abs_nonneg d) (abs_nonneg y)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hd (by positivity)

lemma gramCoordinates_product_bound {d s L : ℝ} (hs : 0 < s) (hL : 1 ≤ L)
    (hd : (1+|d|)/s ≤ L) (y : ℝ) (r k : Fin 3) :
    |gramCoordinates d s y r*gramCoordinates d s y k| ≤ 2*L^2*(1+y^2) := by
  rw [abs_mul]
  have hp := mul_le_mul (gramCoordinates_bound hs hL hd y r)
    (gramCoordinates_bound hs hL hd y k) (abs_nonneg _) (by positivity : 0 ≤ L*(1+|y|))
  have hx : (1+|y|)^2 ≤ 2*(1+y^2) := by nlinarith [sq_nonneg (|y|-1),sq_abs y]
  nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg L)]

def empiricalGramColumns {n : ℕ} (y : Fin n → ℝ) (d s : ℝ) :
    Fin 3 → EuclideanSpace ℝ (Fin n) := fun r => WithLp.toLp 2 (fun i => gramCoordinates d s (y i) r/√(n:ℝ))

lemma diagonal_empirical_gram_entry {n : ℕ} (hn : 0 < n) (a y : Fin n → ℝ) (d s : ℝ) (r k : Fin 3) :
    matrixPair (diagonal a) (empiricalGramColumns y d s r).ofLp
      (empiricalGramColumns y d s k).ofLp=
      (n:ℝ)⁻¹*∑ i,a i*gramCoordinates d s (y i) r*gramCoordinates d s (y i) k := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  simp only [matrixPair,Matrix.mulVec_diagonal,empiricalGramColumns,WithLp.ofLp_toLp,dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hn0 : √(n:ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
  field_simp
  rw [Real.sq_sqrt hnR.le]
  ring

theorem empirical_augmented_gram_comparison {n : ℕ} [NeZero n]
    (a y : Fin n → ℝ) {d s L D R ε ν : ℝ} (hs : 0 < s) (hL : 1 ≤ L)
    (hd : (1+|d|)/s ≤ L) (hD : 0 ≤ D) (hR : 1 ≤ R) (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (ha : ∀ i,|a i-(1-tanh (y i)^2)| ≤ D)
    (hclose : ∑ i,(a i-(1-tanh (y i)^2))^2 ≤ ε^2*(n:ℝ))
    (htail : (∑ i,if R < |y i| then y i^2 else 0) ≤ ν*(n:ℝ)) :
    ‖diagonalAugmentedGram a (empiricalGramColumns y d s)-
      augmentedGram (ν := Unit) (scalarMomentGram (empiricalLaw y) d s)‖ ≤
      4*(2*L^2*(1+R^2)*ε+4*L^2*D*ν) := by
  have hn : 0 < n := NeZero.pos n
  have he (r k : Fin 3) : |matrixPair (diagonal a) (empiricalGramColumns y d s r).ofLp
      (empiricalGramColumns y d s k).ofLp-scalarMomentGram (empiricalLaw y) d s r k| ≤
      2*L^2*(1+R^2)*ε+4*L^2*D*ν := by
    rw [diagonal_empirical_gram_entry hn,scalarMomentGram_empirical]
    have hsmall (i : Fin n) (hi : |y i| ≤ R) :
        |gramCoordinates d s (y i) r*gramCoordinates d s (y i) k| ≤ 2*L^2*(1+R^2) := by
      apply (gramCoordinates_product_bound hs hL hd (y i) r k).trans
      have hy : y i^2 ≤ R^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (y i)) (by linarith : 0 ≤ R)).mpr hi
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hb := normalized_weighted_moment_comparison hn a (fun i=>1-tanh (y i)^2) y
      (fun i=>gramCoordinates d s (y i) r*gramCoordinates d s (y i) k)
      (H := 2*L^2*(1+R^2)) (C := 2*L^2) (D := D) (R := R) (by positivity)
      (by positivity) hD hR hε ha hsmall (fun i=>gramCoordinates_product_bound hs hL hd (y i) r k)
      hclose htail
    have hid : (n:ℝ)⁻¹*(∑ i,a i*gramCoordinates d s (y i) r*gramCoordinates d s (y i) k)-
        (n:ℝ)⁻¹*(∑ i,(1-tanh (y i)^2)*gramCoordinates d s (y i) r*gramCoordinates d s (y i) k)=
        (∑ i,(a i-(1-tanh (y i)^2))*(gramCoordinates d s (y i) r*gramCoordinates d s (y i) k))/(n:ℝ) := by
      rw [← mul_sub,← Finset.sum_sub_distrib,div_eq_mul_inv,mul_comm _ (n:ℝ)⁻¹]
      congr 1
      apply Finset.sum_congr rfl
      intro i _;ring
    rw [hid]
    convert hb using 1; ring
  have hb0 : 0 ≤ 2*L^2*(1+R^2)*ε+4*L^2*D*ν := by positivity
  have hb := frobenius_le_card_bound (M := diagonalAugmentedGram a (empiricalGramColumns y d s)-
    augmentedGram (ν := Unit) (scalarMomentGram (empiricalLaw y) d s))
    (ε := 2*L^2*(1+R^2)*ε+4*L^2*D*ν) (by positivity) (by
      intro r k
      cases r with
      | inl r => cases k with
        | inl k => exact he r k
        | inr k => change |(0:ℝ)-0| ≤ _; simpa only [sub_zero,abs_zero] using hb0
      | inr r => cases k with
        | inl k => change |(0:ℝ)-0| ≤ _; simpa only [sub_zero,abs_zero] using hb0
        | inr k => change |(1:ℝ)-1| ≤ _; simpa only [sub_self,abs_zero] using hb0)
  simpa using hb
end SKGap
end
end

end OAI
