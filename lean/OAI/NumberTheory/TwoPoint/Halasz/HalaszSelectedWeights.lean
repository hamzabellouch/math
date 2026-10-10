import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogWeightCost

namespace OAI

/-! Only the selected middle degrees need nontrivial cancellation. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_log_weight_cost_trivial (k r : ℕ) : 2*(r:ℝ)+1≤halaszLogWeightCost k r := by
  have hp : (8:ℝ)^2≤(8:ℝ)^(k+2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hmul := mul_le_mul_of_nonneg_right hp (show (0:ℝ)≤r+k+1 by positivity)
  unfold halaszLogWeightCost
  norm_num at hmul
  nlinarith [show (0:ℝ)≤k by positivity]

lemma halasz_selected_weight_product {k r M : ℕ} (γ : Fin k → ℝ)
    (S : Finset (Fin k)) {C N η : ℝ} (hN : 0<N)
    (htriv : ∀ j,halaszNormalizedWeight r M γ j≤C)
    (hsel : ∀ j∈S,halaszNormalizedWeight r M γ j≤C*N^(-η)) :
    (∏ j : Fin k,halaszNormalizedWeight r M γ j)≤C^k*N^(-(S.card:ℝ)*η) := by
  let w : Fin k → ℝ := fun j => if j∈S then η else 0
  have hw : ∀ j,halaszNormalizedWeight r M γ j≤C*N^(-w j) := by
    intro j
    by_cases hj : j∈S
    · simpa only [w,ite_eq_left hj] using hsel j hj
    · simpa only [w,ite_eq_right hj,neg_zero,Real.rpow_zero,mul_one] using htriv j
  have hs : (∑ j,w j)=(S.card:ℝ)*η := by
    simp [w]
  calc
    _ ≤ ∏ j,C*N^(-w j) :=
      prod_le_prod₀ (fun j _ => halasz_normalized_weight_nonneg γ j) (fun j _ => hw j)
    _ = _ := by
      rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,
        ← Real.rpow_sum_of_pos hN,sum_neg_distrib,hs]
      congr 2
      ring

theorem halasz_log_selected_weight_product {k r M : ℕ} (hr : 1≤r) (hM : 1≤M)
    {t z N α lam η : ℝ} (hN : 1≤N) (hz : N≤z) (hzhi : z≤2*N)
    (ht : |t|=N^lam) (hscale : N^α≤2*(M:ℝ)) (S : Finset (Fin k))
    (h₁ : ∀ j∈S,η≤α*(j.val+1)) (h₂ : ∀ j∈S,η≤(j.val+1)-lam)
    (h₃ : ∀ j∈S,η≤lam-(j.val+1)+2*α*(j.val+1)) :
    (∏ j : Fin k,halaszNormalizedWeight r M (halaszLogCoefficient t z) j)≤
      (halaszLogWeightCost k r)^k*N^(-(S.card:ℝ)*η) := by
  apply halasz_selected_weight_product _ S (by linarith : 0<N)
  · intro j
    exact (min_le_left _ _).trans (halasz_log_weight_cost_trivial k r)
  · intro j hj
    exact halasz_log_coordinate_saving hr hM hN hz hzhi ht hscale j
      (h₁ j hj) (h₂ j hj) (h₃ j hj)

end TwoPointCorrelations

end OAI
