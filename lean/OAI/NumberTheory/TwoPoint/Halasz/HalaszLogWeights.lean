import OAI.NumberTheory.TwoPoint.Halasz.HalaszNormalizedDoubleMoment
import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogCoefficients

namespace OAI

/-! The three competing degree weights for the logarithmic phase. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_log_weight_identity {k r M : ℕ} (hr : 1≤r) (hM : 1≤M)
    {t z : ℝ} (ht : t≠0) (hz : 0<z) (j : Fin k) :
    halaszNormalizedWeight r M (halaszLogCoefficient t z) j =
      min (2*(r:ℝ)+1)
        ((5/2:ℝ)/(M:ℝ)^(j.val+1)+
          (r:ℝ)*|t|/(Real.pi*(j.val+1)*z^(j.val+1))+
          Real.pi*(j.val+1)*z^(j.val+1)/
            ((r:ℝ)*((M:ℝ)^(j.val+1))^2*|t|)) := by
  have hr0 : (r:ℝ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have hM0 : (M:ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
  have hj0 : (j.val:ℝ)+1≠0 := by positivity
  have ht0 : |t|≠0 := abs_ne_zero.mpr ht
  unfold halaszNormalizedWeight
  rw [halasz_log_coefficient_abs,abs_of_pos hz]
  congr 1
  field_simp [hr0,hM0,hj0,ht0,hz.ne',Real.pi_ne_zero]

lemma halasz_normalized_weight_product {k r M : ℕ} (γ : Fin k → ℝ)
    {C : ℝ} (w : Fin k → ℝ)
    (hw : ∀ j,halaszNormalizedWeight r M γ j≤C*(M:ℝ)^(-w j))
    (hM : 0<M) :
    (∏ j,halaszNormalizedWeight r M γ j)≤C^k*(M:ℝ)^(-(∑ j,w j)) := by
  have hM0 : 0<(M:ℝ) := by exact_mod_cast hM
  calc
    _ ≤ ∏ j,C*(M:ℝ)^(-w j) :=
      prod_le_prod₀ (fun j _ => halasz_normalized_weight_nonneg γ j) (fun j _ => hw j)
    _ = C^k*(M:ℝ)^(-(∑ j,w j)) := by
      rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,
        ← Real.rpow_sum_of_pos hM0, sum_neg_distrib]

end TwoPointCorrelations

end OAI
