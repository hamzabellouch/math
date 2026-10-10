import OAI.Geometry.Perimeter.Regularity.EllipticIteration
import OAI.Geometry.Perimeter.Regularity.EllipticGradientLimit

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem linear_pointwise_iteration {θ δ K a B H R : ℝ}
    (hθ : 0<θ) (hθ1 : θ<1) (hK : 1≤K)
    (hc : LinearContractionProperty n θ δ K)
    (ha : 0≤a) (hB : 0≤B) (hH : 0≤H) (hR : 0<R)
    (hsmall : 32*K^2*a≤1) (hforce : 16*K*B≤H)
    {A : Euc n → Euc n →L[ℝ] Euc n} (hA : Continuous A)
    {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f) {F : Euc n → Euc n} (hF : Continuous F)
    (p : Euc n) (h : WeakLinearEquation A f F (Metric.ball p R))
    (hnear : ∀ x∈Metric.ball p R, ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖≤δ)
    (hosc : ∀ j x, x∈Metric.ball p (θ^j*R) →
      ‖A p-A x‖≤a*(1/2)^j ∧ ‖F x-F p‖≤B*(1/2)^j)
    (hinit : scaledGradientEnergy f p R 0≤H^2) :
    ∃ q : ℕ → Euc n, (∀ j, ‖q j-gradient f p‖≤2*K*H*(1/2)^j) ∧
      (∀ j, scaledGradientEnergy f p (θ^j*R) (q j)≤H^2*((1/2)^j)^2) ∧
      ‖gradient f p‖≤2*K*H := by
  obtain ⟨q,hq0,hqb,hqE,hqinc⟩ := linear_energy_iteration hθ hθ1 hK hc ha hB hH hR
    hsmall hforce hA hf hF p h hnear hosc hinit
  have hdist (j : ℕ) : dist (q j) (q (j+1))≤(K*H)*(1/2:ℝ)^j := by
    rw [dist_eq_norm,norm_sub_rev]; exact hqinc j
  obtain ⟨w,hw⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1/2) (K*H) (by norm_num) hdist)
  have hwf : gradient f p=w := gradient_eq_of_scaled_energy hf p
    (fun j ↦ by positivity)
    (by simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1).mul_const R)
    (by simpa only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).pow 2).const_mul (H^2))
    hw hqE
  have herror (j : ℕ) : ‖q j-gradient f p‖≤2*K*H*(1/2)^j := by
    have hh := dist_le_of_le_geometric_of_tendsto (1/2) (K*H) (by norm_num) hdist hw j
    rw [dist_eq_norm,←hwf] at hh
    convert hh using 1
    ring
  refine ⟨q,herror,hqE,?_⟩
  have hh := herror 0
  simpa only [hq0,zero_sub,norm_neg,pow_zero,mul_one] using hh

end RPISingularHarnack

end

end OAI
