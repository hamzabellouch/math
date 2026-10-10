import Mathlib
import OAI.Probability.SKRatio.Gaussian.PlantedEmpirical
import OAI.Probability.SKRatio.Quantization.BinStability

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression Bins
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma augmentedAverage_gaussian (β : ℝ) :
    HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ =>
      (∑ i, augmentedField β g i)/(n:ℝ)) (standardArrayLaw (Fin n × Fin n)) := by
  simpa only [smul_apply,ContinuousLinearMap.id_apply,
    smul_eq_mul,inv_mul_eq_div] using
    (augmentedField_gaussian (n := n) β).fun_sum.map_fun
      ((n:ℝ)⁻¹ • ContinuousLinearMap.id ℝ ℝ)

lemma augmentedAverage_hasLaw (hn : 0<n) (β : ℝ) :
    HasLaw (fun g : (Fin n × Fin n) → ℝ => (∑ i, augmentedField β g i)/(n:ℝ))
      (gaussianReal (β^2) (Real.toNNReal (2*β^2/(n:ℝ))))
      (standardArrayLaw (Fin n × Fin n)) := by
  have hg := augmentedAverage_gaussian (n := n) β
  have hLp (i : Fin n) := ((augmentedField_gaussian β).eval i).memLp_two
  have hmean : (∫ g, (∑ i, augmentedField β g i)/(n:ℝ)
      ∂standardArrayLaw (Fin n × Fin n))=β^2 := by
    rw [integral_div,integral_finsetSum _ (fun i _ => ((augmentedField_gaussian β).eval i).integrable)]
    simp only [augmentedField_mean hn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hvar : Var[(fun g => (∑ i, augmentedField β g i)/(n:ℝ));
      standardArrayLaw (Fin n × Fin n)] = 2*β^2/(n:ℝ) := by
    rw [←covariance_self hg.aemeasurable,covariance_fun_div_left,covariance_fun_div_right,
      covariance_fun_sum_fun_sum hLp hLp]
    simp only [augmentedField_covariance hn,Finset.sum_add_distrib,Finset.sum_ite_eq,
      Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
    ring
  exact ⟨hg.aemeasurable,by rw [hg.map_eq_gaussianReal,hmean,hvar]⟩

theorem augmentedField_firstMoment (β : ℝ) (hβ : 0<β) :
    ExponentialConvergence (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n g => (∑ i, augmentedField β g i)/(n:ℝ)) (β^2) := by
  intro ε hε
  refine ⟨2,ε^2/(4*β^2),by norm_num,by positivity,?_⟩
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hc : HasLaw (fun g : (Fin n × Fin n) → ℝ =>
      (∑ i, augmentedField β g i)/(n:ℝ)-β^2)
      (gaussianReal 0 (Real.toNNReal (2*β^2/(n:ℝ))))
      (standardArrayLaw (Fin n × Fin n)) := by
    have h := gaussianReal_add_const (augmentedAverage_hasLaw hn β) (-(β^2 : ℝ))
    rw [add_neg_cancel] at h
    simpa only [sub_eq_add_neg] using h
  have ht := subgaussian_abs_tail (gaussian_hasSubgaussianMGF hc) ε hε.le
  rw [Real.coe_toNNReal _ (by positivity : 0≤2*β^2/(n:ℝ))] at ht
  have he : -ε^2/(2*(2*β^2/(n:ℝ)))=-(ε^2/(4*β^2))*(n:ℝ) := by field_simp; ring
  rw [he,←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by norm_num)] at ht
  exact ht

lemma siteNorm_eq_sqrt (H : Fin n → ℝ) :
    siteNorm H = sqrt ((∑ i, H i^2)/(n:ℝ)) := by
  rw [←siteNorm_sq,sqrt_sq (siteNorm_nonneg H)]

lemma augmentedField_siteNorm (β : ℝ) (hβ : 0<β) :
    ExponentialConvergence (fun n => standardArrayLaw (Fin n × Fin n))
      (fun _ g => siteNorm (augmentedField β g)) (sqrt (β^2+β^4)) := by
  simpa only [siteNorm_eq_sqrt] using
    (augmentedField_secondMoment β hβ).continuous_map continuous_sqrt.continuousAt

end SKRatio.Planted

end

end OAI
