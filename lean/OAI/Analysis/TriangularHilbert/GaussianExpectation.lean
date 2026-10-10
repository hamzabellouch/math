import OAI.Analysis.TriangularHilbert.JointHeat

namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
noncomputable section

lemma weight_three_integrable {h : ℝ} (hh : 0 < h) (a b c d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart 2 d z 0) (σ 0)*
      weight h b (chart 2 d z 1) (σ 1)*weight h c (chart 2 d z v) (σ v)) := by
  have hi := weight_pair_integrable h a b d σ hσ 0 2
  have he : (0:Three)+1=1 := by decide
  rw [he] at hi
  apply (hi.mul_const (h*density (σ v) 0)).mono'
  · have hc (k : Three) : Continuous (fun z : ℝ×ℝ => chart 2 d z k) :=
      (continuous_apply k).comp ((chart_continuous 2).comp (continuous_const.prodMk continuous_id))
    exact ((continuous_weight_param h a (hc 0) continuous_const (fun _ => hσ 0)).mul
      (continuous_weight_param h b (hc 1) continuous_const (fun _ => hσ 1)) |>.mul
      (continuous_weight_param h c (hc v) continuous_const (fun _ => hσ v))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg
      (weight_pos hh (hσ 0) _ _).le (weight_pos hh (hσ 1) _ _).le) (weight_pos hh (hσ v) _ _).le)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (density_le_zero (σ v) _) hh.le)
      (mul_nonneg (weight_pos hh (hσ 0) _ _).le (weight_pos hh (hσ 1) _ _).le)

lemma planeIntegral_weight_repeat_zero (h a b c d : ℝ) (σ : Three → ℝ)
    (hσ : ∀ w, 0 < σ w) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h c (p 0) (σ 0)) d =
      h^3*density (2*σ 0) (a-c) := by
  unfold planeIntegral
  change (∫ z : ℝ×ℝ, h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 0) (c-z.1)) ∂volume.prod volume) = _
  have he (z : ℝ×ℝ) : h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 0) (c-z.1)) =
      h^3*((density (σ 0) (a-z.1)*density (σ 0) (c-z.1))*density (σ 1) (b-z.2)) := by ring
  simp_rw [he]
  rw [integral_const_mul,integral_prod_mul (fun p => density (σ 0) (a-p)*density (σ 0) (c-p)) (fun q => density (σ 1) (b-q)),integral_density_product (hσ 0) (hσ 0),integral_sub_left_eq_self,integral_density (hσ 1),mul_one]
  congr 2
  ring

lemma planeIntegral_weight_repeat_one (h a b c d : ℝ) (σ : Three → ℝ)
    (hσ : ∀ w, 0 < σ w) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h c (p 1) (σ 1)) d =
      h^3*density (2*σ 1) (b-c) := by
  unfold planeIntegral
  change (∫ z : ℝ×ℝ, h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 1) (c-z.2)) ∂volume.prod volume) = _
  have he (z : ℝ×ℝ) : h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 1) (c-z.2)) =
      h^3*(density (σ 0) (a-z.1)*(density (σ 1) (b-z.2)*density (σ 1) (c-z.2))) := by ring
  simp_rw [he]
  rw [integral_const_mul,integral_prod_mul (fun p => density (σ 0) (a-p)) (fun q => density (σ 1) (b-q)*density (σ 1) (c-q)),integral_density_product (hσ 1) (hσ 1),integral_sub_left_eq_self,integral_density (hσ 0),one_mul]
  congr 2
  ring
end
end TriangularHilbert.Heat
end

end OAI
