import OAI.Analysis.TriangularHilbert.MassPlane

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_triple_integrable {s t v : ℝ} (hs : 0 < s) (ht : 0 < t) (hv : 0 < v) (a b c : ℝ) :
    Integrable (fun z : ℝ×ℝ => density s (a-z.1)*density t (b-z.2)*density v (c+z.1+z.2)) := by
  have hst : Integrable (fun z : ℝ×ℝ => density s (a-z.1)*density t (b-z.2)) := by
    exact ((volume.measurePreserving_sub_left a).integrable_comp_of_integrable (density_integrable hs.le)).mul_prod
      ((volume.measurePreserving_sub_left b).integrable_comp_of_integrable (density_integrable ht.le))
  apply (hst.mul_const (density v 0)).mono'
  · have hc : Continuous (fun z : ℝ×ℝ => density s (a-z.1)*density t (b-z.2)*density v (c+z.1+z.2)) :=
      (((continuous_density s).comp (continuous_const.sub continuous_fst)).mul
        ((continuous_density t).comp (continuous_const.sub continuous_snd))).mul
          ((continuous_density v).comp ((continuous_const.add continuous_fst).add continuous_snd))
    exact hc.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (density_nonneg hs.le _) (density_nonneg ht.le _)) (density_nonneg hv.le _))]
    exact mul_le_mul_of_nonneg_left (density_le_zero v _) (mul_nonneg (density_nonneg hs.le _) (density_nonneg ht.le _))

lemma integral_density_triple {s t v : ℝ} (hs : 0 < s) (ht : 0 < t) (hv : 0 < v) (a b c : ℝ) :
    (∫ z : ℝ×ℝ, density s (a-z.1)*density t (b-z.2)*density v (c+z.1+z.2)) =
      density (s+t+v) (a+b+c) := by
  rw [MeasureTheory.Measure.volume_eq_prod,integral_prod _ (density_triple_integrable hs ht hv a b c)]
  have inner (p : ℝ) : (∫ q, density s (a-p)*density t (b-q)*density v (c+p+q)) =
      density s (a-p)*density (t+v) (b+c+p) := by
    have he (q : ℝ) : density v (c+p+q) = density v ((-c-p)-q) := by
      rw [show (-c-p)-q = -(c+p+q) by ring,density_neg]
    simp_rw [he,mul_assoc]
    rw [integral_const_mul,integral_density_product ht hv]
    congr 2
    ring
  simp_rw [inner]
  have he (p : ℝ) : density (t+v) (b+c+p) = density (t+v) ((-b-c)-p) := by
    rw [show (-b-c)-p = -(b+c+p) by ring,density_neg]
  simp_rw [he]
  rw [integral_density_product hs (add_pos ht hv)]
  congr 1 <;> ring

lemma planeIntegral_weight_triple (h a b c : ℝ) (σ : MatrixEnergy.Three → ℝ)
    (hσ : ∀ w, 0 < σ w) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h c (p 2) (σ 2)) 0 =
      h^3*density (σ 0+σ 1+σ 2) (a+b+c) := by
  unfold planeIntegral
  change (∫ z : ℝ×ℝ, h*density (σ 0) (a-z.1) * (h*density (σ 1) (b-z.2)) *
      (h*density (σ 2) (c-(0-z.1-z.2)))) = _
  have he (z : ℝ×ℝ) : h*density (σ 0) (a-z.1) * (h*density (σ 1) (b-z.2)) *
      (h*density (σ 2) (c-(0-z.1-z.2))) =
      h^3*(density (σ 0) (a-z.1)*density (σ 1) (b-z.2)*density (σ 2) (c+z.1+z.2)) := by
    rw [show c-(0-z.1-z.2) = c+z.1+z.2 by ring]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_density_triple (hσ 0) (hσ 1) (hσ 2)]
end
end TriangularHilbert.Heat
end

end OAI
