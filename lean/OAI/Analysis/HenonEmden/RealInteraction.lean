import OAI.Analysis.HenonEmden.FarLocalization

namespace OAI

section RealInteraction

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden

lemma interaction_density_finite {n : ℕ} (f g : Space n → ℝ) :
    ∀ᵐ z : Space n × Space n ∂volume.prod volume,
      ENNReal.ofReal (f z.1)*ENNReal.ofReal (g z.2)*ENNReal.ofReal (newtonKernel n z) < ⊤ := by
  exact ae_of_all _ fun z => ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top

lemma integrable_interaction_iff {n : ℕ} (hn : 3 ≤ n) {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (F : Space n × Space n → ℝ) :
    Integrable F (interaction f g) ↔ Integrable (fun z => f z.1*g z.2*newtonKernel n z*F z) (volume.prod volume) := by
  rw [interaction,integrable_withDensity_iff_integrable_smul' (by fun_prop) (interaction_density_finite f g)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hf0 _),ENNReal.toReal_ofReal (hg0 _),
    ENNReal.toReal_ofReal (newtonKernel_nonneg hn _),smul_eq_mul]

lemma integral_interaction {n : ℕ} (hn : 3 ≤ n) {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (F : Space n × Space n → ℝ) :
    (∫ z, F z ∂interaction f g) = ∫ z, f z.1*g z.2*newtonKernel n z*F z ∂volume.prod volume := by
  rw [interaction,integral_withDensity_eq_integral_toReal_smul (by fun_prop) (interaction_density_finite f g)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hf0 _),ENNReal.toReal_ofReal (hg0 _),
    ENNReal.toReal_ofReal (newtonKernel_nonneg hn _),smul_eq_mul]

lemma interaction_ae_ne {n : ℕ} (hn : 1 ≤ n) (f g : Space n → ℝ) :
    ∀ᵐ z : Space n × Space n ∂interaction f g, z.1 ≠ z.2 := by
  have : Nontrivial (Space n) := (Module.finrank_pos_iff (R := ℝ)).mp (by simp; omega)
  apply ae_iff.mpr
  apply withDensity_absolutelyContinuous (volume.prod volume) _
  apply ae_iff.mp
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  exact ae_of_all _ fun x => ae_iff.mpr (by simp)

end HenonLaneEmden
end
end RealInteraction

end OAI
