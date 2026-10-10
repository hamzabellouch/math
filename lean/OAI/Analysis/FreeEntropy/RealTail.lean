import OAI.Analysis.FreeEntropy.EntropyReal

namespace OAI

noncomputable section
open MeasureTheory Set Filter
namespace FiniteEntropySeparation
 theorem integrableOn_Ioi_translate {f : ℝ → ℝ} (a : ℝ) :
    IntegrableOn (fun s => f (a+s)) (Ioi 0) ↔ IntegrableOn f (Ioi a) := by
  have he : (fun s : ℝ => a+s) ⁻¹' Ioi a = Ioi 0 := by ext s; simp
  simpa only [he, Function.comp_def] using
    (measurePreserving_add_left volume a).integrableOn_comp_preimage (measurableEmbedding_addLeft a)
      (f := f) (s := Ioi a)
 theorem integral_Ioi_translate (f : ℝ → ℝ) (a : ℝ) :
    (∫ s in Ioi (0 : ℝ), f (a+s)) = ∫ u in Ioi a, f u := by
  have he : (fun s : ℝ => a+s) ⁻¹' Ioi a = Ioi 0 := by ext s; simp
  simpa only [he] using (measurePreserving_add_left volume a).setIntegral_preimage_emb
    (measurableEmbedding_addLeft a) f (Ioi a)
 theorem inverseFourth_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => 1/u^4) (Ioi a) := by
  apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) ha).congr_fun _ measurableSet_Ioi
  intro u hu
  norm_num
 theorem inverseFourth_integral {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioi a, 1/u^4) = 1/(3*a^3) := by
  have he : (∫ u in Ioi a, 1/u^4) = ∫ u in Ioi a, u^(-4 : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    norm_num
  rw [he, integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) ha]
  norm_num
  ring
end FiniteEntropySeparation

end

end OAI
