import OAI.Probability.PosteriorReplicas.Kernels.PosteriorExperiment

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma signalMessageLaw_fst {d k N : ℕ} (p : Measure (Vec d)) [IsProbabilityMeasure p]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] : (signalMessageLaw p κ).fst = p := by
  rw [signalMessageLaw,Measure.fst,Measure.map_map measurable_fst (by fun_prop)]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop),Measure.lintegral_compProd (by fun_prop)]
  simp only [Function.comp_def,lintegral_const,measure_univ,mul_one]
  rw [lintegral_prod _ (by fun_prop)]
  simp

lemma posteriorMessageLaw_message {d k m N : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    (posteriorMessageLaw (m := m) base hf κ).snd = (signalMessageLaw ((base.measure d).withDensity f) κ).snd := by
  rw [← posteriorMessageLaw_coordinate hd hk base hf hLt hfL κ (0 : Fin (m+1)),
    Measure.snd,Measure.snd,Measure.map_map measurable_snd (by fun_prop)]
  rfl

lemma posteriorMessageLaw_coordinateMarginal {d k m N : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] (i : Fin (m+1)) :
    coordinateMarginal (posteriorMessageLaw (m := m) base hf κ).fst i =
      (base.measure d).withDensity f := by
  rw [← signalMessageLaw_fst ((base.measure d).withDensity f) κ,
    ← posteriorMessageLaw_coordinate hd hk base hf hLt hfL κ i]
  rw [coordinateMarginal,Measure.fst,Measure.map_map (measurable_pi_apply i) measurable_fst,
    Measure.fst,Measure.map_map measurable_fst (by fun_prop)]
  rfl

lemma posteriorMessageLaw_marginalProduct {d k m N : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    marginalProduct (posteriorMessageLaw (m := m) base hf κ).fst =
      Measure.pi (fun _ : Fin (m+1) => (base.measure d).withDensity f) := by
  unfold marginalProduct
  congr 1
  funext i
  exact posteriorMessageLaw_coordinateMarginal hd hk base hf hLt hfL κ i

end PosteriorReplicas
end

end OAI
