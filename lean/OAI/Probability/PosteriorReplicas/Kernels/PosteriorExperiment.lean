import OAI.Probability.PosteriorReplicas.Information.ReplicaMeasureInformation
import OAI.Probability.PosteriorReplicas.Kernels.PosteriorKernel

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma replicaLaw_eq_dataKernel {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    replicaLaw (k := k) (m := m) base f =
      (dataLaw (k := k) ((base.measure d).withDensity f) ⊗ₘ
        piKernel (fun _ : Fin (m+1) => posteriorKernel base hf)).map
        (fun z => (z.1.1,z.1.2,z.2)) := by
  let : NeZero d := ⟨by omega⟩
  let := bounded_withDensity_finite (base.measure d) hLt hfL
  let := posteriorKernel_markov (k := k) base hf hLt hfL
  let : IsFiniteMeasure (dataLaw (k := k) ((base.measure d).withDensity f)) := by
    unfold dataLaw
    infer_instance
  apply Measure.ext_of_lintegral
  intro H hH
  rw [replicaLaw_lintegral hd hk hm base hf hLt hfL hH,
    lintegral_map hH (by fun_prop), Measure.lintegral_compProd (by fun_prop),
    dataLaw_density (by omega) (by omega) base hf hLt hfL,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_projectedDensity base hf) (by fun_prop),
    lintegral_prod _ (by fun_prop)]
  simp only [Pi.mul_apply]
  simp_rw [piKernel_apply]
  rfl

lemma dataSignal_lintegral {d k : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : Data d k × Vec d → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ z, ∫⁻ x, H (z,x) ∂posteriorKernel base hf z
      ∂dataLaw (k := k) ((base.measure d).withDensity f)) =
      ∫⁻ A, ∫⁻ x, H ((A,labels A x),x) ∂(base.measure d).withDensity f ∂gaussianRows d k := by
  let : NeZero d := ⟨by omega⟩
  let := bounded_withDensity_finite (base.measure d) hLt hfL
  let := posteriorKernel_markov (k := k) base hf hLt hfL
  rw [dataLaw_density hd hk base hf hLt hfL,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_projectedDensity base hf) (by fun_prop),
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_gaussian_rows_full_rank hd hk] with A hA
  exact (posterior_disintegration_lintegral hA hk base hf hLt hfL
    (H := fun z => H ((A,z.1),z.2)) (by fun_prop)).symm

def posteriorMessageLaw {d k m N : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    (κ : Kernel (Data d k) (Fin N)) : Measure (Tuple d m × Fin N) :=
  (dataLaw (k := k) ((base.measure d).withDensity f) ⊗ₘ
    (piKernel (fun _ : Fin (m+1) => posteriorKernel base hf) ×ₖ κ)).snd

lemma posteriorMessageLaw_probability {d k m N : ℕ} (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    IsProbabilityMeasure (posteriorMessageLaw (m := m) base hf κ) := by
  let := posteriorKernel_markov (k := k) base hf hLt hfL
  unfold posteriorMessageLaw
  infer_instance

lemma posteriorMessageLaw_coordinate {d k m N : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] (i : Fin (m+1)) :
    (posteriorMessageLaw (m := m) base hf κ).map (fun z => (z.1 i,z.2)) =
      signalMessageLaw ((base.measure d).withDensity f) κ := by
  let := posteriorKernel_markov (k := k) base hf hLt hfL
  have (z : Data d k) := tiltedFiber_probability base hLt hfL z.1 z.2
  apply Measure.ext_of_lintegral
  intro H hH
  rw [posteriorMessageLaw, Measure.snd, Measure.map_map (by fun_prop) measurable_snd,
    lintegral_map hH (by fun_prop), Measure.lintegral_compProd (by fun_prop)]
  simp only [Kernel.prod_apply, piKernel_apply]
  have hp (z : Data d k) :
      (∫⁻ uw, H (uw.1 i,uw.2) ∂(Measure.pi (fun _ : Fin (m+1) => posteriorKernel base hf z)).prod (κ z)) =
      ∫⁻ x, ∫⁻ w, H (x,w) ∂κ z ∂posteriorKernel base hf z := by
    rw [lintegral_prod _ (by fun_prop)]
    exact (measurePreserving_eval (fun _ : Fin (m+1) => posteriorKernel base hf z) i).lintegral_comp
      (show Measurable (fun x : Vec d => ∫⁻ w, H (x,w) ∂κ z) by fun_prop)
  change (∫⁻ z, ∫⁻ uw, H (uw.1 i,uw.2)
    ∂(Measure.pi (fun _ : Fin (m+1) => posteriorKernel base hf z)).prod (κ z)
    ∂dataLaw ((base.measure d).withDensity f)) = _
  simp_rw [hp]
  have hK : Measurable (fun z : Data d k × Vec d => ∫⁻ w, H (z.2,w) ∂κ z.1) := by
    exact (hH.comp (show Measurable (fun z : (Data d k × Vec d) × Fin N => (z.1.2,z.2)) by fun_prop)).lintegral_kernel_prod_right'
      (κ := κ.comap Prod.fst measurable_fst)
  rw [dataSignal_lintegral hd hk base hf hLt hfL hK]
  rw [signalMessageLaw, lintegral_map hH (by fun_prop), Measure.lintegral_compProd (by fun_prop)]
  have hK' : Measurable (fun a : Vec d × Rows d k => ∫⁻ w, H (a.1,w) ∂messageKernel κ a) := by
    exact (hH.comp (show Measurable (fun z : (Vec d × Rows d k) × Fin N => (z.1.1,z.2)) by fun_prop)).lintegral_kernel_prod_right'
      (κ := messageKernel κ)
  rw [lintegral_prod _ (show AEMeasurable (fun a : Vec d × Rows d k =>
    ∫⁻ w, H (a.1,w) ∂messageKernel κ a) _ from hK'.aemeasurable)]
  simp only [messageKernel, Kernel.comap_apply]
  exact lintegral_lintegral_swap
    ((hK.comp (show Measurable (fun z : Rows d k × Vec d => ((z.1,labels z.1 z.2),z.2)) by
      unfold labels; fun_prop)).aemeasurable)

lemma posteriorMessageLaw_tuple {d k m N : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    (posteriorMessageLaw (m := m) base hf κ).fst = (replicaLaw (k := k) (m := m) base f).map (fun z => z.2.2) := by
  let := posteriorKernel_markov (k := k) base hf hLt hfL
  let := posteriorMessageLaw_probability (m := m) base hf hLt hfL κ
  rw [replicaLaw_eq_dataKernel hd hk hm base hf hLt hfL,
    Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.ext_of_lintegral
  intro H hH
  rw [posteriorMessageLaw, Measure.fst, Measure.snd,
    Measure.map_map measurable_fst measurable_snd,
    lintegral_map hH (by fun_prop), lintegral_map hH (by fun_prop),
    Measure.lintegral_compProd (by fun_prop), Measure.lintegral_compProd (by fun_prop)]
  apply lintegral_congr
  intro z
  rw [Kernel.prod_apply, lintegral_prod _ (by fun_prop)]
  simp

end PosteriorReplicas
end

end OAI
