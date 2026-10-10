import OAI.Probability.PosteriorReplicas.Kernels.KernelPi
import OAI.Probability.PosteriorReplicas.Kernels.ReplicaMeasure

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma measurable_tiltedFiber {d k : ℕ} (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : Data d k => tiltedFiber base f z.1 z.2) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have ht := measurable_tiltMass (d := d) (k := k) base hf
  have hm : Measurable (fun z : Data d k => (baseFiber base z.1 z.2).withDensity f s) := by
    simp only [withDensity_apply _ hs]
    simpa only [lintegral_indicator hs, baseKernel, Kernel.coe_mk] using
      (hf.indicator hs).lintegral_kernel (κ := baseKernel base)
  have he : (fun z : Data d k => tiltedFiber base f z.1 z.2 s) =
      fun z => if tiltMass base f z.1 z.2 = 0 then (Measure.dirac (0 : Vec d)) s
        else (tiltMass base f z.1 z.2)⁻¹ * (baseFiber base z.1 z.2).withDensity f s := by
    funext z
    unfold tiltedFiber
    split_ifs <;> simp [Measure.smul_apply]
  rw [he]
  exact Measurable.ite (measurableSet_eq_fun ht measurable_const) measurable_const (ht.inv.mul hm)

def posteriorKernel {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    Kernel (Data d k) (Vec d) where
  toFun z := tiltedFiber base f z.1 z.2
  measurable' := measurable_tiltedFiber base hf

lemma posteriorKernel_markov {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    IsMarkovKernel (@posteriorKernel d k base f hf) :=
  ⟨fun z => tiltedFiber_probability base hLt hfL z.1 z.2⟩

def dataLaw {d k : ℕ} (ν : Measure (Vec d)) : Measure (Data d k) :=
  ((gaussianRows d k).prod ν).map (fun z => (z.1,labels z.1 z.2))

instance {d k : ℕ} (ν : Measure (Vec d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (dataLaw (k := k) ν) := by
  unfold dataLaw
  infer_instance

lemma posterior_disintegration_lintegral {d k : ℕ} {A : Rows d k}
    (hA : LinearIndependent ℝ A) (hk : k < d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞)
    (hfL : ∀ x, f x ≤ L) {H : Labels k × Vec d → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ x, H (labels A x,x) ∂(base.measure d).withDensity f) =
      ∫⁻ y, projectedDensity base f A y *
        ∫⁻ x, H (y,x) ∂tiltedFiber base f A y := by
  rw [weighted_base_lintegral hA hk base hf (show Measurable (fun x => H (labels A x,x)) by
    unfold labels; fun_prop)]
  apply lintegral_congr
  intro y
  by_cases hb : baseDensity base A y = 0
  · simp [projectedDensity,hb]
  have he : (∫⁻ x, f x * H (labels A x,x) ∂baseFiber base A y) =
      ∫⁻ x, H (y,x) ∂(baseFiber base A y).withDensity f := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hf (show Measurable (fun x => H (y,x)) by fun_prop)]
    simp only [Pi.mul_apply]
    rw [baseFiber_eq_map,
      lintegral_map (show Measurable (fun x => f x * H (labels A x,x)) by unfold labels; fun_prop)
        (measurable_basePoint_fixed base A y),
      lintegral_map (show Measurable (fun x => f x * H (y,x)) by fun_prop)
        (measurable_basePoint_fixed base A y)]
    simp only [labels_basePoint hA]
  rw [he, ← tiltMass_smul_tiltedFiber base hf hLt hfL A y, lintegral_smul_measure]
  simp only [projectedDensity, smul_eq_mul, mul_assoc]

lemma dataLaw_density {d k : ℕ} (hd : 3 ≤ d) (hk : k < d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞)
    (hfL : ∀ x, f x ≤ L) :
    dataLaw (k := k) ((base.measure d).withDensity f) =
      ((gaussianRows d k).prod volume).withDensity (fun z => projectedDensity base f z.1 z.2) := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  apply Measure.ext_of_lintegral
  intro H hH
  rw [dataLaw, lintegral_map hH (by unfold labels; fun_prop), lintegral_prod _ (by unfold labels; fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_projectedDensity base hf) hH,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_gaussian_rows_full_rank hd hk] with A hA
  have h := posterior_disintegration_lintegral hA hk base hf hLt hfL
    (H := fun z : Labels k × Vec d => H (A,z.1)) (by fun_prop)
  have (y : Labels k) := tiltedFiber_probability base hLt hfL A y
  simpa using h

end PosteriorReplicas
end

end OAI
