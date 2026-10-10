import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

theorem condExp_mul_of_condIndepFun {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f g : Ω → ℝ}
    (hind : CondIndepFun m hm f g μ) (hf : Measurable[mΩ] f) (hg : Measurable[mΩ] g)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfgi : Integrable (fun ω => f ω * g ω) μ) :
    μ[(fun ω => f ω * g ω) | m] =ᵐ[μ] fun ω => μ[f | m] ω * μ[g | m] ω := by
  let : MeasurableSpace Ω := mΩ
  have hmap := ae_of_ae_trim (μ := μ) hm
    ((condIndepFun_iff_map_prod_eq_prod_map_map (mΩ := mΩ) (m' := m)
      (hm' := hm) (μ := μ) hf hg).mp hind)
  filter_upwards [condExp_ae_eq_integral_condExpKernel (mΩ := mΩ) (μ := μ) hm hfgi,
    condExp_ae_eq_integral_condExpKernel (mΩ := mΩ) (μ := μ) hm hfi,
    condExp_ae_eq_integral_condExpKernel (mΩ := mΩ) (μ := μ) hm hgi, hmap] with ω hfg hfω hgω hmapω
  rw [hfg, hfω, hgω]
  have hmap' : Measure.map (fun y => (f y, g y)) (condExpKernel μ m ω) =
      (Measure.map f (condExpKernel μ m ω)).prod (Measure.map g (condExpKernel μ m ω)) := by
    simpa only [Kernel.prod_apply, Kernel.map_apply _ (hf.prodMk hg),
      Kernel.map_apply _ hf, Kernel.map_apply _ hg] using hmapω
  have hmfun : Measurable (fun p : ℝ × ℝ => p.1 * p.2) := measurable_fst.mul measurable_snd
  rw [← integral_map (hf.prodMk hg).aemeasurable hmfun.aestronglyMeasurable, hmap',
    integral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y)]
  congr 1
  · simpa only [id_eq] using integral_map (μ := condExpKernel μ m ω)
      hf.aemeasurable measurable_id.aestronglyMeasurable
  · simpa only [id_eq] using integral_map (μ := condExpKernel μ m ω)
      hg.aemeasurable measurable_id.aestronglyMeasurable

theorem integral_mul_eq_integral_condExp_mul_of_condIndepFun {Ω : Type*}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f g : Ω → ℝ} (hind : CondIndepFun m hm f g μ)
    (hf : Measurable[mΩ] f) (hg : Measurable[mΩ] g) (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfgi : Integrable (fun ω => f ω * g ω) μ) :
    (∫ ω, f ω * g ω ∂μ) = ∫ ω, μ[f | m] ω * μ[g | m] ω ∂μ := by
  let : MeasurableSpace Ω := mΩ
  rw [← integral_condExp (m₀ := mΩ) (μ := μ) hm (f := fun ω => f ω * g ω)]
  exact integral_congr_ae (μ := μ)
    (condExp_mul_of_condIndepFun (mΩ := mΩ) (μ := μ) hm hind hf hg hfi hgi hfgi)

theorem condExp_pair_eq_of_condIndepFun {Ω Z W : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [mZ : MeasurableSpace Z]
    [mW : MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {z : Ω → Z} {w : Ω → W} {f : Ω → ℝ}
    (hz : Measurable z) (hw : Measurable w) (hf : Measurable f) (hfi : Integrable f μ)
    (hind : CondIndepFun (mZ.comap z) hz.comap_le w f μ) :
    μ[f | (inferInstance : MeasurableSpace (Z × W)).comap (fun ω => (z ω, w ω))] =ᵐ[μ] μ[f | mZ.comap z] := by
  have hdist := (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hf hw hz).mp hind
  have hpull := ae_of_ae_map (hz.prodMk hw).aemeasurable hdist
  filter_upwards [condExp_ae_eq_integral_condDistrib' (hz.prodMk hw) hfi,
    condExp_ae_eq_integral_condDistrib' hz hfi, hpull] with ω hpair hzω hdistω
  rw [hpair, hzω, hdistω, Kernel.prodMkRight_apply]

theorem condExp_sup_eq_of_condIndepFun {Ω Z W : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [mZ : MeasurableSpace Z]
    [mW : MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {z : Ω → Z} {w : Ω → W} {f : Ω → ℝ}
    (hz : Measurable z) (hw : Measurable w) (hf : Measurable f) (hfi : Integrable f μ)
    (hind : CondIndepFun (mZ.comap z) hz.comap_le w f μ) :
    μ[f | mZ.comap z ⊔ mW.comap w] =ᵐ[μ] μ[f | mZ.comap z] := by
  simpa only [Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk] using
    condExp_pair_eq_of_condIndepFun hz hw hf hfi hind

end Problem367

end

end OAI
