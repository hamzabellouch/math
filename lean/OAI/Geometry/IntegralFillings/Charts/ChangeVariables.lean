import Mathlib
import OAI.Geometry.IntegralFillings.Charts.Differentiability

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
lemma lipschitzOn_image_null {s : Set E} {f : E → E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hs : μ s = 0) : μ (f '' s) = 0 := by
  let H : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have ha : H ≪ μ := Measure.absolutelyContinuous_isAddHaarMeasure H μ
  have hb : μ ≪ H := Measure.absolutelyContinuous_isAddHaarMeasure μ H
  apply hb
  apply le_antisymm _ zero_le
  have hi := hf.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
  change H (f '' s) ≤ (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) * H s at hi
  simpa only [ha hs,mul_zero] using hi

lemma lipschitzOn_image_ae_congr_subset {s t : Set E} {f : E → E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hts : t ⊆ s) (heq : s =ᵐ[μ] t) :
    f '' s =ᵐ[μ] f '' t := by
  apply ae_eq_set.mpr
  constructor
  · have hsub : f '' s \ f '' t ⊆ f '' (s \ t) := by
      rintro y ⟨⟨x,hx,rfl⟩,hy⟩
      exact ⟨x,⟨hx,fun h => hy ⟨x,h,rfl⟩⟩,rfl⟩
    exact measure_mono_null hsub
      (lipschitzOn_image_null μ (hf.mono sdiff_subset) (ae_eq_set.mp heq).1)
  · rw [sdiff_eq_empty.mpr (image_mono hts),measure_empty]

lemma exists_measurable_full_derivative_domain {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ t, t ⊆ s ∧ MeasurableSet t ∧ t =ᵐ[μ] s ∧
      ∀ x ∈ t, HasFDerivWithinAt f (fderivWithin ℝ f s x) t x := by
  let d : Set E := {x | x ∈ s ∧ DifferentiableWithinAt ℝ f s x}
  have hd : d =ᵐ[μ] s := by
    filter_upwards [(ae_restrict_iff' hs).mp (hf.ae_differentiableWithinAt hs (μ := μ))] with x hx
    change (x ∈ s ∧ DifferentiableWithinAt ℝ f s x) = (x ∈ s)
    exact propext ⟨And.left,fun h => ⟨h,hx h⟩⟩
  obtain ⟨t,htd,htm,hteq⟩ := (hs.nullMeasurableSet.congr hd.symm).exists_measurable_subset_ae_eq
  have hts : t ⊆ s := fun x hx => (htd hx).1
  exact ⟨t,hts,htm,hteq.trans hd,fun x hx => (htd hx).2.hasFDerivWithinAt.mono hts⟩

lemma integral_image_eq_integral_abs_det_within {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : E → V) :
    ∫ y in f '' s, g y ∂μ =
      ∫ x in s, |(fderivWithin ℝ f s x).det| • g (f x) ∂μ := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  calc
    _ = ∫ y in f '' t, g y ∂μ :=
      setIntegral_congr_set (lipschitzOn_image_ae_congr_subset μ hf hts hteq.symm)
    _ = ∫ x in t, |(fderivWithin ℝ f s x).det| • g (f x) ∂μ :=
      integral_image_eq_integral_abs_det_fderiv_smul μ htm htd (hinj.mono hts) g
    _ = _ := setIntegral_congr_set hteq

lemma integrableOn_image_iff_integrableOn_abs_det_within {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : E → V) :
    IntegrableOn g (f '' s) μ ↔
      IntegrableOn (fun x => |(fderivWithin ℝ f s x).det| • g (f x)) s μ := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  exact (integrableOn_congr_set_ae (lipschitzOn_image_ae_congr_subset μ hf hts hteq.symm)).trans
    ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ htm htd (hinj.mono hts) g).trans
      (integrableOn_congr_set_ae hteq))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lipschitzOn_invFunOn {s : Set E} {f : E → E} {L : ℝ≥0}
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y)) :
    LipschitzOnWith L (Function.invFunOn f s) (f '' s) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have h := ha _ (Function.invFunOn_mem hx) _ (Function.invFunOn_mem hy)
  simpa only [Function.invFunOn_eq hx,Function.invFunOn_eq hy] using h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma antilipschitzOn_injOn {s : Set E} {f : E → E} {L : ℝ≥0}
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y)) :
    InjOn f s := by
  intro x hx y hy heq
  have h := ha x hx y hy
  rw [heq,dist_self,mul_zero] at h
  exact dist_le_zero.mp h

lemma bilipschitzOn_ae_pullback {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K L : ℝ≥0} (hf : LipschitzOnWith K f s)
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y))
    {p : E → Prop} (hp : ∀ᵐ y ∂μ.restrict (f '' s), p y) :
    ∀ᵐ x ∂μ.restrict s, p (f x) := by
  have hinj := antilipschitzOn_injOn ha
  have him := hs.image_of_continuousOn_injOn hf.continuousOn hinj
  have hnull : μ ({y | ¬ p y} ∩ f '' s) = 0 := by
    rwa [ae_iff,Measure.restrict_apply' him] at hp
  rw [ae_iff,Measure.restrict_apply' hs]
  apply measure_mono_null _
    (lipschitzOn_image_null μ ((lipschitzOn_invFunOn ha).mono inter_subset_right) hnull)
  intro x hx
  refine ⟨f x,⟨hx.1,⟨x,hx.2,rfl⟩⟩,?_⟩
  exact hinj.leftInvOn_invFunOn hx.2

lemma ae_fderivWithin_comp_bilipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K L : ℝ≥0} (hf : LipschitzOnWith K f s)
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {g : E → V} {J : ℝ≥0} (hg : LipschitzOnWith J g (f '' s)) :
    ∀ᵐ x ∂μ.restrict s, fderivWithin ℝ (g ∘ f) s x =
      (fderivWithin ℝ g (f '' s) (f x)).comp (fderivWithin ℝ f s x) := by
  have hinj := antilipschitzOn_injOn ha
  have him := hs.image_of_continuousOn_injOn hf.continuousOn hinj
  filter_upwards [ae_uniqueDiffWithinAt μ s,hf.ae_differentiableWithinAt hs (μ := μ),
    bilipschitzOn_ae_pullback μ hs hf ha (hg.ae_differentiableWithinAt him (μ := μ))]
    with x hx hfx hgx
  exact fderivWithin_comp x hgx hfx (mapsTo_image f s) hx

lemma ae_det_fderivWithin_ne_zero_bilipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K L : ℝ≥0} (hf : LipschitzOnWith K f s)
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y)) :
    ∀ᵐ x ∂μ.restrict s, (fderivWithin ℝ f s x).det ≠ 0 := by
  have hinj := antilipschitzOn_injOn ha
  filter_upwards [ae_fderivWithin_comp_bilipschitzOn μ hs hf ha (lipschitzOn_invFunOn ha),
    ae_uniqueDiffWithinAt μ s,ae_restrict_mem hs] with x hx hu hxs
  have heq : EqOn (Function.invFunOn f s ∘ f) id s :=
    fun x hxs => hinj.leftInvOn_invFunOn hxs
  rw [fderivWithin_congr' heq hxs,fderivWithin_id hu] at hx
  have hd := congrArg (fun a : E →L[ℝ] E => a.det) hx
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hd
  intro hz
  change LinearMap.det _ = 0 at hz
  rw [hz,mul_zero] at hd
  exact one_ne_zero hd

lemma aemeasurable_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    AEMeasurable (fderivWithin ℝ f s) (μ.restrict s) := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  have h := aemeasurable_fderivWithin μ htm htd
  rwa [Measure.restrict_congr_set hteq] at h

lemma ae_norm_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∀ᵐ x ∂μ.restrict s, ‖fderivWithin ℝ f s x‖ ≤ K := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  have hlin : ApproximatesLinearOn f (0 : E →L[ℝ] E) t K := by
    intro x hx y hy
    simpa only [_root_.zero_apply,sub_zero,←dist_eq_norm] using
      hf.dist_le_mul x (hts hx) y (hts hy)
  have h := hlin.norm_fderiv_sub_le μ htm (fderivWithin ℝ f s) htd
  rw [Measure.restrict_congr_set hteq] at h
  filter_upwards [h] with x hx
  exact_mod_cast (by simpa only [sub_zero] using hx : ‖fderivWithin ℝ f s x‖₊ ≤ K)

lemma ae_bound_det_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ C : ℝ, ∀ᵐ x ∂μ.restrict s, ‖(fderivWithin ℝ f s x).det‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) (K : ℝ)).exists_bound_of_continuousOn
    (ContinuousLinearMap.continuous_det (𝕜 := ℝ) (E := E)).continuousOn
  refine ⟨C,?_⟩
  filter_upwards [ae_norm_fderivWithin_lipschitzOn μ hs hf] with x hx
  exact hC _ (by simpa only [mem_closedBall,dist_zero_right] using hx)

lemma integrable_mul_det_fderivWithin_lipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    {g : E → ℝ} (hg : IntegrableOn g s μ) :
    IntegrableOn (fun x => g x * (fderivWithin ℝ f s x).det) s μ := by
  obtain ⟨C,hC⟩ := ae_bound_det_fderivWithin_lipschitzOn μ hs hf
  exact hg.mul_bdd ((ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
    (aemeasurable_fderivWithin_lipschitzOn μ hs hf)).aestronglyMeasurable) hC

end SharpIntegralFillings
end

end OAI
