import Mathlib
import OAI.Probability.SKValue.Control.StripRegularity

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

lemma IsDiffusion.gradient_square_integral {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    {T : ℝ} (hT : 0<T) (hT1 : T<1) :
    (∫ ω, (gradient W γ T (X T ω))^2 ∂W.μ)=
      ∫ t in (0 : ℝ)..T, ∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ := by
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨hT.le,hT1⟩
  exact diffusion_gradient_isometry W.brownian.toIsPreBrownianReal hT hT1.le hG
    hD hLu hLa hDb hu ha
    (fun t ht ↦ (hX.measurable ⟨ht.1,ht.2.trans hT1.le⟩).aestronglyMeasurable)
    (hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ hu s hs t ht y x))

lemma IsDiffusion.curvature_square_mean_continuous {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ) :
    ContinuousOn (fun t ↦ ∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ) (Ico (0 : ℝ) 1) := by
  intro t ht
  obtain ⟨T,htT,hT1⟩ := exists_between ht.2
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨ht.1.trans htT.le,hT1⟩
  have hc := mean_derivative_square_continuous hD hLa
    (fun s hs ↦ (hG.smooth s hs).continuous_deriv (by norm_num)) hDb ha
    (fun s hs ↦ (hX.measurable ⟨hs.1,hs.2.trans hT1.le⟩).aestronglyMeasurable)
    (hX.2.mono (fun _ hω ↦ hω.1.mono (Icc_subset_Icc le_rfl hT1.le)))
  apply (hc t ⟨ht.1,htT.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with s hs hsT
  exact ⟨hs.1,hsT.le⟩

lemma continuous_eq_one_of_primitive {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ico (0 : ℝ) 1))
    (hi : ∀ t∈Ioo (0 : ℝ) 1, (∫ s in (0 : ℝ)..t, f s)=t) :
    ∀ t∈Ico (0 : ℝ) 1, f t=1 := by
  have hint (t : ℝ) (ht : t∈Ioo (0 : ℝ) 1) : f t=1 := by
    have hf : IntervalIntegrable f volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.1.le]
      exact hc.mono (fun s hs ↦ ⟨hs.1,hs.2.trans_lt ht.2⟩)
    have hs : Ico (0 : ℝ) 1∈𝓝 t := Ico_mem_nhds ht.1 ht.2
    have hd := intervalIntegral.integral_hasDerivAt_right hf
      ⟨Ico (0 : ℝ) 1,hs,hc.aestronglyMeasurable measurableSet_Ico⟩
      ((hc t ⟨ht.1.le,ht.2⟩).continuousAt hs)
    have he : (fun t ↦ ∫ s in (0 : ℝ)..t, f s)=ᶠ[𝓝 t] (id : ℝ → ℝ) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hi s hs
    exact hd.unique ((hasDerivAt_id t).congr_of_eventuallyEq he)
  intro t ht
  obtain h0|h0 := ht.1.eq_or_lt
  · subst t
    have hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
      apply (hc 0 (by norm_num)).mono_left
      apply le_inf nhdsWithin_le_nhds
      apply le_principal_iff.mpr
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))] with s hs hs1
      exact ⟨hs.le,hs1⟩
    apply tendsto_nhds_unique hlim
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))] with s hs hs1
    exact (hint s ⟨hs,hs1⟩).symm
  · exact hint t ⟨h0,ht.2⟩

lemma IsDiffusion.curvature_unit_moment_of_contact {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1 := by
  apply continuous_eq_one_of_primitive (hX.curvature_square_mean_continuous hreg)
  intro t ht
  rw [←hX.gradient_square_integral hreg ht.1 ht.2,hmom t ⟨ht.1.le,ht.2⟩]

end SKValue

end

end OAI
