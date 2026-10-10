import Mathlib
import OAI.Probability.SKValue.Processes.StripPaths
import OAI.Probability.SKValue.Processes.DiffusionGradientCondExp
import OAI.Probability.SKValue.Processes.TerminalCondExp

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
open scoped Topology

noncomputable def BrownianSpace.realFiltration (W : BrownianSpace) :
    Filtration ℝ W.measurableSpace :=
  ⟨fun t ↦ W.filtration t.toNNReal, fun _ _ h ↦ W.filtration.mono (Real.toNNReal_mono h),
    fun t ↦ W.filtration.le t.toNNReal⟩

lemma IsDiffusion.natural_measurable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    StronglyMeasurable[W.filtration t.toNNReal] (X t) := by
  have hh := hX.1 t.toNNReal
  simpa only [Real.coe_toNNReal t ht.1,min_eq_left ht.2] using hh.stronglyMeasurable

lemma IsDiffusion.unitMomentMartingale {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hreg : ∀ T∈Ico (0 : ℝ) 1, ∃ K L Lu : ℝ, 0≤Lu ∧
      GradientStripCore T γ.coeff (gradient W γ) K L ∧
      ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
        |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|))
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)) := by
  constructor
  · intro t ht
    obtain ⟨K,L,Lu,hLu,hg,hLip⟩ := hreg t ht
    exact (hg.smooth t ⟨ht.1,le_rfl⟩).continuous.comp_stronglyMeasurable
      (hX.natural_measurable ⟨ht.1,ht.2.le⟩)
  · intro t ht ω
    obtain ⟨K,L,Lu,hLu,hg,hLip⟩ := hreg t ht
    exact hg.bounded t ⟨ht.1,le_rfl⟩ _
  · intro s hs t ht hst
    obtain ⟨K,L,Lu,hLu,hg,hLip⟩ := hreg t ht
    exact diffusion_gradient_condExp W.brownian.toIsPreBrownianReal W.measurable ht.2.le
      hLu hg hLip (fun r hr ↦ hX.natural_measurable ⟨hr.1,hr.2.trans ht.2.le⟩)
      ((hX.strip_paths ht.1 ht.2 hLu (fun a ha b hb x y ↦ hLip b hb a ha y x)).mono
        (fun _ hω ↦ ⟨hω.1,hω.2.1,hω.2.2.1⟩)) ⟨hs.1,hst⟩ ⟨ht.1,le_rfl⟩ hst
  · exact hmom

lemma IsDiffusion.gradient_continuous {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hreg : ∀ T∈Ico (0 : ℝ) 1, ∃ Lu : ℝ, 0≤Lu ∧
      ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
        |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|)) :
    ∀ᵐ ω ∂W.μ, ContinuousOn (fun t ↦ gradient W γ t (X t ω)) (Ico (0 : ℝ) 1) := by
  filter_upwards [hX.2] with ω hω
  intro t ht
  obtain ⟨T,htT,hT1⟩ := exists_between ht.2
  have hT : T∈Ico (0 : ℝ) 1 := ⟨ht.1.trans htT.le,hT1⟩
  obtain ⟨Lu,hLu,hLip⟩ := hreg T hT
  have hj : ContinuousOn (fun p : ℝ×ℝ ↦ gradient W γ p.1 p.2)
      {p | p.1∈Icc (0 : ℝ) T} :=
    derivative_joint_continuous hLu hLip
  have hp : ContinuousOn (fun s ↦ (s,X s ω)) (Icc (0 : ℝ) T) :=
    continuousOn_id.prodMk (hω.1.mono (Icc_subset_Icc le_rfl hT1.le))
  have hc := ContinuousOn.comp (g := fun p : ℝ×ℝ ↦ gradient W γ p.1 p.2)
    (f := fun s ↦ (s,X s ω)) hj hp (fun s hs ↦ hs)
  apply (hc t ⟨ht.1,htT.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with s hs hsT
  exact ⟨hs.1,hsT.le⟩

lemma IsDiffusion.exists_gradient_terminal {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hreg : ∀ T∈Ico (0 : ℝ) 1, ∃ K L Lu : ℝ, 0≤Lu ∧
      GradientStripCore T γ.coeff (gradient W γ) K L ∧
      ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
        |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|))
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    ∃ U : W.Ω → ℝ, StronglyMeasurable[W.filtration 1] U ∧
      Martingale (gradientStopped W γ X U) W.filtration W.μ ∧
      (∀ᵐ ω ∂W.μ, |U ω|≤1 ∧ (U ω)^2=1 ∧
        Tendsto (fun t ↦ gradient W γ t (X t ω)) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) ∧
      Tendsto (fun t ↦ ∫ ω, (gradient W γ t (X t ω)-U ω)^2 ∂W.μ)
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hh := (hX.unitMomentMartingale hreg hmom).exists_terminal
    (hX.gradient_continuous (fun T hT ↦ by
      obtain ⟨K,L,Lu,hLu,hg,hLip⟩ := hreg T hT
      exact ⟨Lu,hLu,hLip⟩))
  have he : (⟨fun t : ℝ≥0 ↦ W.realFiltration t,
      fun _ _ hij ↦ W.realFiltration.mono hij,fun t ↦ W.realFiltration.le t⟩ :
      Filtration ℝ≥0 W.measurableSpace)=W.filtration := by
    ext : 1
    simp only [BrownianSpace.realFiltration,Real.toNNReal_coe]
  obtain ⟨U,hUm,hm,hU,hUt⟩ := hh
  refine ⟨U,?_,?_,hU,hUt⟩
  · change StronglyMeasurable[W.filtration ((1 : ℝ).toNNReal)] U at hUm
    have h1 : (1 : ℝ).toNNReal = (1 : ℝ≥0) := by norm_num
    rw [h1] at hUm
    exact hUm
  · change Martingale (gradientStopped W γ X U)
      (⟨fun t : ℝ≥0 ↦ W.realFiltration t,
        fun _ _ hij ↦ W.realFiltration.mono hij,fun t ↦ W.realFiltration.le t⟩ :
          Filtration ℝ≥0 W.measurableSpace) W.μ at hm
    rw [he] at hm
    exact hm

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

lemma joint_aestronglyMeasurable_of_ae_continuous
    {Ω I : Type*} [MeasurableSpace Ω] [TopologicalSpace I] [TopologicalSpace.MetrizableSpace I]
    [MeasurableSpace I] [SecondCountableTopology I] [OpensMeasurableSpace I]
    {μ : Measure Ω} {ν : Measure I} [SFinite μ] [SFinite ν]
    {f : I → Ω → ℝ} (hm : ∀ t, StronglyMeasurable (f t))
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ f t ω)) :
    AEStronglyMeasurable (Function.uncurry f) (ν.prod μ) := by
  classical
  obtain ⟨s,hsub,hsm,hs0⟩ := exists_measurable_superset_of_null (ae_iff.mp hc)
  let g (t : I) (ω : Ω) : ℝ := if ω∈s then 0 else f t ω
  have hg : StronglyMeasurable (Function.uncurry g) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro ω
      by_cases hω : ω∈s
      · simpa only [g,ite_eq_left hω] using (continuous_const : Continuous (fun _ : I ↦ (0 : ℝ)))
      · have hh : Continuous (fun t ↦ f t ω) := by
          by_contra hh
          exact hω (hsub hh)
        simpa only [g,ite_eq_right hω] using hh
    · intro t
      exact StronglyMeasurable.ite hsm stronglyMeasurable_const (hm t)
  apply hg.aestronglyMeasurable.congr
  have hs : ∀ᵐ ω ∂μ, ω∉s := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hs0
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hs] with p hp
  exact ite_eq_right hp

lemma compact_joint_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {f : ℝ → Ω → ℝ} {T : ℝ} (hT : 0≤T)
    (hm : ∀ t∈Icc (0 : ℝ) T, StronglyMeasurable (f t))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ f t ω) (Icc (0 : ℝ) T)) :
    AEStronglyMeasurable (Function.uncurry f) ((volume.restrict (Ioc (0 : ℝ) T)).prod μ) := by
  let c : ℝ → ℝ := fun t ↦ (projIcc 0 T hT t : ℝ)
  have hcm (t : ℝ) : c t∈Icc (0 : ℝ) T := (projIcc 0 T hT t).2
  have hj : AEStronglyMeasurable (fun p : ℝ×Ω ↦ f (c p.1) p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ) :=
    joint_aestronglyMeasurable_of_ae_continuous (fun t ↦ hm _ (hcm t))
      (hc.mono (fun ω hω ↦ hω.comp_continuous (continuous_subtype_val.comp continuous_projIcc) hcm))
  apply hj.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem measurableSet_Ioc : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T), t∈Ioc (0 : ℝ) T)] with p hp
  simp only [c,projIcc_of_mem hT ⟨hp.1.le,hp.2⟩,Function.uncurry]

lemma compact_weighted_fubini {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ℝ → Ω → ℝ} {U : Ω → ℝ}
    {γ : ℝ → ℝ} {T : ℝ} (hT : 0≤T)
    (hm : ∀ t∈Icc (0 : ℝ) T, StronglyMeasurable (f t))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ f t ω) (Icc (0 : ℝ) T))
    (hb : ∀ t∈Icc (0 : ℝ) T, ∀ ω, |f t ω|≤1)
    (hUm : AEStronglyMeasurable U μ) (hUb : ∀ᵐ ω ∂μ, |U ω|≤1)
    (hγ : IntervalIntegrable γ volume 0 T) :
    (∫ ω, U ω*(∫ t in (0 : ℝ)..T, γ t*f t ω) ∂μ) =
      ∫ t in (0 : ℝ)..T, γ t*(∫ ω, U ω*f t ω ∂μ) := by
  have hγi : Integrable γ (volume.restrict (Ioc (0 : ℝ) T)) := hγ.1
  have hj := compact_joint_aestronglyMeasurable hT hm hc
  have ht : ∀ᵐ p : ℝ×Ω ∂(volume.restrict (Ioc (0 : ℝ) T)).prod μ,
      p.1∈Ioc (0 : ℝ) T := Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  have hu : ∀ᵐ p : ℝ×Ω ∂(volume.restrict (Ioc (0 : ℝ) T)).prod μ,
      |U p.2|≤1 := Measure.quasiMeasurePreserving_snd.ae hUb
  have hi : Integrable (fun p : ℝ×Ω ↦ γ p.1*(U p.2*f p.1 p.2))
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ) := by
    apply (hγi.abs.comp_fst μ).mono' (hγi.aestronglyMeasurable.comp_fst.mul (hUm.comp_snd.mul hj))
    filter_upwards [ht,hu] with p hp hUp
    change ‖γ p.1*(U p.2*f p.1 p.2)‖≤|γ p.1|
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    have hf := hb p.1 ⟨hp.1.le,hp.2⟩ p.2
    have huf : |U p.2| * |f p.1 p.2| ≤ 1 := by
      nlinarith [abs_nonneg (f p.1 p.2),abs_nonneg (U p.2)]
    exact (mul_le_mul_of_nonneg_left huf (abs_nonneg _)).trans_eq (mul_one _)
  simp only [intervalIntegral.integral_of_le hT]
  have he := integral_integral_swap (f := fun t ω ↦ γ t*(U ω*f t ω)) hi
  calc
    _ = ∫ ω, ∫ t in Ioc (0 : ℝ) T, γ t*(U ω*f t ω) ∂volume ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring
    _ = ∫ t in Ioc (0 : ℝ) T, ∫ ω, γ t*(U ω*f t ω) ∂μ := he.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact integral_const_mul _ _

lemma UnitMomentMartingale.terminal_past_product
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {f : ℝ → Ω → ℝ}
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω|≤1 ∧ Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω)))
    {t : ℝ} (ht : t∈Ico (0 : ℝ) 1) :
    (∫ ω, U ω*f t ω ∂μ)=t := by
  have hUi : Integrable U μ := Integrable.of_bound (hUm.mono (ℱ.le 1)).aestronglyMeasurable 1
    (hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1))
  have hprod : Integrable (fun ω ↦ f t ω*U ω) μ :=
    hUi.bdd_mul ((h.measurable t ht).mono (ℱ.le t)).aestronglyMeasurable
      (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (h.bounded t ht ω)))
  have hc := condExp_mul_of_stronglyMeasurable_left (h.measurable t ht) hprod hUi
  have he : μ[(f t)*U | ℱ t] =ᵐ[μ] (fun ω ↦ (f t ω)^2) := by
    filter_upwards [hc,h.terminal_condExp hUm hU ht] with ω hω hω'
    simpa only [Pi.mul_apply,hω',pow_two] using hω
  calc
    _ = ∫ ω, f t ω*U ω ∂μ := by congr 1; funext ω; ring
    _ = ∫ ω, μ[(f t)*U | ℱ t] ω ∂μ := (integral_condExp (ℱ.le t)).symm
    _ = ∫ ω, (f t ω)^2 ∂μ := integral_congr_ae he
    _ = t := h.secondMoment t ht

end SKValue

end

end OAI
