import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportedGoodSetSelection
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ProfileFlowConvergence

namespace OAI

/-! # Horizontal Lipschitz bounds for every supported profile -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Uniformly converging observables retain every uniform asymptotic bound
on the support of a weak sample limit. -/
theorem le_on_support_of_ae_sample_bound
    {X A : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace A]
    (samples : ℕ → ProbabilityMeasure A) (sample : ℕ → A → X)
    (hsample : ∀ n, Measurable (sample n)) (ν : ProbabilityMeasure X)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (sample n)) atTop (𝓝 ν))
    (obsn : ℕ → X → ℝ) (obs : X → ℝ) (hobs : Continuous obs)
    (hlim : TendstoUniformly obsn obs atTop)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (C : ℝ)
    (hbound : ∀ᶠ n in atTop, ∀ᵐ a ∂(samples n : Measure A),
      obsn n (sample n a) ≤ C + ε n)
    {f : X} (hf : f ∈ (ν : Measure X).support) : obs f ≤ C := by
  by_contra h
  have hgap : 0 < obs f - C := sub_pos.mpr (lt_of_not_ge h)
  let δ := (obs f - C) / 3
  have hδ : 0 < δ := div_pos hgap (by norm_num)
  let U := {x | C + 2 * δ < obs x}
  have hU : IsOpen U := isOpen_lt continuous_const hobs
  have hfU : f ∈ U := by dsimp [U, δ]; linarith
  obtain ⟨c, hc, hmass⟩ := eventual_positive_mass_of_supported_weak_limit hν hf hU hfU
  have herr := (Metric.tendstoUniformly_iff.mp hlim) δ hδ
  have heps := hε.eventually (gt_mem_nhds hδ)
  obtain ⟨n, hn, hb, he, hm⟩ := (hbound.and (herr.and (heps.and hmass))).exists
  have hempty : (samples n : Measure A) (sample n ⁻¹' U) = 0 := by
    have hnot : ∀ᵐ a ∂(samples n : Measure A), a ∉ sample n ⁻¹' U := by
      filter_upwards [hn] with a haBound
      intro ha
      have hd := hb (sample n a)
      have hd' : obs (sample n a) < obsn n (sample n a) + δ := by
        have ht := (abs_lt.mp (by simpa only [Real.dist_eq, abs_sub_comm] using hd)).1
        linarith
      change C + 2 * δ < obs (sample n a) at ha
      linarith
    simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hnot
  have hz : ((ProbabilityMeasure.map (samples n) (sample n) : Measure X) U).toReal = 0 := by
    change (Measure.map (sample n) (samples n : Measure A) U).toReal = 0
    rw [Measure.map_apply (hsample n) hU.measurableSet,
      hempty, ENNReal.toReal_zero]
  rw [hz] at hm
  exact (not_le_of_gt hc) hm

/-- The pointwise version of the almost-everywhere sample bound. -/
theorem le_on_support_of_uniform_sample_bound
    {X A : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [MeasurableSpace A]
    (samples : ℕ → ProbabilityMeasure A) (sample : ℕ → A → X)
    (hsample : ∀ n, Measurable (sample n)) (ν : ProbabilityMeasure X)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (sample n)) atTop (𝓝 ν))
    (obsn : ℕ → X → ℝ) (obs : X → ℝ) (hobs : Continuous obs)
    (hlim : TendstoUniformly obsn obs atTop)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (C : ℝ)
    (hbound : ∀ᶠ n in atTop, ∀ a, obsn n (sample n a) ≤ C + ε n)
    {f : X} (hf : f ∈ (ν : Measure X).support) : obs f ≤ C := by
  exact le_on_support_of_ae_sample_bound samples sample hsample ν hν obsn obs hobs hlim
    ε hε C (hbound.mono fun _ hn => Filter.Eventually.of_forall hn) hf

def profileFlowDistance {V W : Type*} [TopologicalSpace V] [LocallyCompactSpace V]
    [PseudoMetricSpace W] (S : Set C(V, W)) (z : V) (s t : ℝ)
    (F : C(V × ℝ, V)) : C(S, ℝ) :=
  ⟨fun f => dist (f.val (F (z, s))) (f.val (F (z, t))), by
    exact (continuous_eval.comp (continuous_subtype_val.prodMk continuous_const)).dist
      (continuous_eval.comp (continuous_subtype_val.prodMk continuous_const))⟩

theorem continuous_profileFlowDistance
    {V W : Type*} [TopologicalSpace V] [LocallyCompactSpace V]
    [PseudoMetricSpace W] (S : Set C(V, W)) (z : V) (s t : ℝ) :
    Continuous (profileFlowDistance S z s t) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : C(V × ℝ, V) × S =>
    dist (p.2.val (p.1 (z, s))) (p.2.val (p.1 (z, t))))
  apply Continuous.dist
  · exact continuous_eval.comp ((continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_eval.comp (continuous_fst.prodMk continuous_const)))
  · exact continuous_eval.comp ((continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_eval.comp (continuous_fst.prodMk continuous_const)))

/-- A coarse Lipschitz bound with a vanishing additive error becomes an
exact Lipschitz bound along the limiting horizontal flow. -/
theorem lipschitz_supported_profile_flow
    {V W A : Type*} [TopologicalSpace V] [LocallyCompactSpace V]
    [PseudoMetricSpace W] [MeasurableSpace A]
    (S : Set C(V, W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (samples : ℕ → ProbabilityMeasure A) (sample : ℕ → A → S)
    (hsample : ∀ n, Measurable (sample n)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (sample n)) atTop (𝓝 ν))
    (Fn : ℕ → C(V × ℝ, V)) (F : C(V × ℝ, V)) (hF : Tendsto Fn atTop (𝓝 F))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (C : ℝ≥0) (z : V)
    (hbound : ∀ᶠ n in atTop, ∀ a s t,
      dist ((sample n a).val (Fn n (z, s))) ((sample n a).val (Fn n (z, t))) ≤
        C * |s - t| + ε n)
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    LipschitzWith C (fun t : ℝ => f.val (F (z, t))) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  apply LipschitzWith.of_dist_le_mul
  intro s t
  let obsn := fun n => profileFlowDistance S z s t (Fn n)
  let obs := profileFlowDistance S z s t F
  have ho : Tendsto obsn atTop (𝓝 obs) :=
    ((continuous_profileFlowDistance S z s t).tendsto F).comp hF
  have hu : TendstoUniformly (fun n g => obsn n g) obs atTop :=
    tendstoUniformlyOn_univ.mp
      ((ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ho)
        univ isCompact_univ)
  have hb := le_on_support_of_uniform_sample_bound samples sample hsample ν hν
    (fun n g => obsn n g) obs obs.continuous hu ε hε (C * |s - t|)
    (hbound.mono fun n hn a => hn a s t) hf
  simpa only [obs, profileFlowDistance, ContinuousMap.coe_mk, Real.dist_eq] using hb

end PolycyclicRecognition

end

end OAI
