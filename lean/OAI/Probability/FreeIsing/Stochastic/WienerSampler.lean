import OAI.Probability.FreeIsing.Brownian.ContinuousExistence
import OAI.Probability.FreeIsing.Estimates.UniformSampler
import OAI.Probability.FreeIsing.Factors.Transfer

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.WienerSampler

abbrev Path := C(ℝ≥0, ℝ)

instance pathMeasurableSpace : MeasurableSpace Path := borel Path
instance pathBorelSpace : BorelSpace Path := ⟨rfl⟩

theorem measurableEmbedding_denseEval : MeasurableEmbedding
    (fun f : Path => fun n : ℕ => f (TopologicalSpace.denseSeq ℝ≥0 n)) := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval fun index => (continuous_eval_const _).measurable
  · intro f g h
    apply ContinuousMap.coe_injective
    exact (TopologicalSpace.denseRange_denseSeq ℝ≥0).equalizer f.continuous g.continuous h

theorem measurable_path_of_eval {Ω : Type*} [MeasurableSpace Ω]
    {F : Ω → Path} (hF : ∀ t, Measurable (fun ω => F ω t)) : Measurable F := by
  apply measurableEmbedding_denseEval.measurable_comp_iff.mp
  exact Measurable.of_eval fun index => hF _

theorem exists_measurable_path_version {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t))
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => B t ω)) :
    ∃ F : Ω → Path, Measurable F ∧ ∀ᵐ ω ∂μ, ∀ t, F ω t = B t ω := by
  classical
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hc)
  have hcont (ω : Ω) (hω : ω ∉ N) : Continuous (fun t => B t ω) := by
    by_contra h
    exact hω (hNsub h)
  let F : Ω → Path := fun ω => if hω : ω ∈ N then 0 else ⟨fun t => B t ω, hcont ω hω⟩
  refine ⟨F, ?_, ?_⟩
  · apply measurable_path_of_eval
    intro t
    have heq : (fun ω => F ω t) = N.piecewise (fun _ => 0) (B t) := by
      funext ω
      by_cases hω : ω ∈ N <;> simp [F, hω, Set.piecewise]
    rw [heq]
    exact measurable_const.piecewise hNm (hm t)
  · have hgood : ∀ᵐ ω ∂μ, ω ∉ N := by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hNzero
    filter_upwards [hgood] with ω hω t
    simp [F, hω]

theorem measurable_brownian_version (t : ℝ≥0) : Measurable
    (BrownianContinuousExistence.version (fun s (ω : ℝ≥0 → ℝ) => ω s) t) := by
  exact (StronglyMeasurable.limUnder (fun n =>
    (measurable_pi_apply (Real.toNNReal (ContinuousModification.dyadicLeft t n))).stronglyMeasurable)).measurable

theorem isBrownian_eval_map {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {F : Ω → Path} (hF : Measurable F)
    (heq : ∀ᵐ ω ∂μ, ∀ t, F ω t = B t ω) :
    IsBrownianReal (fun t (f : Path) => f t) (μ.map F) where
  hasLaw I := by
    have hI : Measurable (fun f : Path => I.restrict (fun t => f t)) :=
      Measurable.of_eval fun index => (continuous_eval_const index.1).measurable
    refine ⟨hI.aemeasurable, ?_⟩
    rw [Measure.map_map hI hF]
    have he : (fun ω => I.restrict (fun t => F ω t)) =ᵐ[μ]
        (fun ω => I.restrict (fun t => B t ω)) := by
      filter_upwards [heq] with ω hω
      exact funext (fun i => hω i.1)
    exact (Measure.map_congr he).trans (hB.hasLaw I).map_eq
  cont := Filter.Eventually.of_forall (fun f => f.continuous)

theorem exists_wienerMeasure :
    ∃ ν : Measure Path, IsProbabilityMeasure ν ∧
      IsBrownianReal (fun t (f : Path) => f t) ν := by
  let B := BrownianContinuousExistence.version (fun t (ω : ℝ≥0 → ℝ) => ω t)
  have hB : IsBrownianReal B BrownianExistence.preWienerMeasure :=
    BrownianContinuousExistence.isBrownianReal_version
      BrownianExistence.coordinate_isPreBrownianReal
  obtain ⟨F, hF, heq⟩ := exists_measurable_path_version
    BrownianExistence.preWienerMeasure B measurable_brownian_version hB.cont
  exact ⟨BrownianExistence.preWienerMeasure.map F,
    inferInstance,
    isBrownian_eval_map hB.toIsPreBrownianReal hF heq⟩

def wienerMeasure : Measure Path := Classical.choose exists_wienerMeasure

instance wienerProbability : IsProbabilityMeasure wienerMeasure :=
  (Classical.choose_spec exists_wienerMeasure).1

theorem coordinate_isBrownianReal :
    IsBrownianReal (fun t (f : Path) => f t) wienerMeasure :=
  (Classical.choose_spec exists_wienerMeasure).2

theorem exists_uniform01_wiener_sampler :
    ∃ ξ : ℝ → Path, Measurable ξ ∧ Measure.map ξ uniform01 = wienerMeasure :=
  exists_uniform01_sampler wienerMeasure

theorem isBrownianReal_of_sampler {ξ : ℝ → Path} (hξ : Measurable ξ)
    (hξlaw : Measure.map ξ uniform01 = wienerMeasure) :
    IsBrownianReal (fun t u => ξ u t) uniform01 where
  hasLaw I := (coordinate_isBrownianReal.hasLaw I).comp ⟨hξ.aemeasurable, hξlaw⟩
  cont := Filter.Eventually.of_forall (fun u => (ξ u).continuous)

def sample : ℝ → Path := Classical.choose exists_uniform01_wiener_sampler

theorem measurable_sample : Measurable sample :=
  (Classical.choose_spec exists_uniform01_wiener_sampler).1

theorem map_sample : Measure.map sample uniform01 = wienerMeasure :=
  (Classical.choose_spec exists_uniform01_wiener_sampler).2

theorem sample_isBrownianReal : IsBrownianReal (fun t u => sample u t) uniform01 :=
  isBrownianReal_of_sampler measurable_sample map_sample

theorem measurable_sample_eval :
    Measurable (fun p : ℝ≥0 × ℝ => sample p.2 p.1) := by
  exact continuous_eval.measurable.comp
    ((measurable_sample.comp measurable_snd).prodMk measurable_fst)

theorem wiener_starts_zero : ∀ᵐ f ∂wienerMeasure, f 0 = 0 :=
  coordinate_isBrownianReal.toIsPreBrownianReal.eval_zero_ae_eq_zero

def array (d : ℕ) : (TreeVertex d → ℝ) → (TreeVertex d → Path) :=
  vertexSampler sample

theorem measurable_array (d : ℕ) : Measurable (array d) :=
  measurable_vertexSampler measurable_sample

theorem map_array (d : ℕ) :
    Measure.map (array d) (labelMeasure d) =
      Measure.infinitePi (fun _ : TreeVertex d => wienerMeasure) := by
  rw [array, map_vertexSampler_labelMeasure measurable_sample, map_sample]

theorem array_relabel {d : ℕ} (g : TreeAut d) (u : TreeVertex d → ℝ) :
    array d (relabel g u) = relabel g (array d u) := rfl

theorem array_iIndepFun (d : ℕ) :
    iIndepFun (fun v (u : TreeVertex d → ℝ) => array d u v) (labelMeasure d) := by
  exact iIndepFun_infinitePi (fun _ => measurable_sample)

theorem array_isBrownianReal {d : ℕ} (v : TreeVertex d) :
    IsBrownianReal (fun t u => array d u v t) (labelMeasure d) where
  hasLaw I := by
    apply (sample_isBrownianReal.hasLaw I).comp
    exact ⟨(measurable_pi_apply v).aemeasurable,
      Measure.infinitePi_map_eval (fun _ : TreeVertex d => uniform01) v⟩
  cont := Filter.Eventually.of_forall (fun u => (array d u v).continuous)

end Problem367.WienerSampler

end

end OAI
