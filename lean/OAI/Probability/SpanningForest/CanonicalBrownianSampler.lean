import OAI.Probability.SpanningForest.CanonicalBrownianReference
import OAI.Probability.SpanningForest.CanonicalPosteriorMartingale
import OAI.Probability.SpanningForest.InnovationProcessLaw
import OAI.Probability.SpanningForest.RawInnovationSampler

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336.CanonicalBrownianSampler

local instance : MeasurableSpace GlobalWiener.Path := borel _
local instance : BorelSpace GlobalWiener.Path := ⟨rfl⟩

open CanonicalBrownianReference

variable {I : Type*} [countableIndices : Countable I]

def signal (q : Space I) (i : I) : ℝ := TiltLimit.bit (CanonicalBrownianReference.hidden q i)

def driftField (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (i : I) (s : ℝ) (q : Space I) : ℝ :=
  PosteriorDrift.drift μ S s (CanonicalBrownianReference.observation s.toNNReal q) i

omit countableIndices in
theorem observation_measurable [Countable I] (t : ℝ≥0) (i : I) :
    Measurable (fun q : Space I => CanonicalBrownianReference.observation t q i) :=
  (measurable_pi_apply i).comp (observation_jointlyMeasurable.comp
    (measurable_const.prodMk measurable_id))

def filtration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Space I)) :=
  Innovation.observationHistoryFiltration CanonicalBrownianReference.observation observation_measurable

omit countableIndices in
theorem measurable_driftField [Countable I] (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I) (i : I) :
    Measurable (Function.uncurry (driftField μ S i)) := by
  have hf : Measurable (fun p : ℝ × Space I => CanonicalBrownianReference.observation p.1.toNNReal p.2) :=
    observation_jointlyMeasurable.comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  change Measurable (fun p : ℝ × Space I =>
    PosteriorDrift.drift μ S p.1 (CanonicalBrownianReference.observation p.1.toNNReal p.2) i)
  let f : ℝ × Space I → ℝ × (I → ℝ) := fun p =>
    (p.1, CanonicalBrownianReference.observation p.1.toNNReal p.2)
  have hm : Measurable f := measurable_fst.prodMk hf
  exact (PosteriorDrift.measurable_drift_coordinate μ S i).comp (f := f) hm

theorem martingale_innovation (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I) (i : I)
    (hS : Monotone (S i)) (hcover : ∀ j, ∃ n, j ∈ S i n) :
    Martingale (Innovation.nnInnovation (fun q : Space I => signal q i)
      (CanonicalBrownianReference.noise i) (driftField μ S i)) filtration (law μ) := by
  exact CanonicalPosteriorMartingale.martingale_nnInnovation (law μ) μ CanonicalBrownianReference.hidden
    hidden_measurable (hidden_hasLaw μ).map_eq CanonicalBrownianReference.noise
    (fun i => (noise_brownian μ i).toIsPreBrownianReal) noise_measurable
    noise_continuous (noise_independent μ) (hidden_independent_flat_noise μ)
    S i hS hcover

theorem raw_innovation_identDistrib (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I)
    (hS : ∀ i, Monotone (S i)) (hcover : ∀ i j, ∃ n, j ∈ S i n) :
    IdentDistrib
      (fun q i t => Innovation.nnInnovation (fun q : Space I => signal q i)
        (CanonicalBrownianReference.noise i) (driftField μ S i) t q)
      (fun (q : Space I) i t => CanonicalBrownianReference.noise i t q) (law μ) (law μ) := by
  apply InnovationProcessLaw.identDistrib_nnInnovation (law μ) filtration signal CanonicalBrownianReference.noise
    (driftField μ S)
  · exact fun i => (noise_brownian μ i).toIsPreBrownianReal
  · exact noise_measurable
  · exact noise_independent μ
  · exact bit_hidden_measurable
  · exact bit_hidden_independent_noise μ
  · exact measurable_driftField μ S
  · exact bit_hidden_mem_Icc
  · exact fun i s q => PosteriorDrift.drift_mem_Icc μ S s _ i
  · exact fun i => martingale_innovation μ S i (hS i) (hcover i)
  · intro u
    exact le_rfl

theorem raw_innovation_hasLaw (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I)
    (hS : ∀ i, Monotone (S i)) (hcover : ∀ i j, ∃ n, j ∈ S i n) :
    HasLaw (RawInnovationSampler.rawInnovation CanonicalBrownianReference.hidden CanonicalBrownianReference.noise (PosteriorDrift.drift μ S))
      ((noiseLaw I).map ContinuousPathLaw.raw) (law μ) := by
  have hd := raw_innovation_identDistrib μ S hS hcover
  exact ⟨hd.aemeasurable_fst, hd.map_eq.trans (raw_noise_hasLaw μ).map_eq⟩

theorem hasLaw_sample
    (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (hS : ∀ e, Monotone (S e)) (hcover : ∀ e i, ∃ n, i ∈ S e n)
    {L : ℝ} (hL : 0 ≤ L) (hresponse : PosteriorDrift.FiniteResponseBound μ S L) :
    HasLaw (PicardSampler.NonnegativeTime.sample ContinuousPathLaw.raw
      (PosteriorDrift.drift μ S)) (μ : Measure (I → Bool)) (noiseLaw I) := by
  have hfresh : HasLaw (id : (I → GlobalWiener.Path) → I → GlobalWiener.Path)
      (noiseLaw I) (noiseLaw I) := ⟨measurable_id.aemeasurable, Measure.map_id⟩
  exact RawInnovationSampler.hasLaw_of_raw_innovation (hidden_hasLaw μ)
    (noise_brownian μ) (PosteriorDrift.drift μ S)
    (PosteriorDrift.measurable_drift_coordinate μ S)
    (fun t y i => by
      have h := PosteriorDrift.drift_mem_Icc μ S t y i
      rw [abs_of_nonneg h.1]
      exact h.2) hL
    (fun t y z D hD hdiff i => PosteriorDrift.drift_response μ S hresponse
      t y z hD hdiff i) (raw_innovation_hasLaw μ S hS hcover) hfresh

end Problem336.CanonicalBrownianSampler

end

end OAI
