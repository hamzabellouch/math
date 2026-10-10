import OAI.Probability.SpanningForest.PosteriorTiltLimit
import OAI.Probability.SpanningForest.CanonicalDrift

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Problem336.PosteriorDrift
open TiltLimit

variable {I : Type*} [Countable I]

def finiteStage (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (e : I) (n : ℕ) (p : ℝ × (I → ℝ)) : ℝ :=
  finiteTiltMean μ (S e n) (fun i => p.2 i - p.1 / 2) e

def drift (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (t : ℝ) (y : I → ℝ) (e : I) : ℝ :=
  CanonicalDrift.outerLimit (finiteStage μ S e) (t, y)

omit [Countable I] in
theorem measurable_drift_coordinate (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I) (e : I) :
    Measurable (fun p : ℝ × (I → ℝ) => drift μ S p.1 p.2 e) :=
  CanonicalDrift.measurable_outerLimit (fun n => measurable_finitePosterior μ (S e n) e)

omit [Countable I] in
theorem measurable_drift (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I) :
    Measurable (fun p : ℝ × (I → ℝ) => drift μ S p.1 p.2) :=
  Measurable.of_eval (fun e => measurable_drift_coordinate μ S e)

theorem drift_mem_Icc (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (t : ℝ) (y : I → ℝ) (e : I) : drift μ S t y e ∈ Set.Icc (0 : ℝ) 1 :=
  CanonicalDrift.outerLimit_mem_Icc (b := finiteStage μ S e)
    (fun n (p : ℝ × (I → ℝ)) =>
      finiteTiltMean_mem_Icc μ (S e n) (fun i => p.2 i - p.1 / 2) e) (t, y)

def FiniteResponseBound (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (L : ℝ) : Prop :=
  ∀ (e : I) (n : ℕ) (h h' : I → ℝ) (D : ℝ), 0 ≤ D →
    (∀ i ∈ S e n, |h i - h' i| ≤ D) →
    |finiteTiltMean μ (S e n) h e - finiteTiltMean μ (S e n) h' e| ≤ L * D

theorem drift_response (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    {L : ℝ} (hresponse : FiniteResponseBound μ S L)
    (t : ℝ) (y y' : I → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hdiff : ∀ i, |y i - y' i| ≤ D) (e : I) :
    |drift μ S t y e - drift μ S t y' e| ≤ L * D := by
  apply CanonicalDrift.abs_outerLimit_sub_le (b := finiteStage μ S e)
    (fun n (p : ℝ × (I → ℝ)) =>
      finiteTiltMean_mem_Icc μ (S e n) (fun i => p.2 i - p.1 / 2) e)
  intro n
  apply hresponse e n _ _ D hD
  intro i hi
  simpa only [sub_sub_sub_cancel_right] using hdiff i

theorem finiteResponseBound_of_tendsto
    {J : Type*} {l : Filter J} [l.NeBot]
    {μs : J → ProbabilityMeasure (I → Bool)} {μ : ProbabilityMeasure (I → Bool)}
    (hμ : Tendsto μs l (𝓝 μ)) (S : I → ℕ → Finset I) {L : ℝ}
    (hb : ∀ᶠ j in l, FiniteResponseBound (μs j) S L) : FiniteResponseBound μ S L := by
  intro e n h h' D hD hdiff
  exact finiteTiltMean_response_bound_of_tendsto hμ (S e n) h h' e
    (hb.mono (fun j hj => hj e n h h' D hD hdiff))

theorem measurable_drift_evaluation [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I) :
    Measurable (fun p : (ℝ × (I → ℝ)) × I => drift μ S p.1.1 p.1.2 p.2) :=
  measurable_from_prod_countable_left (fun e => measurable_drift_coordinate μ S e)

omit [Countable I] in

theorem drift_reindex {J : Type*} [Countable J] (σ : I ≃ J)
    (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (S' : J → ℕ → Finset J)
    (hS : ∀ e n, S' (σ e) n = (S e n).map σ.toEmbedding)
    (t : ℝ) (y : I → ℝ) (e : I) :
    drift (μ.map (reindex σ)) S'
      t (fun j => y (σ.symm j)) (σ e) = drift μ S t y e := by
  unfold drift CanonicalDrift.outerLimit
  apply limsup_congr
  apply Eventually.of_forall
  intro n
  dsimp only [finiteStage]
  rw [hS e n]
  exact finiteTiltMean_reindex σ μ (S e n) (fun i => y i - t / 2) e

omit [Countable I] in

theorem drift_eq_of_tendsto (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I) (t : ℝ) (y : I → ℝ) (e : I) {a : ℝ}
    (h : Tendsto (fun n => finiteTiltMean μ (S e n) (fun i => y i - t / 2) e)
      atTop (𝓝 a)) : drift μ S t y e = a :=
  h.limsup_eq

end Problem336.PosteriorDrift

end

end OAI
