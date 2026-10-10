import OAI.Probability.MatroidSecretary.Labels.RelabelingTheorems
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Probability-law reindexing, including the full-seed almighty-adversary
simulation, on arbitrary finite label types. -/

namespace MatroidProphet.Relabeling

open MeasureTheory ProbabilityTheory

variable {α : Type*} {n bits : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Mutual independence of all paired source coordinates is preserved exactly by labeling. -/
theorem paired_independent_encode (e : α ≃ Fin n) (μ : Measure Ω)
    (S V : Ω → α → ℝ) (hi : iIndepFun (labeledPairedCoordinates S V) μ) :
    iIndepFun (pairedCoordinates (fun ω => encodeWeights e (S ω))
      (fun ω => encodeWeights e (V ω))) μ := by
  let f : (Fin n × Bool) → α × Bool := fun i => (e.symm i.1, i.2)
  have hf : Function.Injective f := by
    intro x y h
    apply Prod.ext
    · exact e.symm.injective (congrArg Prod.fst h)
    · exact congrArg (fun z : α × Bool => z.2) h
  have hp : iIndepFun (fun i : Fin n × Bool => labeledPairedCoordinates S V (f i)) μ :=
    iIndepFun.precomp (g := f) hf hi
  exact hp

/-- Joint independence from the complete seed survives reindexing both vectors. -/
theorem seed_independent_encode (e : α ≃ Fin n) (μ : Measure Ω)
    (S V : Ω → α → ℝ) (R : Ω → Seed bits)
    (h : IndepFun (fun ω => (S ω, V ω)) R μ) :
    IndepFun (fun ω => (encodeWeights e (S ω), encodeWeights e (V ω))) R μ := by
  exact h.comp
    (((measurable_encodeWeights e).comp measurable_fst).prodMk
      ((measurable_encodeWeights e).comp measurable_snd)) measurable_id

/-- Enumeration changes no observed coordinate law. -/
theorem matching_laws_encode (e : α ≃ Fin n) (μ : Measure Ω)
    (S V : Ω → α → ℝ)
    (h : ∀ a, μ.map (fun ω => S ω a) = μ.map (fun ω => V ω a)) :
    ∀ i, μ.map (fun ω => encodeWeights e (S ω) i) =
      μ.map (fun ω => encodeWeights e (V ω) i) := by
  intro i
  exact h (e.symm i)

/-- No independence is imposed on the order when changing its label representation. -/
theorem measurable_encoded_order [Fintype α]
    [MeasurableSpace (LabeledOrder α n)] [MeasurableSingletonClass (LabeledOrder α n)]
    (e : α ≃ Fin n) (π : Ω → LabeledOrder α n) (hπ : Measurable π) :
    Measurable (fun ω => (π ω).trans e) :=
  (measurable_of_finite (fun p : LabeledOrder α n => p.trans e)).comp hπ

/-- Full one-sample expected-minimum simulation on original finite labels.
The hypotheses are exactly the hidden-rule guarantee and source probability
hypotheses; in particular the adversarial permutation need not be independent
of any sample, value, or seed information. -/
theorem oneSample_of_hidden_labeled [Fintype α]
    [MeasurableSpace (LabeledOrder α n)] [MeasurableSingletonClass (LabeledOrder α n)]
    (M : Matroid α) (e : α ≃ Fin n) (A : HiddenRule n bits)
    (ν : Measure (Seed bits)) [IsProbabilityMeasure ν] (c : ℝ)
    (hA : ∀ (w : Weights n), (∀ i, 0 ≤ w i) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        (M.mapEquiv e).Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hbound : ∀ (w : Weights n), (∀ i, 0 ≤ w i) →
      c * optimum (M.mapEquiv e) w ≤ ∫ r, hiddenWorstReward A w r ∂ν)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S V : Ω → α → ℝ) (R : Ω → Seed bits)
    (hS : Measurable S) (hV : Measurable V) (hR : Measurable R)
    (hSN : ∀ᵐ ω ∂μ, ∀ a, 0 ≤ S ω a) (hVN : ∀ᵐ ω ∂μ, ∀ a, 0 ≤ V ω a)
    (hi : iIndepFun (labeledPairedCoordinates S V) μ)
    (hlaw : ∀ a, μ.map (fun ω => S ω a) = μ.map (fun ω => V ω a))
    (hseed : IndepFun (fun ω => (S ω, V ω)) R μ)
    (hRlaw : μ.map R = ν)
    (hopt : Integrable (fun ω => finiteOptimum M (V ω)) μ)
    (π : Ω → LabeledOrder α n) (hπ : Measurable π) :
    Integrable (fun ω => transportedReward e (sampleSimulation A)
      (R ω) (S ω) (V ω) (π ω)) μ ∧
    c * (∫ ω, finiteOptimum M (V ω) ∂μ) ≤
      ∫ ω, transportedReward e (sampleSimulation A) (R ω) (S ω) (V ω) (π ω) ∂μ := by
  have ho (w : α → ℝ) : optimum (M.mapEquiv e) (encodeWeights e w) =
      finiteOptimum M w := finiteOptimum_mapEquiv M e w
  have hsN : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ encodeWeights e (S ω) i := by
    filter_upwards [hSN] with ω hω
    exact (encodeWeights_nonnegative_iff e (S ω)).2 hω
  have hvN : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ encodeWeights e (V ω) i := by
    filter_upwards [hVN] with ω hω
    exact (encodeWeights_nonnegative_iff e (V ω)).2 hω
  have hopt' : Integrable (fun ω => optimum (M.mapEquiv e) (encodeWeights e (V ω))) μ := by
    simpa only [ho] using hopt
  have h := oneSample_of_hidden (M.mapEquiv e) A ν c hA hbound μ
    (fun ω => encodeWeights e (S ω)) (fun ω => encodeWeights e (V ω)) R
    ((measurable_encodeWeights e).comp hS) ((measurable_encodeWeights e).comp hV) hR
    hsN hvN (paired_independent_encode e μ S V hi) (matching_laws_encode e μ S V hlaw)
    (seed_independent_encode e μ S V R hseed) hRlaw hopt'
    (fun ω => (π ω).trans e) (measurable_encoded_order e π hπ)
  simpa only [ho, transportedReward_eq_reward] using h

end MatroidProphet.Relabeling

end OAI
