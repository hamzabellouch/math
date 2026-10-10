import OAI.Probability.MatroidSecretary.Labels.FiniteLabelTransport
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# The one-sample endpoint on arbitrary finite labels

This is supporting transport for `thm:main`, not a new manuscript target.
The enumeration is fixed from the label type before the input distributions.
All labels, including loops, and all probability/online-information hypotheses
are retained.  The probability-space universe is independent of the label
universe.  No moment assumption on individual loop values is introduced.
-/

namespace MatroidProphet.Labeling

open MeasureTheory ProbabilityTheory

variable {E : Type*} [Fintype E]

lemma measurable_finWeights : Measurable (finWeights (E := E)) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply ((Fintype.equivFin E).symm i)

lemma paired_independent_finWeights {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S V : Ω → E → ℝ)
    (hi : iIndepFun (fun i : E × Bool =>
      if i.2 then fun ω => S ω i.1 else fun ω => V ω i.1) μ) :
    iIndepFun (pairedCoordinates (fun ω => finWeights (S ω))
      (fun ω => finWeights (V ω))) μ := by
  have h := hi.precomp (Equiv.prodCongr
    (Fintype.equivFin E).symm (Equiv.refl Bool)).injective
  change iIndepFun (fun i : Fin (Fintype.card E) × Bool =>
    if i.2 then fun ω => S ω ((Fintype.equivFin E).symm i.1)
      else fun ω => V ω ((Fintype.equivFin E).symm i.1)) μ
  simpa using h

/-- The complete distribution-independent prophet guarantee after a fixed
renaming of arbitrary finite labels.  The order may depend on the full seed,
all samples, all values, and any other randomness in the probability space. -/
theorem one_sample_finite_labels.{u, v} {E : Type v} [Fintype E]
    [MeasurableSpace E] [MeasurableSingletonClass E]
    (M : Matroid E) (hE : M.E = Set.univ) :
    ∃ (bits : ℕ) (ν : Measure (Seed bits)), IsProbabilityMeasure ν ∧
    ∃ A : LabeledOnlineRule E bits,
      (∀ (r : Seed bits) (s v : E → ℝ) (π : LabeledOrder E) (t : ℕ),
        (∀ e, 0 ≤ s e) → (∀ e, 0 ≤ v e) →
        M.Indep (labeledAcceptedThrough A r s v π t : Set E)) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (S V : Ω → E → ℝ) (R : Ω → Seed bits),
        Measurable S → Measurable V → Measurable R →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e) →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e) →
        iIndepFun (fun i : E × Bool =>
          if i.2 then fun ω => S ω i.1 else fun ω => V ω i.1) μ →
        (∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e)) →
        IndepFun (fun ω => (S ω, V ω)) R μ → μ.map R = ν →
        Integrable (fun ω => finiteOptimum M (V ω)) μ →
        ∀ π : Ω → LabeledOrder E, Measurable π →
          Integrable (fun ω => ∑ e ∈ labeledAcceptedThrough A
            (R ω) (S ω) (V ω) (π ω) (Fintype.card E), V ω e) μ ∧
          ((2 : ℝ) ^ 310)⁻¹ * (∫ ω, finiteOptimum M (V ω) ∂μ) ≤
            ∫ ω, ∑ e ∈ labeledAcceptedThrough A
              (R ω) (S ω) (V ω) (π ω) (Fintype.card E), V ω e ∂μ := by
  obtain ⟨bits, ν, hν, A, hA, hbound⟩ :=
    MatroidProphet.one_sample.{u} (Fintype.card E) (finMatroid M)
      (finMatroid_ground M hE)
  refine ⟨bits, ν, hν, relabelRule A, relabelRule_feasible M A hA, ?_⟩
  intro Ω mΩ μ hμ S V R hS hV hR hSN hVN hi hlaw hseed hRlaw hopt π hπ
  have hSN' : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ finWeights (S ω) i :=
    hSN.mono fun _ h => (finWeights_nonnegative_iff _).2 h
  have hVN' : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ finWeights (V ω) i :=
    hVN.mono fun _ h => (finWeights_nonnegative_iff _).2 h
  have hseed' : IndepFun
      (fun ω => (finWeights (S ω), finWeights (V ω))) R μ := by
    exact hseed.comp ((measurable_finWeights.comp measurable_fst).prodMk
      (measurable_finWeights.comp measurable_snd)) measurable_id
  have hπ' : Measurable
      (fun ω => (π ω).trans (Fintype.equivFin E)) :=
    (measurable_of_countable
      (fun p : LabeledOrder E => p.trans (Fintype.equivFin E))).comp hπ
  have hopt' : Integrable
      (fun ω => optimum (finMatroid M) (finWeights (V ω))) μ := by
    simpa only [optimum_finMatroid] using hopt
  have hb := hbound μ (fun ω => finWeights (S ω))
    (fun ω => finWeights (V ω)) R (measurable_finWeights.comp hS)
    (measurable_finWeights.comp hV) hR hSN' hVN'
    (paired_independent_finWeights μ S V hi)
    (fun i => hlaw ((Fintype.equivFin E).symm i)) hseed' hRlaw hopt'
    (fun ω => (π ω).trans (Fintype.equivFin E)) hπ'
  simpa only [relabelRule_reward, optimum_finMatroid] using hb

end MatroidProphet.Labeling

end OAI
