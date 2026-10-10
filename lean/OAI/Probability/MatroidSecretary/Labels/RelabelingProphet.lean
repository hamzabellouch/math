import OAI.Probability.MatroidSecretary.Labels.RelabelingProbability
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! An unconditional prophet witness on arbitrary finite labels, reusing the
canonical relabeling implementation. This supplies the existential endpoint
rather than requiring a hidden-rule performance hypothesis from the caller. -/

namespace MatroidProphet.Relabeling

open MeasureTheory ProbabilityTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {n : ℕ} [MeasurableSpace (LabeledOrder α n)] [MeasurableSingletonClass (LabeledOrder α n)]

/-- A distribution-independent measurable one-sample rule on the original
labels, with exact prefix feasibility and the full almighty-adversary bound.
The enumeration is fixed before all probability laws and realizations. -/
theorem exists_labeled_one_sample.{u} (M : Matroid α) (hE : M.E = Set.univ)
    (e : α ≃ Fin n) :
    ∃ (bits : ℕ) (ν : Measure (Seed bits)), IsProbabilityMeasure ν ∧
    ∃ (A : OnlineRule n bits),
      (∀ k : Fin n, Measurable (fun x : Seed bits × ((α → ℝ) × LabeledHistory α k) =>
        transportedDecision e A k x.1 x.2.1 x.2.2)) ∧
      (∀ (r : Seed bits) (s v : α → ℝ) (π : LabeledOrder α n) (t : ℕ),
        (∀ a, 0 ≤ s a) → (∀ a, 0 ≤ v a) →
        M.Indep (transportedAcceptedThrough e A r s v π t : Set α)) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (S V : Ω → α → ℝ) (R : Ω → Seed bits),
        Measurable S → Measurable V → Measurable R →
        (∀ᵐ ω ∂μ, ∀ a, 0 ≤ S ω a) →
        (∀ᵐ ω ∂μ, ∀ a, 0 ≤ V ω a) →
        iIndepFun (labeledPairedCoordinates S V) μ →
        (∀ a, μ.map (fun ω => S ω a) = μ.map (fun ω => V ω a)) →
        IndepFun (fun ω => (S ω, V ω)) R μ → μ.map R = ν →
        Integrable (fun ω => finiteOptimum M (V ω)) μ →
        ∀ (π : Ω → LabeledOrder α n), Measurable π →
          Integrable (fun ω => transportedReward e A (R ω) (S ω) (V ω) (π ω)) μ ∧
          ((2 : ℝ) ^ 310)⁻¹ * (∫ ω, finiteOptimum M (V ω) ∂μ) ≤
            ∫ ω, transportedReward e A (R ω) (S ω) (V ω) (π ω) ∂μ := by
  obtain ⟨bits, ν, hν, A, hA, hbound⟩ :=
    MatroidProphet.one_sample.{u} n (M.mapEquiv e) (mapEquiv_ground_univ M e hE)
  refine ⟨bits, ν, hν, A, measurable_transportedDecision e A, ?_, ?_⟩
  · exact transported_feasible M e A hA
  · intro Ω _ μ _ S V R hS hV hR hS0 hV0 hind hmatch hseed hlaw hint π hπ
    have ho (w : α → ℝ) :
        optimum (M.mapEquiv e) (encodeWeights e w) = finiteOptimum M w :=
      finiteOptimum_mapEquiv M e w
    have hS0' : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ encodeWeights e (S ω) i :=
      hS0.mono (fun _ h => (encodeWeights_nonnegative_iff e _).2 h)
    have hV0' : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ encodeWeights e (V ω) i :=
      hV0.mono (fun _ h => (encodeWeights_nonnegative_iff e _).2 h)
    have hint' : Integrable (fun ω => optimum (M.mapEquiv e) (encodeWeights e (V ω))) μ := by
      simpa only [ho] using hint
    have hb := hbound μ (fun ω => encodeWeights e (S ω))
      (fun ω => encodeWeights e (V ω)) R
      ((measurable_encodeWeights e).comp hS) ((measurable_encodeWeights e).comp hV) hR
      hS0' hV0' (paired_independent_encode e μ S V hind)
      (matching_laws_encode e μ S V hmatch) (seed_independent_encode e μ S V R hseed)
      hlaw hint' (fun ω => (π ω).trans e) (measurable_encoded_order e π hπ)
    simpa only [ho, transportedReward_eq_reward] using hb

end MatroidProphet.Relabeling

end OAI
