import OAI.Probability.MatroidSecretary.Labels.LabeledTransport
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! The indexed endpoint transported to any finite labeled ground type. The
encoding is fixed from the labels alone, before distributions and randomness.
No representability, positive-rank, atomlessness, or per-label moment premise
is introduced. This is optional source-correspondence support. -/

namespace MatroidProphet.LabeledTransport

open MeasureTheory ProbabilityTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

def pairedCoordinates {Ω : Type*} (S V : Ω → α → ℝ) (i : α × Bool) : Ω → ℝ :=
  if i.2 then fun ω => S ω i.1 else fun ω => V ω i.1

/-- The main guarantee on arbitrary finite physical labels, with a measurable
history-only rule and the same all-prefix feasibility and arbitrary-law bound. -/
theorem one_sample.{u} (M : Matroid α) (hE : M.E = Set.univ) :
    ∃ (bits : ℕ) (ν : Measure (Seed bits)), IsProbabilityMeasure ν ∧
    ∃ (A : OnlineRule α (Fintype.card α) bits),
      (∀ (r : Seed bits) (s v : α → ℝ) (π : ArrivalOrder α (Fintype.card α)) (t : ℕ),
        (∀ a, 0 ≤ s a) → (∀ a, 0 ≤ v a) →
        M.Indep (acceptedThrough A r s v π t : Set α)) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (S V : Ω → α → ℝ) (R : Ω → Seed bits),
        Measurable S → Measurable V → Measurable R →
        (∀ᵐ ω ∂μ, ∀ a, 0 ≤ S ω a) →
        (∀ᵐ ω ∂μ, ∀ a, 0 ≤ V ω a) →
        iIndepFun (pairedCoordinates S V) μ →
        (∀ a, Measure.map (fun ω => S ω a) μ = Measure.map (fun ω => V ω a) μ) →
        IndepFun (fun ω => (S ω, V ω)) R μ →
        Measure.map R μ = ν →
        Integrable (fun ω => optimum M (V ω)) μ →
        ∀ (π : Ω → ArrivalOrder α (Fintype.card α)), Measurable π →
          Integrable (fun ω => reward A (R ω) (S ω) (V ω) (π ω)) μ ∧
          ((2 : ℝ) ^ 310)⁻¹ * (∫ ω, optimum M (V ω) ∂μ) ≤
            ∫ ω, reward A (R ω) (S ω) (V ω) (π ω) ∂μ := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  obtain ⟨bits, ν, hν, A, hA, hperf⟩ :=
    MatroidProphet.one_sample.{u} (Fintype.card α) (M.mapEquiv e) (mapEquiv_ground M hE e)
  refine ⟨bits, ν, hν, decodeRule e A, ?_, ?_⟩
  · intro r s v π t hs hv
    exact decode_feasible M e A hA r s v π t hs hv
  · intro Ω _ μ _ S V R hS hV hR hS0 hV0 hind hmatch hseed hlaw hint π hπ
    let S' : Ω → Weights (Fintype.card α) := fun ω => S ω ∘ e.symm
    let V' : Ω → Weights (Fintype.card α) := fun ω => V ω ∘ e.symm
    have hS' : Measurable S' := by
      apply Measurable.of_eval
      intro i
      exact (measurable_pi_apply (e.symm i)).comp hS
    have hV' : Measurable V' := by
      apply Measurable.of_eval
      intro i
      exact (measurable_pi_apply (e.symm i)).comp hV
    have hS0' : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ S' ω i :=
      hS0.mono (fun _ h i => h (e.symm i))
    have hV0' : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ V' ω i :=
      hV0.mono (fun _ h i => h (e.symm i))
    have hind' : iIndepFun (MatroidProphet.pairedCoordinates S' V') μ := by
      have h := hind.precomp (g := fun i : Fin (Fintype.card α) × Bool => (e.symm i.1, i.2))
        (by
          intro i j hij
          apply Prod.ext
          · exact e.symm.injective (congrArg Prod.fst hij)
          · exact congrArg (fun p : α × Bool => p.2) hij)
      exact h
    have hmap : Measurable (fun x : (α → ℝ) × (α → ℝ) =>
        (x.1 ∘ e.symm, x.2 ∘ e.symm)) := by
      apply Measurable.prodMk
      · apply Measurable.of_eval
        intro i
        exact (measurable_pi_apply (e.symm i)).comp measurable_fst
      · apply Measurable.of_eval
        intro i
        exact (measurable_pi_apply (e.symm i)).comp measurable_snd
    have hseed' : IndepFun (fun ω => (S' ω, V' ω)) R μ :=
      hseed.comp hmap measurable_id
    have hint' : Integrable (fun ω => MatroidProphet.optimum (M.mapEquiv e) (V' ω)) μ := by
      simpa only [optimum_eq_indexed M e, V'] using hint
    have hπ' : Measurable (fun ω => (π ω).trans e) :=
      (measurable_of_finite (fun p : ArrivalOrder α (Fintype.card α) => p.trans e)).comp hπ
    have h := hperf μ S' V' R hS' hV' hR hS0' hV0' hind'
      (fun i => hmatch (e.symm i)) hseed' hlaw hint' (fun ω => (π ω).trans e) hπ'
    simpa only [decode_reward, optimum_eq_indexed M e, S', V'] using h

end MatroidProphet.LabeledTransport

end OAI
