import OAI.Probability.MatroidProphet.Main
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

open MeasureTheory

namespace MatroidProphet

/-- For a fixed vector, arbitrary measurable seed-dependent orders give an
integrable reward under every finite measure. No feasibility or sign assumption
is needed, since the seed and order spaces are finite. -/
lemma integrable_hiddenReward_randomOrder {n bits : ℕ} (A : HiddenRule n bits)
    (w : Weights n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Ω → Seed bits) (π : Ω → ArrivalOrder n)
    (hR : Measurable R) (hπ : Measurable π) :
    Integrable (fun ω => hiddenReward A (R ω) w (π ω)) μ := by
  let f : Seed bits × ArrivalOrder n → ℝ := fun x => hiddenReward A x.1 w x.2
  have hf : Measurable f := measurable_of_finite f
  have hpair : Measurable (fun ω => (R ω, π ω)) := hR.prodMk hπ
  exact (integrable_map_measure hf.aestronglyMeasurable hpair.aemeasurable).1
    (Integrable.of_finite (f := f))

/-- The seedwise minimum is integrable after any measurable finite-seed map. -/
lemma integrable_hiddenWorstReward_comp {n bits : ℕ} (A : HiddenRule n bits)
    (w : Weights n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Ω → Seed bits) (hR : Measurable R) :
    Integrable (fun ω => hiddenWorstReward A w (R ω)) μ := by
  have hf : Measurable (hiddenWorstReward A w) := measurable_of_finite _
  exact (integrable_map_measure hf.aestronglyMeasurable hR.aemeasurable).1
    (Integrable.of_finite (f := hiddenWorstReward A w))

/-- A reconstructed seed's correct marginal transports the expected minimum to
any measurable full-information order. The order need not be independent of the
seed, and the ambient space may carry arbitrarily much additional information. -/
theorem hiddenWorstReward_integral_le_randomOrder {n bits : ℕ}
    (A : HiddenRule n bits) (w : Weights n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : Measure (Seed bits)) (R : Ω → Seed bits) (π : Ω → ArrivalOrder n)
    (hR : Measurable R) (hπ : Measurable π) (hRlaw : μ.map R = ν) :
    (∫ r, hiddenWorstReward A w r ∂ν) ≤
      ∫ ω, hiddenReward A (R ω) w (π ω) ∂μ := by
  have hf : Measurable (hiddenWorstReward A w) := measurable_of_finite _
  rw [← hRlaw, integral_map_of_stronglyMeasurable hR hf.stronglyMeasurable]
  apply integral_mono
    (integrable_hiddenWorstReward_comp A w μ R hR)
    (integrable_hiddenReward_randomOrder A w μ R π hR hπ)
  intro ω
  exact hiddenWorstReward_le A w (R ω) (π ω)

/-- A pointwise accepted-reward identity may be replaced by an almost-everywhere
identity. This is useful when a reconstruction kernel has zero-mass seed outcomes. -/
theorem hiddenWorstReward_integral_le_replayed {n bits : ℕ}
    (A : HiddenRule n bits) (w : Weights n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ν : Measure (Seed bits)) (R : Ω → Seed bits) (π : Ω → ArrivalOrder n)
    (hR : Measurable R) (hπ : Measurable π) (hRlaw : μ.map R = ν)
    (payoff : Ω → ℝ)
    (hreplay : payoff =ᵐ[μ] fun ω => hiddenReward A (R ω) w (π ω)) :
    Integrable payoff μ ∧ (∫ r, hiddenWorstReward A w r ∂ν) ≤ ∫ ω, payoff ω ∂μ := by
  refine ⟨(integrable_hiddenReward_randomOrder A w μ R π hR hπ).congr hreplay.symm, ?_⟩
  rw [integral_congr_ae hreplay]
  exact hiddenWorstReward_integral_le_randomOrder A w μ ν R π hR hπ hRlaw

/-- There is a measurable adversary attaining the minimum separately at every
seed. Thus the minimum used above is genuinely inside expectation, not the
minimum of fixed-order expected rewards. -/
lemma exists_measurable_worstOrder {n bits : ℕ} (A : HiddenRule n bits)
    (w : Weights n) :
    ∃ π : Seed bits → ArrivalOrder n, Measurable π ∧
      ∀ r, hiddenReward A r w (π r) = hiddenWorstReward A w r := by
  classical
  have hex (r : Seed bits) :
      ∃ π : ArrivalOrder n, hiddenReward A r w π = hiddenWorstReward A w r := by
    obtain ⟨π, _, hπ⟩ := Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (ArrivalOrder n))) Finset.univ_nonempty
      (hiddenReward A r w)
    exact ⟨π, hπ.symm⟩
  choose π hπ using hex
  exact ⟨π, measurable_of_finite π, hπ⟩

/-- The lower bound is sharp among measurable full-seed order policies. -/
lemma exists_order_integral_eq_hiddenWorstReward {n bits : ℕ}
    (A : HiddenRule n bits) (w : Weights n) (ν : Measure (Seed bits)) :
    ∃ π : Seed bits → ArrivalOrder n, Measurable π ∧
      (∫ r, hiddenReward A r w (π r) ∂ν) = ∫ r, hiddenWorstReward A w r ∂ν := by
  obtain ⟨π, hπ, heq⟩ := exists_measurable_worstOrder A w
  exact ⟨π, hπ, integral_congr_ae (ae_of_all _ heq)⟩

end MatroidProphet

end OAI
