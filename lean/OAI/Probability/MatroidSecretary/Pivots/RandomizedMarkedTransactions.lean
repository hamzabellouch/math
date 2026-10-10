import OAI.Probability.MatroidSecretary.Pivots.MarkedTransactions
import OAI.Probability.MatroidSecretary.Pivots.CertificateAuxSeed
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace OAI

/-!
# The complete disjoint-query certificate contract

This is the independent-auxiliary-seed form of `lem:transactions`, with explicit
success declarations rather than counting every certifying transaction. The
inner finite product expectation has the original Bernoulli law for every seed.
Soundness is required only on bit vectors with positive product mass; this keeps
deterministic Bernoulli coordinates within scope without restricting impossible
executions. Integrability follows from the proved logarithmic budget.
-/

namespace MatroidProphet.MarkedQueryProgram

open Finset MeasureTheory

/-- On every sound execution with positive failure probability, successes are
bounded by the number of coordinates, even if the chosen finite tree contains
arbitrarily many empty or unsuccessful transactions. -/
lemma run_le_card_of_positive_failure
    {α : Type*} [Fintype α] [DecidableEq α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hδ : 0 < bitsFailure cert q univ ∅)
    (prog : MarkedQueryProgram α) (fresh : prog.Fresh univ)
    (S : Finset α) (sound : prog.SoundAt cert S ∅) :
    prog.run S ≤ (Fintype.card α : ℝ) := by
  have hempty : ¬ cert ∅ := by
    intro hc
    have hz := bitsFailure_certifies cert hcert q univ ∅ hc
    rw [hz] at hδ
    exact lt_irrefl 0 hδ
  have hu := prog.erase.run_le_card cert hempty S univ (prog.erase_fresh univ fresh)
  simpa using (prog.run_le_certifying_run cert S ∅ sound).trans hu

/-- Arbitrary independent auxiliary randomization preserves the certificate
budget for explicitly declared, sound successes. The source's uniform finite
transaction bound is not needed: each seed fixes a finite adaptive tree. -/
theorem disjoint_query_certificates_auxiliary
    {α : Type*} [Fintype α] [DecidableEq α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (prog : Ω → MarkedQueryProgram α)
    (fresh : ∀ ω, (prog ω).Fresh univ)
    (sound : ∀ ω S, 0 < bitsWeight q univ S → (prog ω).SoundAt cert S ∅)
    (meas : ∀ S, Measurable (fun ω => (prog ω).run S)) :
    Integrable (fun ω => bitsExpectation q univ (prog ω).run) μ ∧
    (∫ ω, bitsExpectation q univ (prog ω).run ∂μ) ≤
      Real.log (1 / bitsFailure cert q univ ∅) := by
  let f : Ω → ℝ := fun ω => bitsExpectation q univ (prog ω).run
  have hf0 (ω : Ω) : 0 ≤ f ω :=
    bitsExpectation_nonneg q hq0 hq1 univ
      (fun S _ => (prog ω).run_nonneg S)
  have hf1 (ω : Ω) : f ω ≤ Real.log (1 / bitsFailure cert q univ ∅) :=
    disjoint_query_certificates_support cert hcert q hq0 hq1 hδ
      (prog ω) (fresh ω) (sound ω)
  have hfm : Measurable f := by
    unfold f bitsExpectation
    exact Finset.measurable_sum _ fun S _ => measurable_const.mul (meas S)
  have hfi : Integrable f μ := by
    apply Integrable.of_bound hfm.aestronglyMeasurable
      (Real.log (1 / bitsFailure cert q univ ∅))
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]
      exact hf1 ω
  refine ⟨hfi, ?_⟩
  calc
    (∫ ω, f ω ∂μ) ≤ ∫ _ : Ω, Real.log (1 / bitsFailure cert q univ ∅) ∂μ :=
      integral_mono hfi (integrable_const _) hf1
    _ = Real.log (1 / bitsFailure cert q univ ∅) := by simp

end MatroidProphet.MarkedQueryProgram

end OAI
