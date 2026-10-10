import OAI.Probability.MatroidSecretary.Pivots.MarkedTransactions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace OAI

/-!
# Almost-surely lawful auxiliary-seed transaction policies

The independent auxiliary seed may live in an arbitrary probability space.
Freshness and certificate soundness are needed only almost surely in that seed,
and soundness in the bit vector is needed only on positive-probability vectors.
The iterated expectation expresses the independent product experiment; its
integrability is proved, not assumed. No uniform bound on the sizes of the
seed-indexed finite trees is needed.
-/

namespace MatroidProphet.MarkedQueryProgram

open Finset MeasureTheory

/-- The source logarithmic budget for an arbitrary independent auxiliary seed,
including null exceptional seeds and deterministic Bernoulli coordinates. -/
theorem disjoint_query_certificates_auxiliary_ae
    {α : Type*} [DecidableEq α] [Fintype α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (prog : Ω → MarkedQueryProgram α)
    (fresh : ∀ᵐ ω ∂μ, (prog ω).Fresh univ)
    (sound : ∀ᵐ ω ∂μ, ∀ S, 0 < bitsWeight q univ S → (prog ω).SoundAt cert S ∅)
    (meas : ∀ S, Measurable (fun ω => (prog ω).run S)) :
    Integrable (fun ω => bitsExpectation q univ (prog ω).run) μ ∧
      (∫ ω, bitsExpectation q univ (prog ω).run ∂μ) ≤
        Real.log (1 / bitsFailure cert q univ ∅) := by
  let f : Ω → ℝ := fun ω => bitsExpectation q univ (prog ω).run
  have hf0 (ω : Ω) : 0 ≤ f ω :=
    bitsExpectation_nonneg q hq0 hq1 univ (fun S _ => (prog ω).run_nonneg S)
  have hf1 : ∀ᵐ ω ∂μ, f ω ≤ Real.log (1 / bitsFailure cert q univ ∅) := by
    filter_upwards [fresh, sound] with ω hf hs
    exact (prog ω).disjoint_query_certificates_support cert hcert q hq0 hq1 hδ hf hs
  have hfm : Measurable f := by
    unfold f bitsExpectation
    exact Finset.measurable_sum _ fun S _ => measurable_const.mul (meas S)
  have hfi : Integrable f μ := by
    apply Integrable.of_bound hfm.aestronglyMeasurable
      (Real.log (1 / bitsFailure cert q univ ∅))
    filter_upwards [hf1] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)] using hω
  refine ⟨hfi, ?_⟩
  calc
    (∫ ω, f ω ∂μ) ≤ ∫ _ : Ω, Real.log (1 / bitsFailure cert q univ ∅) ∂μ :=
      integral_mono_ae hfi (integrable_const _) hf1
    _ = Real.log (1 / bitsFailure cert q univ ∅) := by simp

end MatroidProphet.MarkedQueryProgram

end OAI
