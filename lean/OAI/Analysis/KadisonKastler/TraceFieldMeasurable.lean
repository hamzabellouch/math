import OAI.Analysis.KadisonKastler.BoundaryDiagonal
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

namespace OAI

/-! # Measurable operator fields from their tracial Hilbert realizations

On an operator-norm bounded ball, trace two-norm convergence implies
strong operator convergence. Thus a measurable trace-Hilbert field gives
measurable Hilbert-valued evaluations in the original representation.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

variable {D H E : Type*} [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}

/-- Strong-operator evaluation is continuous on a bounded trace-Hilbert ball. -/
theorem continuous_traceBall_eval (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) {C : ℝ} (hC : 0 ≤ C)
    (lift : (J '' Metric.closedBall (0 : Algebra M) C) → Algebra M)
    (hlift : ∀ z, J (lift z) = z.val ∧ ‖lift z‖ ≤ C) (ξ : H) :
    Continuous (fun z => (lift z : H →L[ℂ] H) ξ) := by
  apply Metric.continuous_iff.mpr
  intro z ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hτ.strongContinuous ξ (2 * C) (by positivity) ε hε
  refine ⟨δ, hδ, fun w hw => ?_⟩
  have hnorm : ‖lift w - lift z‖ ≤ 2 * C := by
    have h := (norm_sub_le (lift w) (lift z)).trans
      (add_le_add (hlift w).2 (hlift z).2)
    linarith
  have htwo : traceTwoNorm τ (lift w - lift z) < δ := by
    rw [← hJ, map_sub, (hlift w).1, (hlift z).1]
    simpa only [Subtype.dist_eq, dist_eq_norm] using hw
  have hs := hsmall (lift w - lift z) hnorm htwo
  change ‖(lift w : H →L[ℂ] H) ξ - (lift z : H →L[ℂ] H) ξ‖ < ε at hs
  simpa only [dist_eq_norm] using hs

/-- A globally bounded algebra field measurable in its trace Hilbert
space is strongly measurable after evaluation at any Hilbert vector. -/
theorem aestronglyMeasurable_operator_eval_of_trace [SeparableSpace H]
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) {μ : Measure D}
    (a : D → Algebra M) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ x, ‖a x‖ ≤ C)
    (hmeas : AEStronglyMeasurable (fun x => J (a x)) μ) (ξ : H) :
    AEStronglyMeasurable (fun x => (a x : H →L[ℂ] H) ξ) μ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let S : Set E := J '' Metric.closedBall (0 : Algebra M) C
  have hs (z : S) : ∃ b : Algebra M, J b = z.val ∧ ‖b‖ ≤ C := by
    obtain ⟨b, hb, he⟩ := z.property
    exact ⟨b, he, by simpa only [Metric.mem_closedBall, dist_zero_right] using hb⟩
  choose lift hlift using hs
  let f : D → S := fun x => ⟨J (a x), ⟨a x, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using ha x, rfl⟩⟩
  have hf : AEMeasurable f μ := hmeas.aemeasurable.subtype_mk
  have he := continuous_traceBall_eval J hJ hτ hC lift hlift ξ
  have hm : AEStronglyMeasurable (fun x => (lift (f x) : H →L[ℂ] H) ξ) μ :=
    (he.measurable.comp_aemeasurable hf).aestronglyMeasurable
  apply hm.congr
  exact Filter.Eventually.of_forall fun x => by
    have hax : lift (f x) = a x := traceHilbert_injective J hJ (hlift (f x)).1
    exact congrArg (fun b : Algebra M => (b : H →L[ℂ] H) ξ) hax

/-- In particular all scalar matrix coefficients are measurable. -/
theorem aestronglyMeasurable_operator_coefficient_of_trace [SeparableSpace H]
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) {μ : Measure D}
    (a : D → Algebra M) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ x, ‖a x‖ ≤ C)
    (hmeas : AEStronglyMeasurable (fun x => J (a x)) μ) (ξ η : H) :
    AEStronglyMeasurable (fun x => inner ℂ η ((a x : H →L[ℂ] H) ξ)) μ :=
  (aestronglyMeasurable_operator_eval_of_trace J hJ hτ a hC ha hmeas ξ).const_inner

end

end KadisonKastler

end OAI
