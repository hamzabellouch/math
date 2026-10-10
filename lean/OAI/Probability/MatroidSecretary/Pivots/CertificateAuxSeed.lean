import OAI.Probability.MatroidProphet.Main
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace OAI

/-!
# Disjoint-query certificates with an independent auxiliary seed

The source lemma `lem:transactions` permits an arbitrary independent auxiliary
seed. After fixing that seed the procedure is a fresh finite query tree. The
product-bit expectation below is then averaged over the seed law. In particular
the program may depend on the seed, but the Bernoulli parameters do not.

No integrability assumption on the count is needed: nonnegativity and the
pointwise logarithmic budget prove its integrability. The measurable-count
hypothesis expresses measurability of the seed-dependent procedure.
-/

namespace MatroidProphet

open Finset MeasureTheory

variable {α : Type*} [DecidableEq α]

lemma QueryProgram.run_nonneg (cert : Finset α → Prop) [DecidablePred cert]
    (prog : QueryProgram α) (S I : Finset α) :
    0 ≤ prog.run cert S I := by
  induction prog generalizing I with
  | stop => simp [QueryProgram.run]
  | finish rest ih =>
    simp only [QueryProgram.run]
    exact add_nonneg (by split_ifs <;> norm_num) (ih ∅)
  | query e no yes ihn ihy =>
    simp only [QueryProgram.run]
    split_ifs
    · exact ihy (insert e I)
    · exact ihn I

/-- With no empty certificate, each successful transaction consumes at least one
new positive query. The extra unit allows a nonempty transaction already in
progress. This bound is independent of the number of transaction boundaries. -/
lemma QueryProgram.run_le_card_add (cert : Finset α → Prop) [DecidablePred cert]
    (hempty : ¬ cert ∅) (prog : QueryProgram α) (S V I : Finset α)
    (fresh : prog.Fresh V) :
    prog.run cert S I ≤ (V.card : ℝ) + if I.Nonempty then 1 else 0 := by
  induction prog generalizing V I with
  | stop =>
    simp only [QueryProgram.run]
    positivity
  | finish rest ih =>
    have hr := ih V ∅ fresh
    simp only [Finset.not_nonempty_empty, ↓reduceIte, add_zero] at hr
    simp only [QueryProgram.run]
    by_cases hc : cert I
    · have hi : I.Nonempty := by
        by_contra h
        have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        exact hempty (he ▸ hc)
      simp only [ite_eq_left hc, ite_eq_left hi]
      linarith
    · simp only [ite_eq_right hc, zero_add]
      exact hr.trans (le_add_of_nonneg_right (by split_ifs <;> norm_num))
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have hcard : ((V.erase e).card : ℝ) + 1 = V.card := by
      exact_mod_cast Finset.card_erase_add_one he
    simp only [QueryProgram.run]
    by_cases hes : e ∈ S
    · rw [ite_eq_left hes]
      have hyb := ihy (V.erase e) (insert e I) hy
      simp only [Finset.insert_nonempty, ↓reduceIte] at hyb
      rw [hcard] at hyb
      exact hyb.trans (le_add_of_nonneg_right (by split_ifs <;> norm_num))
    · rw [ite_eq_right hes]
      have hnb := ihn (V.erase e) I hn
      linarith

lemma QueryProgram.run_le_card (cert : Finset α → Prop) [DecidablePred cert]
    (hempty : ¬ cert ∅) (prog : QueryProgram α) (S V : Finset α)
    (fresh : prog.Fresh V) : prog.run cert S ∅ ≤ (V.card : ℝ) := by
  simpa using prog.run_le_card_add cert hempty S V ∅ fresh

/-- Averaging the actual product-bit count over any independent auxiliary seed
preserves the source logarithmic certificate budget. This also proves that the
averaged random variable is integrable. -/
theorem disjoint_query_certificates_auxiliary [Fintype α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (prog : Ω → QueryProgram α) (fresh : ∀ ω, (prog ω).Fresh univ)
    (meas : ∀ S, Measurable (fun ω => (prog ω).run cert S ∅)) :
    Integrable (fun ω => bitsExpectation q univ
      (fun S => (prog ω).run cert S ∅)) μ ∧
    (∫ ω, bitsExpectation q univ (fun S => (prog ω).run cert S ∅) ∂μ) ≤
      Real.log (1 / bitsFailure cert q univ ∅) := by
  let f : Ω → ℝ := fun ω => bitsExpectation q univ
    (fun S => (prog ω).run cert S ∅)
  have hf0 (ω : Ω) : 0 ≤ f ω :=
    bitsExpectation_nonneg q hq0 hq1 univ
      (fun S _ => (prog ω).run_nonneg cert S ∅)
  have hf1 (ω : Ω) : f ω ≤ Real.log (1 / bitsFailure cert q univ ∅) :=
    disjoint_query_certificates_product cert hcert q hq0 hq1 hδ (prog ω) (fresh ω)
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

end MatroidProphet

end OAI
