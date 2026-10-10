import OAI.Combinatorics.Ryser.Construction.GadgetOriginalCounts
import OAI.Combinatorics.Ryser.Geometry.Cardinality
import OAI.Combinatorics.Ryser.Probability.Product

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

private theorem expectation_finset_sum
    {Ω ι : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.expectation (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, μ.expectation (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, FiniteLaw.expectation_const]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, FiniteLaw.expectation_add, ih]

theorem card_nonzeroSlope :
    Fintype.card (NonzeroSlope k) = Fintype.card k - 1 := by
  change Fintype.card {e : k // ¬e = 0} = _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem prob_originalPoint_survival (d : NonzeroSlope k) (w : Point k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => ∀ e, e ≠ d → ¬Incidence w (omittedLine a e)) =
      (1 - 1 / (Fintype.card k : ℝ)) ^ (Fintype.card k - 2) := by
  classical
  have hsingle (e : NonzeroSlope k) :
      (FiniteLaw.uniform k).prob
          (fun z : k => Incidence w (some e.val, z)) =
        1 / (Fintype.card k : ℝ) := by
    rw [FiniteLaw.prob]
    rw [Finset.sum_eq_single_of_mem
      (projection (some e.val) w) (Finset.mem_univ _)]
    · simp [Incidence, FiniteLaw.uniform, one_div]
    · intro b _ hb
      apply ite_eq_right
      intro h
      exact hb (show projection (some e.val) w = b from h).symm
  have hcoord (e : NonzeroSlope k) :
      (FiniteLaw.uniform k).prob
          (fun z : k => e ≠ d → ¬Incidence w (some e.val, z)) =
        if e = d then 1 else 1 - 1 / (Fintype.card k : ℝ) := by
    by_cases he : e = d
    · simp [he]
    · simp only [ne_eq, he, not_false_eq_true, true_implies, ite_false]
      rw [FiniteLaw.prob_compl, hsingle e]
  change
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => ∀ e, e ≠ d → ¬Incidence w (some e.val, a e)) = _
  rw [FiniteLaw.prob_pi
    (A := fun _ : NonzeroSlope k => k)
    (fun _ : NonzeroSlope k => FiniteLaw.uniform k)
    (fun (e : NonzeroSlope k) (b : k) =>
      e ≠ d → ¬Incidence w (some e.val, b))]
  simp_rw [hcoord]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ d), Finset.card_univ,
    card_nonzeroSlope]
  simp only [Nat.sub_sub]

theorem expectation_originalLineCount (d : NonzeroSlope k) (z : k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).expectation
        (fun a => originalLineCount a d z) =
      (Fintype.card k : ℝ) *
        (1 - 1 / (Fintype.card k : ℝ)) ^ (Fintype.card k - 2) := by
  classical
  have hcount (a : GadgetOutcome k) :
      originalLineCount a d z =
        ∑ w ∈ linePoints (some d.val, z),
          if ∀ e : NonzeroSlope k, e ≠ d → ¬Incidence w (omittedLine a e)
          then (1 : ℝ) else 0 := by
    simp only [originalLineCount, originalLineSurvivors, Finset.sum_boole]
  calc
    _ = ∑ w ∈ linePoints (some d.val, z),
        (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).expectation
          (fun a => if ∀ e : NonzeroSlope k,
              e ≠ d → ¬Incidence w (omittedLine a e)
            then (1 : ℝ) else 0) := by
      simpa only [← hcount] using
        (expectation_finset_sum
          (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k))
          (linePoints (some d.val, z))
          (fun (w : Point k) (a : GadgetOutcome k) =>
            if ∀ e : NonzeroSlope k, e ≠ d → ¬Incidence w (omittedLine a e)
            then (1 : ℝ) else 0))
    _ = ∑ w ∈ linePoints (some d.val, z),
        (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
          (fun a => ∀ e, e ≠ d → ¬Incidence w (omittedLine a e)) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [FiniteLaw.prob_eq_expectation]
      apply congrArg (FiniteLaw.expectation
        (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)))
      funext a
      by_cases h : ∀ e : NonzeroSlope k,
          e ≠ d → ¬Incidence w (omittedLine a e)
      · simp
      · simp
    _ = _ := by
      simp only [prob_originalPoint_survival, Finset.sum_const,
        nsmul_eq_mul, card_linePoints]

end RyserCoveringCounterexample.Construction

end

end OAI
