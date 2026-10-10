import OAI.Probability.MatroidSecretary.Pivots.SupportedQueryModel
import OAI.Probability.MatroidSecretary.Pivots.MarkedTransactions

namespace OAI

/-!
# Removing impossible invalid query branches

A no-repeat procedure need only satisfy that property along its possible
transcripts. Truncating at an attempted repeated/unavailable query produces a
globally fresh finite tree and does not change any lawful execution. Together
with support-sensitive certificate soundness, this includes deterministic bit
coordinates without imposing conditions on impossible transcripts.
-/

namespace MatroidProphet.MarkedQueryProgram

open Finset

variable {α : Type*} [DecidableEq α]

/-- Stop at an attempted repeated or otherwise unavailable coordinate. -/
def prune : MarkedQueryProgram α → Finset α → MarkedQueryProgram α
  | .stop, _ => .stop
  | .query e no yes, V => if e ∈ V then
      .query e (no.prune (V.erase e)) (yes.prune (V.erase e)) else .stop
  | .finish success rest, V => .finish success (rest.prune V)

lemma prune_fresh (prog : MarkedQueryProgram α) (V : Finset α) :
    (prog.prune V).Fresh V := by
  induction prog generalizing V with
  | stop => trivial
  | query e no yes ihn ihy =>
    by_cases he : e ∈ V
    · simp only [prune, ite_eq_left he, Fresh]
      exact ⟨he, ihn _, ihy _⟩
    · simp [prune, he, Fresh]
  | finish success rest ih => exact ih V

lemma run_prune_eq (prog : MarkedQueryProgram α) (S V : Finset α)
    (fresh : prog.FreshAt S V) : (prog.prune V).run S = prog.run S := by
  induction prog generalizing V with
  | stop => rfl
  | query e no yes ihn ihy =>
    have heV : e ∈ V := fresh.1
    simp only [prune, ite_eq_left heV, run]
    by_cases heS : e ∈ S
    · simp only [ite_eq_left heS]
      exact ihy _ (by simpa only [FreshAt, ite_eq_left heS] using fresh.2)
    · simp only [ite_eq_right heS]
      exact ihn _ (by simpa only [FreshAt, ite_eq_right heS] using fresh.2)
  | finish success rest ih =>
    simp only [prune, run]
    rw [ih V fresh]

lemma soundAt_prune (cert : Finset α → Prop) (prog : MarkedQueryProgram α)
    (S I V : Finset α) (sound : prog.SoundAt cert S I) :
    (prog.prune V).SoundAt cert S I := by
  induction prog generalizing I V with
  | stop => trivial
  | query e no yes ihn ihy =>
    by_cases heV : e ∈ V
    · simp only [prune, ite_eq_left heV, SoundAt]
      by_cases heS : e ∈ S
      · simp only [ite_eq_left heS]
        exact ihy _ _ (by simpa only [SoundAt, ite_eq_left heS] using sound)
      · simp only [ite_eq_right heS]
        exact ihn _ _ (by simpa only [SoundAt, ite_eq_right heS] using sound)
    · simp [prune, heV, SoundAt]
  | finish success rest ih =>
    exact ⟨sound.1, ih ∅ V sound.2⟩

lemma bitsExpectation_prune_eq [Fintype α]
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (prog : MarkedQueryProgram α)
    (fresh : ∀ S, 0 < bitsWeight q univ S → prog.FreshAt S univ) :
    bitsExpectation q univ (prog.prune univ).run = bitsExpectation q univ prog.run := by
  unfold bitsExpectation
  apply sum_congr rfl
  intro S _
  by_cases hp : 0 < bitsWeight q univ S
  · dsimp only
    rw [prog.run_prune_eq S univ (fresh S hp)]
  · have hz : bitsWeight q univ S = 0 :=
      le_antisymm (le_of_not_gt hp) (bitsWeight_nonneg q hq0 hq1 univ S)
    simp [hz]

/-- The certificate budget requires no-repeat and soundness only on possible
executions. No conditions are placed on zero-probability bit vectors. -/
theorem disjoint_query_certificates_supported [Fintype α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    (prog : MarkedQueryProgram α)
    (fresh : ∀ S, 0 < bitsWeight q univ S → prog.FreshAt S univ)
    (sound : ∀ S, 0 < bitsWeight q univ S → prog.SoundAt cert S ∅) :
    bitsExpectation q univ prog.run ≤ Real.log (1 / bitsFailure cert q univ ∅) := by
  rw [← prog.bitsExpectation_prune_eq q hq0 hq1 fresh]
  exact (prog.prune univ).disjoint_query_certificates_support cert hcert q hq0 hq1 hδ
    (prog.prune_fresh univ) (fun S hS => prog.soundAt_prune cert S ∅ univ (sound S hS))

end MatroidProphet.MarkedQueryProgram

end OAI
