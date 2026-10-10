import OAI.Probability.MatroidSecretary.Pivots.MarkedQueryProgramModel
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Explicit success declarations satisfy the disjoint-query certificate bound.
The support-sensitive version permits arbitrary behavior on zero-probability
bit vectors, including deterministic Bernoulli coordinates. -/

namespace MatroidProphet

open Finset

namespace MarkedQueryProgram

variable {α : Type*} [DecidableEq α]

/-- Forget success declarations, retaining the exact adaptive query tree. -/
def erase : MarkedQueryProgram α → QueryProgram α
  | .stop => .stop
  | .query e no yes => .query e no.erase yes.erase
  | .finish _ rest => .finish rest.erase

lemma erase_fresh (prog : MarkedQueryProgram α) (V : Finset α)
    (fresh : prog.Fresh V) : prog.erase.Fresh V := by
  induction prog generalizing V with
  | stop => trivial
  | query e no yes ihn ihy =>
    exact ⟨fresh.1, ihn _ fresh.2.1, ihy _ fresh.2.2⟩
  | finish success rest ih => exact ih V fresh

lemma run_nonneg (prog : MarkedQueryProgram α) (S : Finset α) :
    0 ≤ prog.run S := by
  induction prog with
  | stop => simp [run]
  | query e no yes ihn ihy => simp only [run]; split_ifs <;> assumption
  | finish success rest ih =>
    cases success <;> simp only [run, Bool.false_eq_true, ite_false, ite_true] <;> linarith

lemma run_le_transactionBound (prog : MarkedQueryProgram α) (S : Finset α) :
    prog.run S ≤ (prog.transactionBound : ℝ) := by
  induction prog with
  | stop => simp [run, transactionBound]
  | query e no yes ihn ihy =>
    simp only [run, transactionBound]
    split_ifs
    · exact ihy.trans (by exact_mod_cast (le_max_right no.transactionBound yes.transactionBound))
    · exact ihn.trans (by exact_mod_cast (le_max_left no.transactionBound yes.transactionBound))
  | finish success rest ih =>
    cases success <;> simp only [run, transactionBound, Bool.false_eq_true, ite_false,
      ite_true, Nat.cast_add, Nat.cast_one] <;> linarith

lemma run_le_certifying_run (cert : Finset α → Prop) [DecidablePred cert]
    (prog : MarkedQueryProgram α) (S I : Finset α)
    (sound : prog.SoundAt cert S I) :
    prog.run S ≤ prog.erase.run cert S I := by
  induction prog generalizing I with
  | stop => simp [run, erase, QueryProgram.run]
  | query e no yes ihn ihy =>
    by_cases he : e ∈ S
    · simp only [run, erase, QueryProgram.run, ite_eq_left he]
      exact ihy (insert e I) (by simpa [SoundAt, he] using sound)
    · simp only [run, erase, QueryProgram.run, ite_eq_right he]
      exact ihn I (by simpa [SoundAt, he] using sound)
  | finish success rest ih =>
    obtain ⟨hcert, hrest⟩ := sound
    have hr := ih ∅ hrest
    cases success with
    | false =>
      simp only [run, erase, QueryProgram.run, Bool.false_eq_true, ite_false]
      split_ifs <;> linarith
    | true =>
      have hc := hcert rfl
      simp only [run, erase, QueryProgram.run, ite_true, ite_eq_left hc]
      linarith

/-- Source `lem:transactions` for actual selected successes, with full support
sensitivity. The tree only needs the soundness law on positive-weight vectors. -/
theorem disjoint_query_certificates_support [Fintype α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    (prog : MarkedQueryProgram α) (fresh : prog.Fresh univ)
    (sound : ∀ S, 0 < bitsWeight q univ S → prog.SoundAt cert S ∅) :
    bitsExpectation q univ prog.run ≤ Real.log (1 / bitsFailure cert q univ ∅) := by
  refine le_trans ?_ (disjoint_query_certificates_product cert hcert q hq0 hq1 hδ
    prog.erase (prog.erase_fresh univ fresh))
  unfold bitsExpectation
  apply sum_le_sum
  intro S hS
  have hw := bitsWeight_nonneg q hq0 hq1 univ S
  by_cases hp : 0 < bitsWeight q univ S
  · exact mul_le_mul_of_nonneg_left (prog.run_le_certifying_run cert S ∅ (sound S hp)) hw
  · have hz : bitsWeight q univ S = 0 := le_antisymm (le_of_not_gt hp) hw
    simp [hz]

/-- The usual everywhere-lawful special case. -/
theorem disjoint_query_certificates [Fintype α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    (prog : MarkedQueryProgram α) (fresh : prog.Fresh univ)
    (sound : ∀ S, prog.SoundAt cert S ∅) :
    bitsExpectation q univ prog.run ≤ Real.log (1 / bitsFailure cert q univ ∅) :=
  prog.disjoint_query_certificates_support cert hcert q hq0 hq1 hδ fresh
    (fun S _ => sound S)

end MarkedQueryProgram
end MatroidProphet

end OAI
