import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import OAI.Probability.MatroidProphet.FiniteBits

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

inductive QueryProgram (α : Type*) where
  | stop
  | query (e : α) (no yes : QueryProgram α)
  | finish (rest : QueryProgram α)

def QueryProgram.Fresh : QueryProgram α → Finset α → Prop
  | .stop, _ => True
  | .query e no yes, V => e ∈ V ∧ no.Fresh (V.erase e) ∧ yes.Fresh (V.erase e)
  | .finish rest, V => rest.Fresh V

noncomputable def QueryProgram.expected (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) : QueryProgram α → Finset α → ℝ
  | .stop, _ => 0
  | .query e no yes, I => (1 - q e) * no.expected cert q I +
      q e * yes.expected cert q (insert e I)
  | .finish rest, I => (if cert I then 1 else 0) + rest.expected cert q ∅

lemma ratio_resource {p p' a : ℝ} (hp : 0 < p) (hpp' : p ≤ p')
    (ha : 0 ≤ a) (hap : a ≤ p) :
    a / p - a / p' ≤ Real.log p' - Real.log p := by
  have hp' : 0 < p' := lt_of_lt_of_le hp hpp'
  have hz : a / p ≤ 1 := (div_le_one hp).2 hap
  have hz0 : 0 ≤ a / p := div_nonneg ha hp.le
  have hx0 : 0 ≤ 1 - p / p' := by
    have h := (div_le_one hp').2 hpp'
    linarith
  have hm := mul_le_mul_of_nonneg_right hz hx0
  have heq : a / p - a / p' = (a / p) * (1 - p / p') := by
    field_simp
  rw [heq]
  calc
    a / p * (1 - p / p') ≤ 1 - p / p' := by simpa using hm
    _ ≤ Real.log (p' / p) := by
      simpa using Real.one_sub_inv_le_log_of_pos (div_pos hp' hp)
    _ = Real.log p' - Real.log p := Real.log_div hp'.ne' hp.ne'

theorem certificate_budget_of_failure_identities
    (cert : Finset α → Prop) [DecidablePred cert] (q : α → ℝ)
    (q_nonneg : ∀ e, 0 ≤ q e) (q_le_one : ∀ e, q e ≤ 1)
    (failure : Finset α → Finset α → ℝ)
    (positive : ∀ V, 0 < failure V ∅)
    (bounded : ∀ V I, 0 ≤ failure V I ∧ failure V I ≤ failure V ∅)
    (at_most_one : ∀ V, failure V ∅ ≤ 1)
    (depleted : ∀ V e, e ∈ V → failure V ∅ ≤ failure (V.erase e) ∅)
    (split : ∀ V I e, e ∈ V → failure V I =
      (1 - q e) * failure (V.erase e) I + q e * failure (V.erase e) (insert e I))
    (certifies : ∀ V I, cert I → failure V I = 0)
    (prog : QueryProgram α) (V I : Finset α) (fresh : prog.Fresh V) :
    prog.expected cert q I ≤ -Real.log (failure V ∅) + 1 - failure V I / failure V ∅ := by
  induction prog generalizing V I with
  | stop =>
    dsimp [QueryProgram.expected]
    have hlog : Real.log (failure V ∅) ≤ 0 :=
      Real.log_nonpos (positive V).le (at_most_one V)
    have hratio : failure V I / failure V ∅ ≤ 1 :=
      (div_le_one (positive V)).2 (bounded V I).2
    linarith
  | finish rest ih =>
    dsimp [QueryProgram.Fresh] at fresh
    have hr := ih V ∅ fresh
    have hp := positive V
    rw [div_self hp.ne'] at hr
    dsimp [QueryProgram.expected]
    split_ifs with hcert
    · rw [certifies V I hcert, zero_div]
      linarith
    · have hratio : failure V I / failure V ∅ ≤ 1 :=
        (div_le_one hp).2 (bounded V I).2
      linarith
  | query e no yes ihn ihy =>
    rcases fresh with ⟨he, hn, hy⟩
    have hno := ihn (V.erase e) I hn
    have hyes := ihy (V.erase e) (insert e I) hy
    have hqn : 0 ≤ 1 - q e := sub_nonneg.2 (q_le_one e)
    have h0 := mul_le_mul_of_nonneg_left hno hqn
    have h1 := mul_le_mul_of_nonneg_left hyes (q_nonneg e)
    have hp := positive V
    have hp' := positive (V.erase e)
    have hs := split V I e he
    have hresource := ratio_resource hp (depleted V e he) (bounded V I).1 (bounded V I).2
    have hmix : (1 - q e) *
        (-Real.log (failure (V.erase e) ∅) + 1 - failure (V.erase e) I / failure (V.erase e) ∅) +
        q e * (-Real.log (failure (V.erase e) ∅) + 1 -
          failure (V.erase e) (insert e I) / failure (V.erase e) ∅) =
        -Real.log (failure (V.erase e) ∅) + 1 - failure V I / failure (V.erase e) ∅ := by
      rw [hs]
      ring
    dsimp [QueryProgram.expected]
    linarith

theorem disjoint_query_certificates [Fintype α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure cert q univ ∅)
    (prog : QueryProgram α) (fresh : prog.Fresh univ) :
    prog.expected cert q ∅ ≤ Real.log (1 / bitsFailure cert q univ ∅) := by
  have hp (V : Finset α) : 0 < bitsFailure cert q V ∅ :=
    lt_of_lt_of_le hδ (bitsFailure_antitone cert hcert q hq0 hq1 ∅ (subset_univ V))
  have h := certificate_budget_of_failure_identities cert q hq0 hq1
    (bitsFailure cert q) hp
    (fun V I => ⟨bitsFailure_nonneg cert q hq0 hq1 V I,
      bitsFailure_forced_antitone cert hcert q hq0 hq1 V (empty_subset I)⟩)
    (fun V => bitsFailure_le_one cert q hq0 hq1 V ∅)
    (fun V e _ => bitsFailure_antitone cert hcert q hq0 hq1 ∅ (erase_subset e V))
    (bitsFailure_split cert q)
    (bitsFailure_certifies cert hcert q) prog univ ∅ fresh
  simpa [div_self hδ.ne'] using h

end MatroidProphet

end OAI
