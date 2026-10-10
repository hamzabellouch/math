import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# The exact one-query resource identity

This is the displayed `eq:log-resource` with its conditional product law written
as the explicit two-outcome Bernoulli expectation. The finite-tree execution
proof justifies applying this identity at every predictably selected fresh query.
-/

namespace MatroidProphet

open Finset

/-- The source's expected one-query decrement, exponential expression, and
logarithmic bound, for the actual finite-product failure probabilities. -/
theorem transaction_log_resource
    {α : Type*} [DecidableEq α]
    (cert : Finset α → Prop) [DecidablePred cert] (hcert : Monotone cert)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V I : Finset α) (e : α) (he : e ∈ V)
    (hp : 0 < bitsFailure cert q V ∅) :
    let p := bitsFailure cert q V ∅
    let p' := bitsFailure cert q (V.erase e) ∅
    let Z := bitsFailure cert q V I / p
    let next := (1 - q e) * (bitsFailure cert q (V.erase e) I / p') +
      q e * (bitsFailure cert q (V.erase e) (insert e I) / p')
    Z - next = Z * (1 - p / p') ∧
      Z - next = Z * (1 - Real.exp (-(Real.log p' - Real.log p))) ∧
      Z - next ≤ Real.log p' - Real.log p := by
  dsimp only
  have hpp' : bitsFailure cert q V ∅ ≤ bitsFailure cert q (V.erase e) ∅ :=
    bitsFailure_antitone cert hcert q hq0 hq1 ∅ (erase_subset e V)
  have hp' : 0 < bitsFailure cert q (V.erase e) ∅ := hp.trans_le hpp'
  have hmean :
      (1 - q e) * (bitsFailure cert q (V.erase e) I /
          bitsFailure cert q (V.erase e) ∅) +
        q e * (bitsFailure cert q (V.erase e) (insert e I) /
          bitsFailure cert q (V.erase e) ∅) =
      bitsFailure cert q V I / bitsFailure cert q (V.erase e) ∅ := by
    rw [bitsFailure_split cert q V I e he]
    ring
  rw [hmean]
  have hid : bitsFailure cert q V I / bitsFailure cert q V ∅ -
      bitsFailure cert q V I / bitsFailure cert q (V.erase e) ∅ =
      bitsFailure cert q V I / bitsFailure cert q V ∅ *
        (1 - bitsFailure cert q V ∅ / bitsFailure cert q (V.erase e) ∅) := by
    field_simp
  refine ⟨hid, ?_, ?_⟩
  · rw [neg_sub, Real.exp_sub, Real.exp_log hp, Real.exp_log hp']
    exact hid
  · exact ratio_resource hp hpp' (bitsFailure_nonneg cert q hq0 hq1 V I)
      (bitsFailure_forced_antitone cert hcert q hq0 hq1 V (empty_subset I))

end MatroidProphet

end OAI
