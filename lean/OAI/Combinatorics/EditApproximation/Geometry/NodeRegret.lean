import OAI.Combinatorics.EditApproximation.Geometry.FirstCrossing

namespace OAI

/-!
# Clipped regret of the actual refinement update

This is the deterministic first-crossing transfer in Proposition 7.3.
The hypothesis about group estimates is a pointwise estimate on their
success event; their probability is handled separately. No independence
between a sampled action and that success event is required.
-/

namespace EditApproximation

open Finset

noncomputable def bandActionCost {β σ : Type*} [Fintype β]
    (charge : ℝ) (table : ℕ → β × σ → ℝ) (t : ℕ) (action : β → σ) : ℝ :=
  charge + ∑ child, table t (child, action child)

noncomputable def sampledPrefixRegret {β σ : Type*} [Fintype β]
    (charge κ : ℝ) (table : ℕ → β × σ → ℝ)
    (comparisonClipped : ℕ → ℝ) (sample : ℕ → β → σ) (t : ℕ) : ℝ :=
  bandActionCost charge table (t + 1) (sample t) +
    κ * (bandActionCost charge table t (sample t) -
      bandActionCost charge table (t + 1) (sample t)) - charge - comparisonClipped (t + 1)

theorem refinement_firstCrossing_regret {β σ : Type*} [Fintype β]
    (band : Finset (β → σ)) (S : ℕ)
    (table : ℕ → β × σ → ℝ) (comparisonClipped : ℕ → ℝ)
    (sample : ℕ → β → σ) (cone online : ℕ → ℝ) (failure : ℕ → Bool)
    (charge c b F δ κ error : ℝ)
    (hc : 0 ≤ c) (hF : 1 ≤ F) (hδ : 0 < δ) (hκ : 0 ≤ κ) (hb : b ≤ c)
    (herror : error * b ≤ κ * δ * b) (herrorCross : error * b ≤ δ * c)
    (hmono : ∀ action ∈ band, Antitone (fun t => bandActionCost charge table t action))
    (hsample : ∀ t < S, sample t ∈ band)
    (hcomparison : ∀ t ≤ S, c ≤ charge + comparisonClipped t)
    (honline : ∀ t < S, online t ≤ bandActionCost charge table (t + 1) (sample t))
    (hbellman : ∀ t < S, ∀ action ∈ band, cone t ≤ bandActionCost charge table t action)
    (hgroup : ∀ t < S, failure t = false → ∀ action ∈ band,
      cone t ≤ (1 + δ) * bandActionCost charge table (t + 1) action + error * b)
    (hupper : ∀ t < S, max c (refinementUpdate δ (cone t) (online t)) ≤ 2 * F * c) :
    let crossing := firstCrossing band S (fun t => bandActionCost charge table (t + 1)) c
    (∑ t ∈ range S,
      (max c (refinementUpdate δ (cone t) (online t)) - charge - comparisonClipped (t + 1))) ≤
      (∑ t ∈ range crossing, sampledPrefixRegret charge κ table comparisonClipped sample t) +
        2 * δ * c + 2 * F * c * ∑ t ∈ range S, (if failure t then (1 : ℝ) else 0) := by
  let actionCost := fun t => bandActionCost charge table (t + 1)
  let crossing := firstCrossing band S actionCost c
  let regret := fun t => max c (refinementUpdate δ (cone t) (online t)) -
    charge - comparisonClipped (t + 1)
  have hcrossing : crossing ≤ S := firstCrossing_le band S actionCost c
  change (∑ t ∈ range S, regret t) ≤
    (∑ t ∈ range crossing, sampledPrefixRegret charge κ table comparisonClipped sample t) +
      2 * δ * c + 2 * F * c * ∑ t ∈ range S, (if failure t then (1 : ℝ) else 0)
  apply firstCrossing_sum_bound S crossing regret
    (sampledPrefixRegret charge κ table comparisonClipped sample)
    (fun t => if failure t then (1 : ℝ) else 0) (2 * δ * c) (2 * F * c)
    hcrossing (by positivity) (by positivity)
  · intro t _
    split_ifs <;> norm_num
  · intro t ht
    have htS : t < S := ht.trans_le hcrossing
    have ha := hsample t htS
    have hcost : c ≤ bandActionCost charge table (t + 1) (sample t) :=
      before_firstCrossing band S actionCost c ht ha
    have hdecrease := hmono (sample t) ha (Nat.le_succ t)
    have hclip : max c (refinementUpdate δ (cone t) (online t)) ≤
        bandActionCost charge table (t + 1) (sample t) +
          κ * (bandActionCost charge table t (sample t) -
            bandActionCost charge table (t + 1) (sample t)) +
          2 * F * c * (if failure t then (1 : ℝ) else 0) := by
      cases hf : failure t with
      | false =>
        simp only [Bool.false_eq_true, ite_false, mul_zero, add_zero]
        exact refinementUpdate_prefix hδ hκ hc hb hcost hdecrease
          (honline t htS) (hbellman t htS (sample t) ha)
          (hgroup t htS hf (sample t) ha) herror
      | true =>
        simp only [ite_true, mul_one]
        have hdec0 := mul_nonneg hκ (sub_nonneg.mpr hdecrease)
        linarith [hupper t htS]
    dsimp only [regret, sampledPrefixRegret]
    linarith
  · intro ht
    obtain ⟨action, ha, hcross⟩ := at_firstCrossing band S actionCost c ht
    have hclip : max c (refinementUpdate δ (cone crossing) (online crossing)) ≤
        c + 2 * δ * c + 2 * F * c * (if failure crossing then (1 : ℝ) else 0) := by
      cases hf : failure crossing with
      | false =>
        simp only [Bool.false_eq_true, ite_false, mul_zero, add_zero]
        apply refinementUpdate_crossing hδ.le hc hcross
        have hestimate := hgroup crossing ht hf action ha
        linarith
      | true =>
        simp only [ite_true, mul_one]
        have hslack := mul_nonneg hδ.le hc
        linarith [hupper crossing ht]
    dsimp only [regret]
    linarith [hcomparison (crossing + 1) (by omega)]
  · intro t ht hafter
    obtain ⟨action, ha, hcross⟩ := at_firstCrossing band S actionCost c (hafter.trans ht)
    have hcost : bandActionCost charge table t action < c :=
      (hmono action ha (show crossing + 1 ≤ t by omega)).trans_lt hcross
    have hparent : refinementUpdate δ (cone t) (online t) ≤ c :=
      (min_le_left _ _).trans ((hbellman t ht action ha).trans hcost.le)
    dsimp only [regret]
    rw [max_eq_left hparent]
    linarith [hcomparison (t + 1) (by omega)]

end EditApproximation

end OAI
