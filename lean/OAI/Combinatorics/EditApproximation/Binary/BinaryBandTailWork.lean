import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeWork

namespace OAI

/-! Work of the literal representative tail. The sole callback premise is
an explicit bound on the already-defined band predicate, whose primitive
bound is `bandPredicateWithWork_cost`; no accuracy property is assumed. -/

namespace EditApproximation
namespace BinaryFraction

def bandFromActionsBitBudget (n B C : ℕ) : ℕ :=
  6000 * (B + 1) ^ 2 + 1000 * (8 * B + 7) ^ 2 + n * (C + 3) + 4

theorem bandFromActionsWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ []) (B C : ℕ)
    (hB : 1 ≤ B) (htau : tau.width ≤ B) (hvel : velocity.width ≤ B)
    (hC : ∀ states ∈ actions,
      (bandPredicateWithWork parent r b tau theta velocity actions hne child states).2 ≤ C) :
    (bandFromActionsWithWork parent r b tau theta velocity child actions hne).2 ≤
      bandFromActionsBitBudget actions.length B C := by
  let margin := subWithWork one tau
  have hmw := subWithWork_width one tau B (by exact hB) htau
  have hmc := subWithWork_cost one tau B (by exact hB) htau
  have hgc := leWithWork_cost velocity.absolute margin.1 (8 * B + 6)
    (by change velocity.width ≤ _; omega) hmw
  have hfc := filterWithWork_cost
    (bandPredicateWithWork parent r b tau theta velocity actions hne child) actions C hC
  unfold bandFromActionsWithWork
  dsimp only
  split_ifs
  · change margin.2 + (leWithWork velocity.absolute margin.1).2 +
      (filterWithWork (bandPredicateWithWork parent r b tau theta velocity actions hne child) actions).2 + 2 ≤ _
    change margin.2 ≤ _ at hmc
    unfold bandFromActionsBitBudget
    simp only [Nat.add_assoc, Nat.reduceAdd] at hgc
    omega
  · change margin.2 + (leWithWork velocity.absolute margin.1).2 + 1 ≤ _
    change margin.2 ≤ _ at hmc
    unfold bandFromActionsBitBudget
    simp only [Nat.add_assoc, Nat.reduceAdd] at hgc
    omega

def representativeTailInputBudget (M B : ℕ) : ℕ :=
  B + endpointScoreWordBudget M B + stateGapWordBudget B + 1

def representativeTailBitBudget (M n B C : ℕ) : ℕ :=
  let W := representativeTailInputBudget M B
  wideMinimumBitBudget M n B + 1000 * (W + 1) ^ 2 + stateGapBitBudget B +
    2100 * (W + 2) ^ 2 + bandFromActionsBitBudget n (4 * W + 4) C + 3

theorem representativeFromActionsWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (B C : ℕ)
    (htau : tau.width ≤ B) (hsource : Nat.size sourceLength + 2 ≤ B)
    (hrl : Nat.size r.lo + 2 ≤ B) (hrh : Nat.size r.hi + 2 ≤ B)
    (he : ∀ states ∈ actions, ∀ i, Nat.size (states i).lo + 2 ≤ B ∧
      Nat.size (states i).hi + 2 ≤ B)
    (hv : ∀ states ∈ actions, ∀ i, (child i (states i)).width ≤ B)
    (hC : ∀ (hne : actions ≠ []) (velocity : BinaryFraction),
      velocity.width ≤ 4 * representativeTailInputBudget M B + 4 →
      ∀ states ∈ actions,
        (bandPredicateWithWork parent r b tau theta velocity actions hne child states).2 ≤ C) :
    (representativeFromActionsWithWork parent r sourceLength b tau theta child actions).2 ≤
      representativeTailBitBudget M actions.length B C := by
  by_cases hnil : actions = []
  · simp only [representativeFromActionsWithWork, dite_eq_left hnil]
    dsimp only [representativeTailBitBudget]
    omega
  · let W := representativeTailInputBudget M B
    let Z := wideMinimumWithWork r child actions hnil
    have hW : B ≤ W := by dsimp only [W, representativeTailInputBudget]; omega
    have hWpos : 1 ≤ W := by dsimp only [W, representativeTailInputBudget]; omega
    have hz := wideMinimumWithWork_bounds r child actions hnil B hrl hrh he hv
    have hZw : Z.1.width ≤ W := hz.1.trans (by dsimp only [W, representativeTailInputBudget]; omega)
    have hpositive := ltWithWork_cost zero Z.1 W hWpos hZw
    have hgap := stateGapWithWork_bounds sourceLength r B hsource hrl hrh
    have hgapW : (stateGapWithWork sourceLength r).1.width ≤ W := hgap.1.trans (by
      dsimp only [W, representativeTailInputBudget]; omega)
    have hvel := divWithWork_width_uniform (stateGapWithWork sourceLength r).1 Z.1 W hgapW hZw
    have hvelc := divWithWork_cost (stateGapWithWork sourceLength r).1 Z.1 W hgapW hZw
    have hband := bandFromActionsWithWork_cost parent r b tau theta
      (divWithWork (stateGapWithWork sourceLength r).1 Z.1).1 child actions hnil (4 * W + 4) C
      (by omega) (htau.trans (by omega)) hvel (hC hnil _ hvel)
    unfold representativeFromActionsWithWork
    rw [dite_eq_right hnil]
    dsimp only
    split_ifs
    · change Z.2 + (ltWithWork zero Z.1).2 + (stateGapWithWork sourceLength r).2 +
        (divWithWork (stateGapWithWork sourceLength r).1 Z.1).2 +
        (bandFromActionsWithWork parent r b tau theta
          (divWithWork (stateGapWithWork sourceLength r).1 Z.1).1 child actions hnil).2 + 3 ≤
        wideMinimumBitBudget M actions.length B + 1000 * (W + 1) ^ 2 + stateGapBitBudget B +
          2100 * (W + 2) ^ 2 + bandFromActionsBitBudget actions.length (4 * W + 4) C + 3
      have hzc : Z.2 ≤ wideMinimumBitBudget M actions.length B := hz.2
      omega
    · change Z.2 + (ltWithWork zero Z.1).2 + 2 ≤
        wideMinimumBitBudget M actions.length B + 1000 * (W + 1) ^ 2 + stateGapBitBudget B +
          2100 * (W + 2) ^ 2 + bandFromActionsBitBudget actions.length (4 * W + 4) C + 3
      have hzc : Z.2 ≤ wideMinimumBitBudget M actions.length B := hz.2
      omega

def representativeGuardInputBudget (M vertices B : ℕ) : ℕ :=
  4 * representativeTailInputBudget M B + 4 + B + M + vertices + 2

def representativeCompleteBitBudget (M vertices B : ℕ) : ℕ :=
  let S := representativeGuardInputBudget M vertices B
  representativeTailBitBudget M vertices B
    (bandPredicateBitBudget M S (S ^ prefixArithmeticDegree))

/-- Every prefix-cut callback in the representative tail is bounded by
the proved finite-prefix implementation, rather than an assumed callback
budget. The premises concern only the stored input widths. -/
theorem representativeFromActionsWithWork_complete_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (B : ℕ)
    (htau : tau.width ≤ B) (htheta : theta.width ≤ B)
    (hsourceLength : Nat.size sourceLength + 2 ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hrl : Nat.size r.lo + 2 ≤ B) (hrh : Nat.size r.hi + 2 ≤ B)
    (hp : Nat.size parent.lo + 2 ≤ B)
    (hsource : ∀ i : Fin M, Nat.size (sourceChild parent i).lo + 2 ≤ B ∧
      Nat.size (sourceChild parent i).hi + 2 ≤ B)
    (hanchor : ∀ i : Fin M, Nat.size (r.lo + ((sourceChild parent i).lo - parent.lo)) + 2 ≤ B ∧
      Nat.size (r.lo + ((sourceChild parent i).hi - parent.lo)) + 2 ≤ B)
    (hradius : Nat.size (6 * b) + 2 ≤ B)
    (he : ∀ states ∈ actions, ∀ i, Nat.size (states i).lo + 2 ≤ B ∧
      Nat.size (states i).hi + 2 ≤ B)
    (hv : ∀ states ∈ actions, ∀ i, (child i (states i)).width ≤ B) :
    (representativeFromActionsWithWork parent r sourceLength b tau theta child actions).2 ≤
      representativeCompleteBitBudget M actions.length B := by
  let S := representativeGuardInputBudget M actions.length B
  have hBS : B ≤ S := by dsimp only [S, representativeGuardInputBudget]; omega
  have hS : 2 ≤ S := by dsimp only [S, representativeGuardInputBudget]; omega
  have hMS : M ≤ S := by dsimp only [S, representativeGuardInputBudget]; omega
  have hnS : actions.length ≤ S := by dsimp only [S, representativeGuardInputBudget]; omega
  apply representativeFromActionsWithWork_cost parent r sourceLength b tau theta child actions B
    (bandPredicateBitBudget M S (S ^ prefixArithmeticDegree)) htau hsourceLength hrl hrh he hv
  intro hne velocity hvelocity states hstates
  apply bandPredicateWithWork_cost parent r b tau theta velocity actions hne child states S
    (S ^ prefixArithmeticDegree) hstates (htau.trans hBS) (htheta.trans hBS)
    (hvelocity.trans (by dsimp only [S, representativeGuardInputBudget]; omega))
    (hb.trans hBS) (hM.trans hBS) (hrl.trans hBS) (hrh.trans hBS) (hp.trans hBS)
    (fun i => ⟨(hsource i).1.trans hBS, (hsource i).2.trans hBS⟩)
    (fun i => ⟨(hanchor i).1.trans hBS, (hanchor i).2.trans hBS⟩)
    (hradius.trans hBS)
    (fun a ha i => ⟨(he a ha i).1.trans hBS, (he a ha i).2.trans hBS⟩)
    (fun a ha i => (hv a ha i).trans hBS)
  intro j
  exact (prefix_guard_budgets_le_fixed_power M j.val actions.length S S hS hMS
    (j.isLt.le.trans hMS) hnS le_rfl).2.2.2.2.1

end BinaryFraction
end EditApproximation

end OAI
