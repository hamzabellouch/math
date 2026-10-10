import OAI.Combinatorics.EditApproximation.Queries.QueryEarlierInputs
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRationalWarmup

namespace OAI

/-! Wide Bellman scoring reads only the earlier child coordinates in the
explicit finite cover. Enumeration can reuse their gathered values. -/

namespace EditApproximation

open Finset

theorem wideActionValues_congr_earlier {nx ny M : ℕ}
    (parent : TargetInterval nx) (P history time : ℕ)
    (small large : List (ℕ × TargetInterval ny)) (hsub : ∀ br ∈ small, br ∈ large)
    (left right : Fin M → ℕ → TargetInterval ny → ℚ) (htime : time < history)
    (hvalues : ∀ input ∈ wideEarlierInputCover parent P history large,
      left input.1 input.2.1 input.2.2 = right input.1 input.2.1 input.2.2)
    (distance : TargetInterval ny → TargetInterval ny → ℚ) (L : ℚ) (q : TargetInterval ny) :
    (rationalActualWideActions parent small P).map
      (rationalActionValue distance L (fun input => left input.1 time input.2) q) =
    (rationalActualWideActions parent small P).map
      (rationalActionValue distance L (fun input => right input.1 time input.2) q) := by
  apply List.map_congr_left
  intro action ha
  obtain ⟨br, hbr, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨states, hs, rfl⟩ := List.mem_map.mp ha
  unfold rationalActionValue
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact hvalues (i, time, states i)
    (wideEarlierInputCover_mem parent P history large br.1 br.2
      (hsub br hbr) time htime states hs i)

theorem localBellman_congr_earlier {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F exponent history time : ℕ) (a : ℚ)
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny)
    (left right : Fin M → ℕ → TargetInterval ny → ℚ) (htime : time < history)
    (hvalues : ∀ input ∈ queryEarlierInputCover parent N P F exponent history a initial q,
      left input.1 input.2.1 input.2.2 = right input.1 input.2.1 input.2.2) (L : ℚ) :
    rationalBellman initial (fun q r => targetEndpointDistance q r) L
      (rationalActualWideActions parent (localRefinementRepresentatives N P F a initial q) P)
      (fun input => left input.1 time input.2) q =
    rationalBellman initial (fun q r => targetEndpointDistance q r) L
      (rationalActualWideActions parent (localRefinementRepresentatives N P F a initial q) P)
      (fun input => right input.1 time input.2) q := by
  unfold rationalBellman
  rw [wideActionValues_congr_earlier parent P history time _ _
    (queryEarlierRepresentatives_local N P F exponent a initial q)
    left right htime hvalues]

end EditApproximation

end OAI
