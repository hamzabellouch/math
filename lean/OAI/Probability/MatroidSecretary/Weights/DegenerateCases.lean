import OAI.Probability.MatroidProphet.Main
import Mathlib.Combinatorics.Matroid.Loop

namespace OAI

/-!
# Degenerate inputs and loop coordinates

These lemmas concern the actual optimum and online execution, not a surrogate
benchmark. They make explicit the empty-ground, all-loop, zero-optimum and
fully-sacrificed cases admitted by setup.tex and secretary.tex. In particular,
no moment or boundedness hypothesis on a loop coordinate is needed for OPT.
-/

namespace MatroidProphet.DegenerateCases

open Finset

/-- Offline optimization is unaffected by any change in loop coordinates. -/
theorem optimum_congr_on_nonloops {n : ℕ} (M : Matroid (Fin n))
    (v w : Weights n) (h : ∀ e, M.IsNonloop e → v e = w e) :
    optimum M v = optimum M w := by
  classical
  unfold optimum
  congr 1
  funext I
  split_ifs with hI
  · apply Finset.sum_congr rfl
    intro e he
    exact h e (hI.isNonloop_of_mem he)
  · rfl

/-- Zero weights have zero optimum, without a full-ground assumption. -/
theorem optimum_zero {n : ℕ} (M : Matroid (Fin n)) :
    optimum M (fun _ => 0) = 0 := by
  classical
  unfold optimum
  simp

/-- If every nonloop has zero weight, arbitrary loop weights do not affect OPT. -/
theorem optimum_eq_zero_of_nonloops_zero {n : ℕ} (M : Matroid (Fin n))
    (w : Weights n) (hw : ∀ e, M.IsNonloop e → w e = 0) :
    optimum M w = 0 := by
  rw [optimum_congr_on_nonloops M w (fun _ => 0) hw, optimum_zero]

/-- The all-loop case includes arbitrarily large and arbitrary-sign loop weights. -/
theorem optimum_eq_zero_of_all_loops {n : ℕ} (M : Matroid (Fin n))
    (hM : ∀ e, M.IsLoop e) (w : Weights n) : optimum M w = 0 := by
  apply optimum_eq_zero_of_nonloops_zero
  intro e he
  exact False.elim (he.not_isLoop (hM e))

/-- No labels is a valid input, and its actual offline optimum is zero. -/
theorem optimum_empty (M : Matroid (Fin 0)) (w : Weights 0) :
    optimum M w = 0 := by
  apply optimum_eq_zero_of_nonloops_zero
  intro e
  exact Fin.elim0 e

/-- A nonloop singleton is one of the sets in the optimization benchmark. -/
theorem nonloop_weight_le_optimum {n : ℕ} (M : Matroid (Fin n))
    (w : Weights n) (e : Fin n) (he : M.IsNonloop e) :
    w e ≤ optimum M w := by
  simpa using sum_le_optimum M w {e} (by simpa using he.indep)

/-- On nonnegative vectors, OPT vanishes exactly when every nonloop weight does. -/
theorem optimum_eq_zero_iff {n : ℕ} (M : Matroid (Fin n))
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    optimum M w = 0 ↔ ∀ e, M.IsNonloop e → w e = 0 := by
  constructor
  · intro h e he
    exact le_antisymm (h ▸ nonloop_weight_le_optimum M w e he) (hw e)
  · exact optimum_eq_zero_of_nonloops_zero M w

/-- Every feasible rule has exactly zero reward on a zero-OPT input. -/
theorem reward_eq_zero_of_optimum_eq_zero {n bits : ℕ}
    (M : Matroid (Fin n)) (A : OnlineRule n bits) (hA : Feasible M A)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n)
    (hs : ∀ e, 0 ≤ s e) (hv : ∀ e, 0 ≤ v e) (hopt : optimum M v = 0) :
    reward A r s v π = 0 := by
  apply le_antisymm
  · simpa only [hopt] using reward_le_optimum M A hA r s v π hs hv
  · exact reward_nonneg A r s v π hv

/-- Running past the finite final arrival does not create any further decisions. -/
theorem acceptedThrough_stabilizes {n bits : ℕ} (A : OnlineRule n bits)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n)
    (t : ℕ) (ht : n ≤ t) :
    acceptedThrough A r s v π t = accepted A r s v π := by
  classical
  ext e
  have he : (π.symm e).val < t := lt_of_lt_of_le (π.symm e).isLt ht
  simp [accepted, acceptedThrough, he]

/-- The empty prefix never accepts anything, regardless of the rule. -/
theorem acceptedThrough_zero {n bits : ℕ} (A : OnlineRule n bits)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) :
    acceptedThrough A r s v π 0 = ∅ := by
  classical
  simp [acceptedThrough]

/-- Fully revealed hidden-vector inputs are fully sacrificed, at every prefix. -/
theorem hiddenAcceptedThrough_eq_empty_of_full_mask {n bits : ℕ}
    (A : HiddenRule n bits) (r : Seed bits) (hmask : A.mask r = Finset.univ)
    (w : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    hiddenAcceptedThrough A r w π t = ∅ := by
  simp [hiddenAcceptedThrough, hmask]

/-- Full sacrifice gives zero reward for every order, including the empty order. -/
theorem hiddenReward_eq_zero_of_full_mask {n bits : ℕ}
    (A : HiddenRule n bits) (r : Seed bits) (hmask : A.mask r = Finset.univ)
    (w : Weights n) (π : ArrivalOrder n) : hiddenReward A r w π = 0 := by
  simp [hiddenReward, hiddenAcceptedThrough_eq_empty_of_full_mask A r hmask]

/-- The seed-wise adversarial minimum also vanishes under full sacrifice. -/
theorem hiddenWorstReward_eq_zero_of_full_mask {n bits : ℕ}
    (A : HiddenRule n bits) (r : Seed bits) (hmask : A.mask r = Finset.univ)
    (w : Weights n) : hiddenWorstReward A w r = 0 := by
  classical
  simp [hiddenWorstReward, hiddenReward_eq_zero_of_full_mask A r hmask]

end MatroidProphet.DegenerateCases

end OAI
