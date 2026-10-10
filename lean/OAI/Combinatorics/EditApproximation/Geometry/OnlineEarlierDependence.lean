import OAI.Combinatorics.EditApproximation.Geometry.LocalOnlineProgram
import OAI.Combinatorics.EditApproximation.Queries.QueryEarlierInputs

namespace OAI

/-! The actual online optimizer reads only the recorded band coordinates
and earlier child histories. Equality on the finite query cover suffices
for equality of its returned action, including deterministic tie breaking. -/

namespace EditApproximation

open Finset

theorem rationalLinearizationMaximizer_congr_on {ι : Type*}
    (coordinates : Finset ι) (vertices : List (ι → ℚ)) (left right : ι → ℚ)
    (heq : ∀ i ∈ coordinates, left i = right i) :
    rationalLinearizationMaximizer coordinates vertices left =
      rationalLinearizationMaximizer coordinates vertices right := by
  have hscore : (fun p : ι → ℚ => ∑ i ∈ coordinates, left i * p i) =
      (fun p : ι → ℚ => ∑ i ∈ coordinates, right i * p i) := by
    funext p
    exact sum_congr rfl (fun i hi => by rw [heq i hi])
  unfold rationalLinearizationMaximizer
  rw [hscore]

theorem finiteRationalOptimizer_congr_linear_on {ι : Type*}
    (coordinates : Finset ι) (vertices : List (ι → ℚ)) (left right : ι → ℚ)
    (G j : ℕ) (heq : ∀ i ∈ coordinates, left i = right i) :
    finiteRationalOptimizer coordinates vertices left G j =
      finiteRationalOptimizer coordinates vertices right G j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [finiteRationalOptimizer, ih]
    have hselected := rationalLinearizationMaximizer_congr_on coordinates vertices
      (rationalSmoothedGradient G left (finiteRationalOptimizer coordinates vertices right G j))
      (rationalSmoothedGradient G right (finiteRationalOptimizer coordinates vertices right G j))
      (fun i hi => by simp only [rationalSmoothedGradient, heq i hi])
    rw [hselected]

theorem finiteOptimizerAction_congr_linear_on {β σ : Type*}
    [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (left right : β × σ → ℚ) (G j : ℕ)
    (heq : ∀ i ∈ bandCoordinates band.toFinset, left i = right i) :
    finiteOptimizerAction band hband mass left G j =
      finiteOptimizerAction band hband mass right G j := by
  unfold finiteOptimizerAction
  dsimp only
  rw [finiteRationalOptimizer_congr_linear_on _ _ left right G j heq]
  have hscore : (fun action : β → σ => ∑ i ∈ bandCoordinates band.toFinset,
      rationalSmoothedGradient G left
        (finiteRationalOptimizer (bandCoordinates band.toFinset) (band.map (actionVector mass)) right G j) i *
          actionVector mass action i) =
      (fun action : β → σ => ∑ i ∈ bandCoordinates band.toFinset,
      rationalSmoothedGradient G right
        (finiteRationalOptimizer (bandCoordinates band.toFinset) (band.map (actionVector mass)) right G j) i *
          actionVector mass action i) := by
    funext action
    apply sum_congr rfl
    intro i hi
    simp only [rationalSmoothedGradient, heq i hi]
  rw [hscore]

theorem finiteOptimizerActionDraw_congr_linear_on {β σ : Type*}
    [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (left right : β × σ → ℚ) (G K : ℕ) (integer : Fin (optimizerTriangularMass K))
    (heq : ∀ i ∈ bandCoordinates band.toFinset, left i = right i) :
    finiteOptimizerActionDraw band hband mass left G K integer =
      finiteOptimizerActionDraw band hband mass right G K integer :=
  finiteOptimizerAction_congr_linear_on band hband mass left right G _ heq

/-- The gain at `t` and decrements at indices below `t` inspect exactly
the input table indices at most `t`. -/
theorem rationalOnlineLinear_child_congr {β σ : Type*} (mass : β → ℚ)
    (left right : ℕ → β × σ → ℚ) (eta kappa : ℚ) (t : ℕ) (i : β × σ)
    (heq : ∀ s ≤ t, left s i = right s i) :
    rationalOnlineLinear eta kappa (childGain mass left) (childDecrement mass left) t i =
      rationalOnlineLinear eta kappa (childGain mass right) (childDecrement mass right) t i := by
  have hgain (s : ℕ) (hs : s ≤ t) : childGain mass left s i = childGain mass right s i := by
    simp only [childGain, heq s hs]
  have hdecrement (s : ℕ) (hs : s < t) :
      childDecrement mass left s i = childDecrement mass right s i := by
    simp only [childDecrement, heq s (by omega), heq (s + 1) (by omega)]
  unfold rationalOnlineLinear rationalOptimisticHistory
  rw [hgain t le_rfl]
  congr 2
  apply sum_congr rfl
  intro s hs
  rw [hgain s (by have ht := mem_range.mp hs; omega), hdecrement s (mem_range.mp hs)]

theorem keyedOnlineCandidate_congr_history {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (tau eta kappa : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (left right : PhysicalChildTables M target.length) (t : ℕ)
    (r : TargetInterval target.length) (integer : ℕ)
    (heq : ∀ i ∈ bandCoordinates (representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child).toFinset, ∀ s ≤ t,
        left i.1 s i.2 = right i.1 s i.2) :
    keyedOnlineCandidate source target parent P F exponent H b tau eta kappa child initial left t r integer =
      keyedOnlineCandidate source target parent P F exponent H b tau eta kappa child initial right t r integer := by
  have hlinear : ∀ i ∈ bandCoordinates (representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child).toFinset,
      rationalOnlineLinear eta kappa
        (childGain (bandChildEnvelope b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial) (fun s i => left i.1 s i.2))
        (childDecrement (bandChildEnvelope b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial) (fun s i => left i.1 s i.2)) t i =
      rationalOnlineLinear eta kappa
        (childGain (bandChildEnvelope b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial) (fun s i => right i.1 s i.2))
        (childDecrement (bandChildEnvelope b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial) (fun s i => right i.1 s i.2)) t i := by
    intro i hi
    exact rationalOnlineLinear_child_congr _ _ _ eta kappa t i (heq i hi)
  unfold keyedOnlineCandidate
  dsimp only
  split_ifs with hband
  · rfl
  · cases htest : testUnskippedBand source target parent b P exponent tau F child initial r with
    | none => rfl
    | some data =>
      apply congrArg (fun action => some (sharedBandRationalAction r action))
      exact finiteOptimizerActionDraw_congr_linear_on _ hband _ _ _ _ _ _ hlinear

theorem keyedOnlineCandidate_congr_earlier_cover {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b history : ℕ) (tau eta kappa : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (left right : PhysicalChildTables M target.length) (t : ℕ)
    (r : TargetInterval target.length) (integer : ℕ)
    (representatives : List (ℕ × TargetInterval target.length)) (hrep : (b, r) ∈ representatives)
    (ht : t < history)
    (heq : ∀ i s q, (i, s, q) ∈ wideEarlierInputCover parent P history representatives →
      left i s q = right i s q) :
    keyedOnlineCandidate source target parent P F exponent H b tau eta kappa child initial left t r integer =
      keyedOnlineCandidate source target parent P F exponent H b tau eta kappa child initial right t r integer := by
  apply keyedOnlineCandidate_congr_history
  intro i hi s hs
  apply heq
  exact bandCoordinates_earlier_cover source target parent P history b tau _ representatives r hrep
    child s (by omega) i hi

/-- All online candidates for a local query, with their original order
and ties, are fixed by the finite earlier-input cover. -/
theorem localOnlineCandidates_congr_earlier_cover {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H history : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (left right : PhysicalChildTables M target.length) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length)
    (ht : t < history)
    (heq : ∀ i s r, (i, s, r) ∈ queryEarlierInputCover parent N P F exponent history a parentInitial q →
      left i s r = right i s r) :
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial left t integer q =
      localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial right t integer q := by
  unfold localOnlineCandidates
  apply List.filterMap_congr
  intro b hb
  dsimp only
  split_ifs with heligible
  · apply keyedOnlineCandidate_congr_earlier_cover source target parent P F exponent H b history
      tau eta kappa child initial left right t _ _
      (queryEarlierRepresentatives N P F exponent a parentInitial q)
      (queryEarlierRepresentatives_online N P F exponent a parentInitial q b hb) ht
    exact heq
  · rfl

section Physical

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent H T : ℕ) (A tau eta kappa : ℚ)

/-- At a positive physical refinement time `t`, the online provider
depends only on child times strictly less than `t` in the query cover. -/
theorem physicalLocalOnline_congr_earlier_cover
    (integer : PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (node : PhysicalInternalNode M J) (left right : PhysicalChildTables M target.length)
    (t : ℕ) (ht : 0 < t) (q : TargetInterval target.length)
    (heq : ∀ i s r, (i, s, r) ∈ queryEarlierInputCover
      (physicalSourceInterval source.length node.1) N P F exponent t (refinementFactor A F)
      (fun r => stageInitial source target U N P F A (node.1, r)) q →
        left i s r = right i s r) :
    physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer node.1 left t q =
      physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer node.1 right t q := by
  unfold physicalLocalOnline
  rw [dite_eq_left node.2, dite_eq_left node.2]
  exact localOnlineCandidates_congr_earlier_cover source target _ N P F exponent H t
    tau (refinementFactor A F) eta kappa _ _ _ left right (t - 1) _ q (by omega) heq

end Physical
end EditApproximation

end OAI
