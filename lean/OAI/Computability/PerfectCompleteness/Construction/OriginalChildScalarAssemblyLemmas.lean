import Mathlib.Data.Fintype.BigOperators
import OAI.Computability.PerfectCompleteness.Construction.AscendingBranchingLemmas
import OAI.Computability.PerfectCompleteness.Construction.OriginalChildScalars
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionOrderLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedRows
import OAI.Computability.PerfectCompleteness.Sampling.UniformChildSum
import OAI.Computability.PerfectCompleteness.Sampling.UniformLatent

namespace OAI


namespace PerfectCompleteness.OriginalChildScalarAssembly

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces
open OriginalChildScalars RecursiveSamplerBiasAlgebra
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

@[simp] theorem stepSquareMap_self (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : ScalarTape repeats chosen q slots) :
    stepSquareMap repeats chosen q slots ω chosen =
      squareSum repeats slots chosen
        (RecursiveSampler.splitEvaluatedTape F2 repeats chosen q (LeafDomain slots) ω).2 := by
  exact congrArg Prod.fst
    ((Equiv.piSplitAt chosen (fun child => ↥(Square slots child))).apply_symm_apply
      (selectedAndOthers repeats chosen q slots ω))

@[simp] theorem stepSquareMap_other (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : ScalarTape repeats chosen q slots) (child : RecursiveSampler.OffPath chosen) :
    stepSquareMap repeats chosen q slots ω child.val = ω (.inl child) := by
  exact congrArg
    (fun z : Square slots chosen ×
      ((j : RecursiveSampler.OffPath chosen) → Square slots j.val) => z.2 child)
    ((Equiv.piSplitAt chosen (fun child => ↥(Square slots child))).apply_symm_apply
      (selectedAndOthers repeats chosen q slots ω))

theorem recursiveSum_eq_sum (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (values : (child : Fin (branch n)) → Square slots child) :
    UniformChildSum.recursiveSum (𝕜 := F2) (LeafDomain slots) values =
      ∑ child : Fin (branch n), childSquareLift F2 (LeafDomain slots) child (values child) := by
  apply Subtype.ext
  change (∑ child : Fin (branch n),
      pullback F2 (childRestriction (LeafDomain slots) child) (values child).val) =
    (H slots).subtype
      (∑ child : Fin (branch n), childSquareLift F2 (LeafDomain slots) child (values child))
  rw [map_sum]
  rfl

theorem childSquareLift_squareSum (repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (chosen : Fin (branch n))
    (values : RecursiveSampler.CallIndex repeats n → H (childSlots slots chosen)) :
    childSquareLift F2 (LeafDomain slots) chosen (squareSum repeats slots chosen values) =
      ∑ pair : Fin (repeats (n + 1)), childProduct F2 (LeafDomain slots) chosen
        (values (pair, false)) (values (pair, true)) := by
  rw [squareSum, map_sum]
  rfl

theorem recursiveSum_stepSquareMap (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : ScalarTape repeats chosen q slots) :
    UniformChildSum.recursiveSum (𝕜 := F2) (LeafDomain slots)
        (stepSquareMap repeats chosen q slots ω) =
      RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain slots) ω := by
  let ordinary : (child : RecursiveSampler.OffPath chosen) → Square slots child.val :=
    (RecursiveSampler.splitEvaluatedTape F2 repeats chosen q (LeafDomain slots) ω).1
  let values : RecursiveSampler.CallIndex repeats n → H (childSlots slots chosen) :=
    (RecursiveSampler.splitEvaluatedTape F2 repeats chosen q (LeafDomain slots) ω).2
  have hself : stepSquareMap repeats chosen q slots ω chosen =
      squareSum repeats slots chosen values :=
    stepSquareMap_self repeats chosen q slots ω
  have hother (child : RecursiveSampler.OffPath chosen) :
      stepSquareMap repeats chosen q slots ω child.val = ordinary child :=
    stepSquareMap_other repeats chosen q slots ω child
  have heval : RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain slots) ω =
      (∑ child : RecursiveSampler.OffPath chosen,
        childSquareLift F2 (LeafDomain slots) child.val (ordinary child)) +
      ∑ pair : Fin (repeats (n + 1)), childProduct F2 (LeafDomain slots) chosen
        (values (pair, false)) (values (pair, true)) :=
    (RecursiveSampler.stepCombine_splitEvaluatedTape F2 repeats chosen q (LeafDomain slots) ω).symm.trans
      (RecursiveSamplerBiasAlgebra.combine_eq F2 (LeafDomain slots) chosen (repeats (n + 1))
        ordinary (fun pair => values (pair, false)) (fun pair => values (pair, true)))
  calc
    _ = ∑ child : Fin (branch n), childSquareLift F2 (LeafDomain slots) child
        (stepSquareMap repeats chosen q slots ω child) :=
      recursiveSum_eq_sum slots (stepSquareMap repeats chosen q slots ω)
    _ = childSquareLift F2 (LeafDomain slots) chosen (stepSquareMap repeats chosen q slots ω chosen) +
        ∑ child : RecursiveSampler.OffPath chosen, childSquareLift F2 (LeafDomain slots) child.val
          (stepSquareMap repeats chosen q slots ω child.val) :=
      Fintype.sum_eq_add_sum_subtype_ne _ chosen
    _ = childSquareLift F2 (LeafDomain slots) chosen (squareSum repeats slots chosen values) +
        ∑ child : RecursiveSampler.OffPath chosen,
          childSquareLift F2 (LeafDomain slots) child.val (ordinary child) :=
      congrArg₂ (fun a b : H slots => a + b)
        (congrArg (childSquareLift F2 (LeafDomain slots) chosen) hself)
        (Finset.sum_congr rfl (fun child _ =>
          congrArg (childSquareLift F2 (LeafDomain slots) child.val) (hother child)))
    _ = (∑ pair : Fin (repeats (n + 1)), childProduct F2 (LeafDomain slots) chosen
          (values (pair, false)) (values (pair, true))) +
        ∑ child : RecursiveSampler.OffPath chosen,
          childSquareLift F2 (LeafDomain slots) child.val (ordinary child) :=
      congrArg (fun z : H slots => z + ∑ child : RecursiveSampler.OffPath chosen,
        childSquareLift F2 (LeafDomain slots) child.val (ordinary child))
        (childSquareLift_squareSum repeats slots chosen values)
    _ = _ := (add_comm _ _).trans heval.symm

theorem recursiveSum_callContributions (calls : Nat) (repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Fin calls → ScalarTape repeats chosen q slots) (call : Fin calls) :
    UniformChildSum.recursiveSum (𝕜 := F2) (LeafDomain slots)
        (fun child => callContributions calls repeats chosen q slots ω child call) =
      RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain slots) (ω call) :=
  recursiveSum_stepSquareMap repeats chosen q slots (ω call)

theorem recursiveSum_callContributions_tuple (calls : Nat) (repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Fin calls → ScalarTape repeats chosen q slots) :
    (fun call => UniformChildSum.recursiveSum (𝕜 := F2) (LeafDomain slots)
      (fun child => callContributions calls repeats chosen q slots ω child call)) =
      (fun call => RecursiveSampler.evaluate F2 repeats (.step chosen q)
        (LeafDomain slots) (ω call)) := by
  funext call
  exact recursiveSum_callContributions calls repeats chosen q slots ω call

end
end PerfectCompleteness.OriginalChildScalarAssembly


namespace PerfectCompleteness.TreeShapeBounds

open TreeCardinality HierarchicalArrays
open scoped BigOperators

def leafCount (branch : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => branch n * leafCount branch n

def domainCountBound (branch : Nat → Nat) (n t : Nat) : Nat :=
  (7 ^ t) ^ leafCount branch n

def functionCountBound (branch : Nat → Nat) (n t : Nat) : Nat :=
  2 ^ domainCountBound branch n t

def arrayCountBound (branch : Nat → Nat) : (n t : Nat) → (Nat → Nat) → Nat
  | 0, _, _ => 1
  | n + 1, t, rows =>
      functionCountBound branch (n + 1) t ^ rows (n + 1) *
        arrayCountBound branch n t rows ^ branch n

theorem slots_card_eq_leafCount (branch : Nat → Nat) (n : Nat) :
    Fintype.card (RecursiveSpaces.Slots branch n) = leafCount branch n := by
  induction n with
  | zero =>
      change Fintype.card Unit = 1
      simp
  | succ n ih =>
      change Fintype.card (Fin (branch n) × RecursiveSpaces.Slots branch n) =
        branch n * leafCount branch n
      rw [Fintype.card_prod, Fintype.card_fin, ih]

theorem domainBound_eq (branch : Nat → Nat) (n t : Nat) :
    domainBound branch n t = domainCountBound branch n t := by
  simp only [domainBound, domainCountBound, slots_card_eq_leafCount]

theorem functionBound_eq (branch : Nat → Nat) (n t : Nat) :
    functionBound branch n t = functionCountBound branch n t := by
  rw [functionBound, functionCountBound, domainBound_eq]

@[simp] theorem domainBound_zero (branch : Nat → Nat) (t : Nat) :
    domainBound branch 0 t = 7 ^ t := by
  rw [domainBound_eq]
  simp [domainCountBound, leafCount]

theorem domainBound_succ (branch : Nat → Nat) (n t : Nat) :
    domainBound branch (n + 1) t = domainBound branch n t ^ branch n := by
  rw [domainBound_eq, domainBound_eq]
  change (7 ^ t) ^ (branch n * leafCount branch n) =
    ((7 ^ t) ^ leafCount branch n) ^ branch n
  rw [Nat.mul_comm (branch n) (leafCount branch n), pow_mul]

@[simp] theorem functionBound_zero (branch : Nat → Nat) (t : Nat) :
    functionBound branch 0 t = 2 ^ (7 ^ t) := by
  rw [functionBound, domainBound_zero]

theorem functionBound_succ (branch : Nat → Nat) (n t : Nat) :
    functionBound branch (n + 1) t = 2 ^ (domainBound branch n t ^ branch n) := by
  rw [functionBound, domainBound_succ]

@[simp] theorem arraysBound_zero (branch : Nat → Nat) (t : Nat) (rows : Nat → Nat) :
    arraysBound branch 0 t rows = 1 := by
  simp [arraysBound, Nodes]

theorem arraysBound_succ (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) :
    arraysBound branch (n + 1) t rows =
      functionBound branch (n + 1) t ^ rows (n + 1) *
        arraysBound branch n t rows ^ branch n := by
  change (∏ node : Unit ⊕ (Fin (branch n) × Nodes branch n),
      functionBound branch (Nodes.height (branch := branch) (n := n + 1) node) t ^
        rows (Nodes.height (branch := branch) (n := n + 1) node)) = _
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Fintype.prod_unique]
  change (functionBound branch (n + 1) t ^ rows (n + 1)) *
      (∏ _j : Fin (branch n), arraysBound branch n t rows) =
    (functionBound branch (n + 1) t ^ rows (n + 1)) *
      arraysBound branch n t rows ^ branch n
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem arraysBound_eq (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) :
    arraysBound branch n t rows = arrayCountBound branch n t rows := by
  induction n with
  | zero => exact arraysBound_zero branch t rows
  | succ n ih =>
      rw [arraysBound_succ, ih, functionBound_eq]
      rfl

theorem leafCount_congr {branch branch' : Nat → Nat} (n : Nat)
    (hbranch : ∀ k < n, branch k = branch' k) :
    leafCount branch n = leafCount branch' n := by
  revert hbranch
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hbranch
      have hlow : ∀ k < n, branch k = branch' k :=
        fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n))
      simp only [leafCount, hbranch n (Nat.lt_succ_self n), ih hlow]

theorem domainCountBound_congr {branch branch' : Nat → Nat} (n t : Nat)
    (hbranch : ∀ k < n, branch k = branch' k) :
    domainCountBound branch n t = domainCountBound branch' n t := by
  simp only [domainCountBound, leafCount_congr n hbranch]

theorem functionCountBound_congr {branch branch' : Nat → Nat} (n t : Nat)
    (hbranch : ∀ k < n, branch k = branch' k) :
    functionCountBound branch n t = functionCountBound branch' n t := by
  rw [functionCountBound, functionCountBound, domainCountBound_congr n t hbranch]

theorem arrayCountBound_congr {branch branch' rows rows' : Nat → Nat} (n t : Nat)
    (hbranch : ∀ k < n, branch k = branch' k)
    (hrows : ∀ k ≤ n, rows k = rows' k) :
    arrayCountBound branch n t rows = arrayCountBound branch' n t rows' := by
  revert hbranch hrows
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
      intro hbranch hrows
      have hlow : ∀ k < n, branch k = branch' k :=
        fun k hk => hbranch k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have hrowsLow : ∀ k ≤ n, rows k = rows' k :=
        fun k hk => hrows k (Nat.le_trans hk (Nat.le_succ n))
      simp only [arrayCountBound, functionCountBound_congr (n + 1) t hbranch,
        hrows (n + 1) le_rfl, ih hlow hrowsLow, hbranch n (Nat.lt_succ_self n)]

theorem domainBound_congr {branch branch' : Nat → Nat} (n t : Nat)
    (hbranch : ∀ k < n, branch k = branch' k) :
    domainBound branch n t = domainBound branch' n t := by
  rw [domainBound_eq, domainBound_eq]
  exact domainCountBound_congr n t hbranch

theorem functionBound_congr {branch branch' : Nat → Nat} (n t : Nat)
    (hbranch : ∀ k < n, branch k = branch' k) :
    functionBound branch n t = functionBound branch' n t := by
  rw [functionBound_eq, functionBound_eq]
  exact functionCountBound_congr n t hbranch

theorem arraysBound_congr {branch branch' rows rows' : Nat → Nat} (n t : Nat)
    (hbranch : ∀ k < n, branch k = branch' k)
    (hrows : ∀ k ≤ n, rows k = rows' k) :
    arraysBound branch n t rows = arraysBound branch' n t rows' := by
  rw [arraysBound_eq, arraysBound_eq]
  exact arrayCountBound_congr n t hbranch hrows

theorem update_agrees_below (branch : Nat → Nat) (n k value : Nat) (hnk : n ≤ k) :
    ∀ j < n, Function.update branch k value j = branch j := by
  intro j hj
  exact Function.update_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hj hnk)) value branch

theorem domainBound_update (branch : Nat → Nat) (n t k value : Nat) (hnk : n ≤ k) :
    domainBound (Function.update branch k value) n t = domainBound branch n t :=
  domainBound_congr n t (update_agrees_below branch n k value hnk)

theorem functionBound_update (branch : Nat → Nat) (n t k value : Nat) (hnk : n ≤ k) :
    functionBound (Function.update branch k value) n t = functionBound branch n t :=
  functionBound_congr n t (update_agrees_below branch n k value hnk)

theorem arraysBound_update (branch : Nat → Nat) (n t k value : Nat)
    (rows : Nat → Nat) (hnk : n ≤ k) :
    arraysBound (Function.update branch k value) n t rows = arraysBound branch n t rows :=
  arraysBound_congr n t (update_agrees_below branch n k value hnk) (fun _ _ => rfl)

end PerfectCompleteness.TreeShapeBounds


namespace PerfectCompleteness.ChildBlockCardinality

theorem shape_bound_pos (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) :
    0 < bound branch n t calls rows :=
  bound_pos calls rows (fun _ _ => MixedSupport.Slot.bit 0)

theorem bound_congr {branch branch' : Nat → Nat} (n t calls : Nat)
    {rows rows' : Nat → Nat} (hbranch : ∀ k < n, branch k = branch' k)
    (hrows : ∀ k ≤ n, rows k = rows' k) :
    bound branch n t calls rows = bound branch' n t calls rows' := by
  unfold bound
  rw [TreeShapeBounds.functionBound_congr n t hbranch,
    TreeShapeBounds.arraysBound_congr n t hbranch hrows]

theorem bound_update (branch : Nat → Nat) (n t calls k value : Nat)
    (rows : Nat → Nat) (hnk : n ≤ k) :
    bound (Function.update branch k value) n t calls rows =
      bound branch n t calls rows := by
  unfold bound
  rw [TreeShapeBounds.functionBound_update branch n t k value hnk,
    TreeShapeBounds.arraysBound_update branch n t k value rows hnk]


open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t calls : Nat} {rows : Nat → Nat}
    {slots : Slots branch n → Fin t → MixedSupport.Slot}

def zeroRaw (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) : Raw calls rows slots :=
  (fun _ => 0, fun _ _ => 0)

def allZero (x : Raw calls rows slots) : Bool := by
  classical
  exact decide ((∀ q, x.1 q = 0) ∧ ∀ node row, x.2 node row = 0)

theorem allZero_iff (x : Raw calls rows slots) :
    allZero x = true ↔ x = zeroRaw calls rows slots := by
  classical
  simp only [allZero, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, ha⟩
    apply Prod.ext
    · funext q
      exact hc q
    · funext node row
      exact ha node row
  · intro h
    subst x
    exact ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem probability_allZero :
    (FiniteDistribution.uniform (Raw calls rows slots)).probability allZero =
      1 / (Fintype.card (Raw calls rows slots) : ℝ) := by
  classical
  have hevent : (allZero : Raw calls rows slots → Bool) =
      fun x => decide (x = zeroRaw calls rows slots) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [allZero_iff, decide_eq_true_eq]
  rw [hevent]
  simp only [FiniteDistribution.probability, FiniteDistribution.uniform,
    decide_eq_true_eq, one_div]
  rw [Finset.sum_eq_single (zeroRaw calls rows slots)]
  · simp
  · intro x _ hx
    exact ite_eq_right hx
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

def cleanLowerBound (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) : ℝ :=
  1 / (bound branch n t calls rows : ℝ)

theorem cleanLowerBound_pos (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) :
    0 < cleanLowerBound branch n t calls rows :=
  one_div_pos.mpr (Nat.cast_pos.mpr (shape_bound_pos branch n t calls rows))

theorem cleanLowerBound_le_one (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) :
    cleanLowerBound branch n t calls rows ≤ 1 := by
  have hpos : (0 : ℝ) < bound branch n t calls rows :=
    Nat.cast_pos.mpr (shape_bound_pos branch n t calls rows)
  apply (div_le_one hpos).2
  exact_mod_cast Nat.succ_le_of_lt (shape_bound_pos branch n t calls rows)

theorem cleanLowerBound_le_probability :
    cleanLowerBound branch n t calls rows ≤
      (FiniteDistribution.uniform (Raw calls rows slots)).probability allZero := by
  rw [probability_allZero]
  exact one_div_le_one_div_of_le (Nat.cast_pos.mpr Fintype.card_pos)
    (by exact_mod_cast fintype_card_le calls rows slots)

theorem cleanLowerBound_update (branch : Nat → Nat) (n t calls k value : Nat)
    (rows : Nat → Nat) (hnk : n ≤ k) :
    cleanLowerBound (Function.update branch k value) n t calls rows =
      cleanLowerBound branch n t calls rows := by
  unfold cleanLowerBound
  rw [bound_update branch n t calls k value rows hnk]

end
end PerfectCompleteness.ChildBlockCardinality


namespace PerfectCompleteness.FixedBranching

open AscendingBranching ChildBlockCardinality

noncomputable section

def extend {n : Nat} (prior : Fin n → Nat) : Nat → Nat :=
  fun k => if h : k < n then prior ⟨k, h⟩ else 0

def cleanRate (cost : Nat) (L : ℝ) : ℝ := 1 / ((48000 : ℝ) * cost * L)

theorem cleanRate_pos {cost : Nat} (hcost : 0 < cost) {L : ℝ} (hL : 0 < L) :
    0 < cleanRate cost L := by
  have : (0 : ℝ) < cost := by exact_mod_cast hcost
  unfold cleanRate
  positivity

theorem cleanRate_le_one {cost : Nat} (hcost : 0 < cost) {L : ℝ} (hL : 1 ≤ L) :
    cleanRate cost L ≤ 1 := by
  have hc : (1 : ℝ) ≤ cost := by exact_mod_cast hcost
  have hp : (1 : ℝ) ≤ (cost : ℝ) * L := by nlinarith
  unfold cleanRate
  apply (div_le_one (by positivity)).2
  nlinarith

theorem exists_branching (t cost : Nat) (rows calls : Nat → Nat)
    (hcost : 0 < cost) {ε : ℝ} (hε : 0 < ε) :
    ∃ size : Nat → Nat, ∀ n,
      CubeErrors (bound (fun k => size k ^ 3) n t (calls n) rows : ℝ)
        (cleanRate cost (bound (fun k => size k ^ 3) n t (calls n) rows : ℝ)) ε (size n) := by
  let L := fun n (prior : Fin n → Nat) => (bound (extend prior) n t (calls n) rows : ℝ)
  have hL : ∀ n prior, 0 < L n prior := by
    intro n prior
    dsimp [L]
    exact_mod_cast shape_bound_pos (extend prior) n t (calls n) rows
  have hL1 : ∀ n prior, 1 ≤ L n prior := by
    intro n prior
    dsimp [L]
    exact_mod_cast Nat.succ_le_of_lt (shape_bound_pos (extend prior) n t (calls n) rows)
  obtain ⟨size, hsize⟩ := exists_ascending_cubes L
    (fun n prior => cleanRate cost (L n prior))
    (fun n prior => (hL n prior).le)
    (fun n prior => cleanRate_pos hcost (hL n prior))
    (fun n prior => cleanRate_le_one hcost (hL1 n prior)) hε
  refine ⟨size, fun n => ?_⟩
  have hbound : bound (extend (fun i : Fin n => size i.val ^ 3)) n t (calls n) rows =
      bound (fun k => size k ^ 3) n t (calls n) rows := by
    apply bound_congr n t (calls n)
    · intro k hk
      simp only [extend, dite_eq_left hk]
    · intro k hk
      rfl
  simpa only [L, hbound] using hsize n

theorem rational_probability {m : Nat} (hm : 2 ≤ m) :
    0 < (1 : ℚ) / (m : ℚ) ^ 2 ∧ (1 : ℚ) / (m : ℚ) ^ 2 < 1 := by
  have hmr : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℚ) < (m : ℚ) ^ 2 := by positivity
  constructor
  · positivity
  · apply (div_lt_one hp).2
    nlinarith

end
end PerfectCompleteness.FixedBranching


namespace PerfectCompleteness.FixedSourceBranching

open FixedRows AscendingBranching ChildBlockCardinality

noncomputable section

variable {δ : ℚ} (plan : Plan δ) (hδ : 0 < δ)

theorem source_rate (cost : Nat) (hcost : 0 < cost)
    (hbudget : SourceOddLists.alphabetLog (cutoff plan hδ) (sourceLength plan hδ) ≤ cost)
    (input : List Bool) (unsat : ¬BinaryLanguage.language input) (k : Nat) :
    ((SourceOddLists.game (cutoff plan hδ)
      (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
      (sourceLength plan hδ)).repetition k).value ≤
      (RepetitionRate.halfRate cost : ℝ) ^ k :=
  SourceOddLists.repetition_halfRate
    (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) PCPSource.sourceGap
    PCPSource.sourceGap_pos PCPSource.sourceGap_le_one
    (PCPSourceMachine.rawSource_clauseGap input unsat) hcost hbudget k

theorem exists_source_branching (calls : Nat → Nat) {ε : ℝ} (hε : 0 < ε) :
    ∃ cost : Nat, 0 < cost ∧
      SourceOddLists.alphabetLog (cutoff plan hδ) (sourceLength plan hδ) ≤ cost ∧
      ∃ size : Nat → Nat, ∀ n,
        CubeErrors
          (bound (fun k => size k ^ 3) n (sourceLength plan hδ) (calls n) (rows plan) : ℝ)
          (FixedBranching.cleanRate cost
            (bound (fun k => size k ^ 3) n (sourceLength plan hδ) (calls n) (rows plan) : ℝ))
          ε (size n) := by
  obtain ⟨cost, hcost, hbudget⟩ :=
    SourceOddLists.exists_alphabet_budget (cutoff plan hδ) (sourceLength plan hδ)
  obtain ⟨size, hsize⟩ := FixedBranching.exists_branching
    (sourceLength plan hδ) cost (rows plan) calls hcost hε
  exact ⟨cost, hcost, hbudget, size, hsize⟩

end
end PerfectCompleteness.FixedSourceBranching

end OAI
