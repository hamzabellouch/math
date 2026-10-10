import OAI.Combinatorics.EditApproximation.Coarse.CoarseSeed
import OAI.Combinatorics.EditApproximation.Geometry.Seed
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# The concrete pruned coarse estimator

The random labels are a finite complete tree of integers in `1,...,B`.
Every execution below uses rational arithmetic and literal finite minima;
pruned arrays are represented by the zero function. Accuracy events are
kept separate from this executable definition.
-/

namespace EditApproximation

open Finset

universe u

/- All threshold labels, including labels below nodes which may be pruned. -/


/-- Rational version of the literal threshold contribution. -/


theorem coarseThresholdContribution_cast (threshold scale value : ℚ) :
    (coarseThresholdContribution threshold scale value : ℝ) =
      thresholdContribution threshold scale value := by
  by_cases h : threshold ≤ value
  · have hreal : (threshold : ℝ) ≤ value := by exact_mod_cast h
    simp only [coarseThresholdContribution, thresholdContribution, h, hreal,
      ↓reduceIte, Rat.cast_max]
  · have hreal : ¬(threshold : ℝ) ≤ value := by exact_mod_cast h
    simp only [coarseThresholdContribution, thresholdContribution, h, hreal,
      ↓reduceIte, Rat.cast_zero]

theorem coarseThresholdContribution_nonneg {threshold scale value : ℚ}
    (hscale : 0 ≤ scale) : 0 ≤ coarseThresholdContribution threshold scale value := by
  unfold coarseThresholdContribution
  split_ifs
  · exact hscale.trans (le_max_right _ _)
  · rfl

/- Exact finite threshold selected by a child label. -/


/- Internal child traversal, retaining actual source starts. -/


/-- Section 3's pruned rational recurrence. All labels are supplied
beforehand; execution exposes a label only when its parent is expanded. -/


theorem coarseChildThreshold_nonneg {B : ℕ} {Q allowance : ℚ} (draw : Fin B)
    (hQ : 0 ≤ Q) (ha : 0 ≤ allowance) : 0 ≤ coarseChildThreshold B Q allowance draw := by
  unfold coarseChildThreshold
  positivity

theorem coarseChildThreshold_pos {B : ℕ} {Q allowance : ℚ} (draw : Fin B)
    (hQ : 0 < Q) (ha : 0 < allowance) : 0 < coarseChildThreshold B Q allowance draw := by
  have hB : 0 < B := Nat.zero_lt_of_lt draw.isLt
  unfold coarseChildThreshold
  positivity

theorem coarseThresholdChildrenCost_nonneg {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (allowance : ℚ) (start : ℕ) (shift : Fin (2 * k + 1))
    (hQ : 0 ≤ Q) (ha : 0 ≤ allowance) :
    0 ≤ coarseThresholdChildrenCost k Q lam value allowance children start shift := by
  induction children generalizing start with
  | nil => rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    simp only [coarseThresholdChildrenCost]
    exact add_nonneg (coarseThresholdContribution_nonneg (div_nonneg ha hQ))
      (ih (start + child.word.length))

theorem coarseThresholdEstimate_nonneg {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α))
    (tree : CoarseSourceTree B α D) (draws : CoarseThresholdDraws B D)
    (allowance : ℚ) (start : ℕ) (shift : Fin (2 * k + 1))
    (hQ : 0 ≤ Q) (ha : 0 ≤ allowance) :
    0 ≤ coarseThresholdEstimate k Q lam frame tree draws allowance start shift := by
  cases tree with
  | leaf letter =>
    simp only [coarseThresholdEstimate]
    split_ifs
    · rfl
    · positivity
  | branch children =>
    obtain ⟨draws, below⟩ := draws
    simp only [coarseThresholdEstimate]
    split_ifs
    · rfl
    · exact coarseThresholdChildrenCost_nonneg k Q lam _ _ allowance start shift hQ ha

/-- Adding a nonnegative connection penalty and taking the actual
finite minimum preserves the multiplicative/additive child guarantee. -/
theorem coarse_penalty_minimum_error {ι : Type*} [Fintype ι] [Nonempty ι]
    (trueCost penalty : ι → ℕ) (estimate : ι → ℚ) (f error : ℝ)
    (hf : 1 ≤ f)
    (hlower : ∀ i, (trueCost i : ℝ) / f - error ≤ estimate i)
    (hupper : ∀ i, (estimate i : ℝ) ≤ f * trueCost i + error) :
    ((univ.inf' univ_nonempty (fun i => trueCost i + penalty i) : ℕ) : ℝ) / f - error ≤
        ((univ.inf' univ_nonempty (fun i => estimate i + (penalty i : ℚ)) : ℚ) : ℝ) ∧
      ((univ.inf' univ_nonempty (fun i => estimate i + (penalty i : ℚ)) : ℚ) : ℝ) ≤
        f * ((univ.inf' univ_nonempty (fun i => trueCost i + penalty i) : ℕ) : ℝ) + error := by
  have hfpos : 0 < f := lt_of_lt_of_le zero_lt_one hf
  constructor
  · obtain ⟨i, hi, hmin⟩ := exists_mem_eq_inf' (s := univ) univ_nonempty
      (fun i => estimate i + (penalty i : ℚ))
    rw [hmin]
    have htrue : ((univ.inf' univ_nonempty (fun i => trueCost i + penalty i) : ℕ) : ℝ) ≤
        (trueCost i : ℝ) + penalty i := by
      exact_mod_cast inf'_le (fun i => trueCost i + penalty i) hi
    have hpen : (penalty i : ℝ) / f ≤ penalty i := by
      apply (div_le_iff₀ hfpos).2
      nlinarith [show (0 : ℝ) ≤ penalty i by positivity]
    simp only [Rat.cast_add, Rat.cast_natCast]
    calc
      _ ≤ ((trueCost i : ℝ) + penalty i) / f - error :=
        sub_le_sub_right (div_le_div_of_nonneg_right htrue hfpos.le) _
      _ = (trueCost i : ℝ) / f - error + (penalty i : ℝ) / f := by ring
      _ ≤ _ := add_le_add (hlower i) hpen
  · obtain ⟨i, hi, hmin⟩ := exists_mem_eq_inf' (s := univ) univ_nonempty
      (fun i => trueCost i + penalty i)
    rw [hmin]
    have hestimate : ((univ.inf' univ_nonempty (fun i => estimate i + (penalty i : ℚ)) : ℚ) : ℝ) ≤
        (estimate i : ℝ) + penalty i := by
      exact_mod_cast inf'_le (fun i => estimate i + (penalty i : ℚ)) hi
    simp only [Nat.cast_add]
    exact hestimate.trans (by nlinarith [hupper i, show (0 : ℝ) ≤ penalty i by positivity])

/-- A zero literal penalty minimum forces the zero-cost child to use
the parent's same shift. -/
theorem coarse_penalty_minimum_zero (k : ℕ) (value : Fin (2 * k + 1) → ℕ)
    (shift : Fin (2 * k + 1))
    (hzero : univ.inf' univ_nonempty
      (fun next => value next + 2 * Nat.dist shift.val next.val) = 0) : value shift = 0 := by
  obtain ⟨next, _, hmin⟩ := exists_mem_eq_inf' (s := univ) univ_nonempty
    (fun next => value next + 2 * Nat.dist shift.val next.val)
  have hdistance : Nat.dist shift.val next.val = 0 := by omega
  have hequal : shift = next := Fin.ext (Nat.eq_of_dist_eq_zero hdistance)
  rw [← hequal] at hmin
  simp only [Nat.dist_self, mul_zero, add_zero] at hmin
  omega

/-- If the same-shift child estimate is zero, its actual minimum is zero. -/
theorem coarse_estimated_minimum_zero (k : ℕ) (value : Fin (2 * k + 1) → ℚ)
    (shift : Fin (2 * k + 1)) (hnonnegative : ∀ next, 0 ≤ value next)
    (hzero : value shift = 0) :
    univ.inf' univ_nonempty (fun next => value next + (2 * Nat.dist shift.val next.val : ℕ)) = 0 := by
  apply le_antisymm
  · have hminimum := inf'_le
      (fun next => value next + (2 * Nat.dist shift.val next.val : ℕ)) (mem_univ shift)
    simpa only [Nat.dist_self, mul_zero, Nat.cast_zero, hzero, add_zero] using hminimum
  · apply le_inf'
    intro next hnext
    exact add_nonneg (hnonnegative next) (by positivity)

theorem coarseThresholdChildrenCost_zero {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (hchildNonnegative : ∀ child draw below, (child, draw, below) ∈ children →
      ∀ allowance start shift, 0 < allowance → 0 ≤ value child below allowance start shift)
    (hchildZero : ∀ child draw below, (child, draw, below) ∈ children →
      ∀ allowance start shift, 0 < allowance → trueValue child start shift = 0 →
        value child below allowance start shift = 0)
    (allowance : ℚ) (start : ℕ) (shift : Fin (2 * k + 1))
    (hQ : 0 < Q) (hlam : 0 < lam) (ha : 0 < allowance)
    (hzero : coarseChildrenCost k trueValue (children.map Prod.fst) start shift = 0) :
    coarseThresholdChildrenCost k Q lam value allowance children start shift = 0 := by
  induction children generalizing start with
  | nil => rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    simp only [List.map_cons, coarseChildrenCost] at hzero
    have hfirstTrue : trueValue child start shift = 0 :=
      coarse_penalty_minimum_zero k (trueValue child start) shift (by omega)
    have hthreshold : 0 < coarseChildThreshold B Q allowance draw :=
      coarseChildThreshold_pos draw hQ ha
    have hchildAllowance : 0 < lam * coarseChildThreshold B Q allowance draw :=
      mul_pos hlam hthreshold
    have hminimum := coarse_estimated_minimum_zero k
      (value child below (lam * coarseChildThreshold B Q allowance draw) start) shift
      (fun next => hchildNonnegative child draw below (by simp) _ start next hchildAllowance)
      (hchildZero child draw below (by simp) _ start shift hchildAllowance hfirstTrue)
    have hrest := ih
      (fun child draw below hmem => hchildNonnegative child draw below (by simp [hmem]))
      (fun child draw below hmem => hchildZero child draw below (by simp [hmem]))
      (start + child.word.length) (by omega)
    simp only [coarseThresholdChildrenCost, hminimum, hrest, add_zero,
      coarseThresholdContribution, not_le_of_gt hthreshold, ↓reduceIte]

/-- Exact zero states remain zero on every label realization, without
conditioning on any accuracy event. -/
theorem coarseThresholdEstimate_zero {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α))
    (tree : CoarseSourceTree B α D) (draws : CoarseThresholdDraws B D)
    (allowance : ℚ) (start : ℕ) (shift : Fin (2 * k + 1))
    (hQ : 0 < Q) (hlam : 0 < lam) (ha : 0 < allowance)
    (hzero : coarseShiftCost k frame tree start shift = 0) :
    coarseThresholdEstimate k Q lam frame tree draws allowance start shift = 0 := by
  induction tree generalizing allowance start shift with
  | leaf letter =>
    simp only [coarseThresholdEstimate]
    split_ifs
    · rfl
    · exact_mod_cast hzero
  | branch children ih =>
    obtain ⟨draws, below⟩ := draws
    simp only [coarseThresholdEstimate]
    split_ifs
    · rfl
    · refine coarseThresholdChildrenCost_zero k Q lam
        (fun child => coarseShiftCost k frame child)
        (fun child => coarseThresholdEstimate k Q lam frame child) _
        (fun child _ childBelow _ allowance start shift ha =>
          coarseThresholdEstimate_nonneg k Q lam frame child childBelow allowance start shift hQ.le ha.le)
        ?_ allowance start shift hQ hlam ha ?_
      · intro child draw childBelow hmem allowance start shift ha hzero
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
        cases hi
        exact ih i (below i) allowance start shift ha hzero
      · simpa only [List.map_ofFn, Function.comp_def, coarseShiftCost] using hzero

end EditApproximation

end OAI
