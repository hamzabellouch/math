import OAI.Combinatorics.EditApproximation.Coarse.CoarseEstimator

namespace OAI

/-!
# Pathwise accuracy of the concrete coarse recurrence

The events concern only fixed true child minima sampled with independent
labels. The deterministic reconstruction requires no independence of
approximate child costs.
-/

namespace EditApproximation

open Finset

universe u

/-- The true-cost threshold sum appearing in the simultaneous event. -/
noncomputable def coarseTrueThresholdSum {B D : ℕ} {α : Type u}
    (k : ℕ) (Q : ℚ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (allowance : ℚ) (transform : ℝ → ℝ) :
    List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D) →
      ℕ → Fin (2 * k + 1) → ℝ
  | [], _, _ => 0
  | (child, draw, _) :: rest, start, shift =>
    thresholdContribution (coarseChildThreshold B Q allowance draw) (allowance / Q)
      (transform ((univ.inf' univ_nonempty
        (fun next => trueValue child start next + 2 * Nat.dist shift.val next.val) : ℕ) : ℝ)) +
      coarseTrueThresholdSum k Q trueValue allowance transform rest (start + child.word.length) shift

/-- Child accuracy at precisely the source positions visited by the
actual traversal, with its actual per-child allowance. -/
noncomputable def CoarseChildAccuracy {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (allowance : ℚ) (f : ℝ) :
    List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D) → ℕ → Prop
  | [], _ => True
  | (child, draw, below) :: rest, start =>
    (∀ shift,
      (trueValue child start shift : ℝ) / f -
          ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ) ≤
        value child below (lam * coarseChildThreshold B Q allowance draw) start shift ∧
      (value child below (lam * coarseChildThreshold B Q allowance draw) start shift : ℝ) ≤
        f * trueValue child start shift + ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ)) ∧
    CoarseChildAccuracy k Q lam trueValue value allowance f rest (start + child.word.length)

/-- The actual rational estimator is trapped between two sums of fixed
true costs, even when each child estimate depends on its threshold. -/
theorem coarseThresholdChildrenCost_sandwich {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (allowance : ℚ) (f : ℝ)
    (hQ : 0 ≤ Q) (ha : 0 ≤ allowance) (hf : 1 ≤ f)
    (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (start : ℕ) (shift : Fin (2 * k + 1))
    (hchild : CoarseChildAccuracy k Q lam trueValue value allowance f children start) :
    coarseTrueThresholdSum k Q trueValue allowance
        (fun cost => cost / (f * (1 + (lam : ℝ)))) children start shift ≤
      ((coarseThresholdChildrenCost k Q lam value allowance children start shift : ℚ) : ℝ) ∧
    ((coarseThresholdChildrenCost k Q lam value allowance children start shift : ℚ) : ℝ) ≤
      coarseTrueThresholdSum k Q trueValue allowance
        (fun cost => f * cost / (1 - (lam : ℝ))) children start shift := by
  induction children generalizing start with
  | nil => simp only [coarseTrueThresholdSum, coarseThresholdChildrenCost, Rat.cast_zero]; exact ⟨le_rfl, le_rfl⟩
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    have hminimum := coarse_penalty_minimum_error (trueValue child start)
      (fun next => 2 * Nat.dist shift.val next.val)
      (value child below (lam * coarseChildThreshold B Q allowance draw) start)
      f ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ) hf
      (fun next => (hchild.1 next).1)
      (fun next => (hchild.1 next).2)
    have hfpos : 0 < f := lt_of_lt_of_le zero_lt_one hf
    have hscale : (0 : ℝ) ≤ ((allowance / Q : ℚ) : ℝ) := by exact_mod_cast div_nonneg ha hQ
    have hstep := coarse_threshold_sandwich hscale hfpos
      (by exact_mod_cast hlam : (0 : ℝ) ≤ lam)
      (by exact_mod_cast hlamone : (lam : ℝ) < 1)
      (by simpa only [Rat.cast_mul] using hminimum.1)
      (by simpa only [Rat.cast_mul] using hminimum.2)
    have hrest := ih (start + child.word.length) hchild.2
    simp only [coarseThresholdChildrenCost, coarseTrueThresholdSum,
      Rat.cast_add, coarseThresholdContribution_cast, Rat.cast_div]
    simp only [Rat.cast_div] at hstep
    exact ⟨add_le_add hstep.1 hrest.1, add_le_add hstep.2 hrest.2⟩

/-- Combining the true-cost concentration events gives the exact
structural-factor update for the executable rational child traversal. -/
theorem coarseThresholdChildrenCost_reconstruction {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (allowance : ℚ) (f : ℝ)
    (hQ : 0 ≤ Q) (ha : 0 ≤ allowance) (hf : 1 ≤ f)
    (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (start : ℕ) (shift : Fin (2 * k + 1))
    (hchild : CoarseChildAccuracy k Q lam trueValue value allowance f children start)
    (hconcentrationLower :
      (1 - (lam : ℝ)) *
        (((coarseChildrenCost k trueValue (children.map Prod.fst) start shift : ℕ) : ℝ) /
          (f * (1 + (lam : ℝ)))) - allowance ≤
        coarseTrueThresholdSum k Q trueValue allowance
          (fun cost => cost / (f * (1 + (lam : ℝ)))) children start shift)
    (hconcentrationUpper :
      coarseTrueThresholdSum k Q trueValue allowance
          (fun cost => f * cost / (1 - (lam : ℝ))) children start shift ≤
        (1 + (lam : ℝ)) *
          (f * ((coarseChildrenCost k trueValue (children.map Prod.fst) start shift : ℕ) : ℝ) /
            (1 - (lam : ℝ))) + allowance) :
    ((coarseChildrenCost k trueValue (children.map Prod.fst) start shift : ℕ) : ℝ) /
        (f * (1 + (lam : ℝ)) / (1 - (lam : ℝ))) - allowance ≤
      ((coarseThresholdChildrenCost k Q lam value allowance children start shift : ℚ) : ℝ) ∧
    ((coarseThresholdChildrenCost k Q lam value allowance children start shift : ℚ) : ℝ) ≤
      (f * (1 + (lam : ℝ)) / (1 - (lam : ℝ))) *
        ((coarseChildrenCost k trueValue (children.map Prod.fst) start shift : ℕ) : ℝ) + allowance := by
  have hsandwich := coarseThresholdChildrenCost_sandwich k Q lam trueValue value children allowance f
    hQ ha hf hlam hlamone start shift hchild
  have hfpos : 0 < f := lt_of_lt_of_le zero_lt_one hf
  have hl : (lam : ℝ) < 1 := by exact_mod_cast hlamone
  have hlnonnegative : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hlower := hconcentrationLower.trans hsandwich.1
  have hupper := hsandwich.2.trans hconcentrationUpper
  constructor
  · convert hlower using 1
    field_simp
  · convert hupper using 1
    ring

/-- The exact depth factor in Section 3. -/
noncomputable def coarseStructuralFactor (lam : ℚ) (D : ℕ) : ℝ :=
  ((1 + (lam : ℝ)) / (1 - (lam : ℝ))) ^ D

theorem coarseStructuralFactor_one_le (lam : ℚ) (D : ℕ)
    (hlam : 0 ≤ lam) (hlamone : lam < 1) : 1 ≤ coarseStructuralFactor lam D := by
  have hl : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hlone : (lam : ℝ) < 1 := by exact_mod_cast hlamone
  apply one_le_pow₀
  apply (le_div_iff₀ (sub_pos.mpr hlone)).2
  nlinarith

theorem coarseStructuralFactor_succ (lam : ℚ) (D : ℕ) :
    coarseStructuralFactor lam (D + 1) =
      coarseStructuralFactor lam D * (1 + (lam : ℝ)) / (1 - (lam : ℝ)) := by
  simp only [coarseStructuralFactor, pow_succ]
  ring

/-- Events for all children, including children below a pruned node. -/
def CoarseDescendantEvents {B D : ℕ} {α : Type u} (Q lam allowance : ℚ)
    (event : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Prop) :
    List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D) → ℕ → Prop
  | [], _ => True
  | (child, draw, below) :: rest, start =>
    event child below (lam * coarseChildThreshold B Q allowance draw) start ∧
      CoarseDescendantEvents Q lam allowance event rest (start + child.word.length)

/-- The actual finite-tree event. At every node it uses only deterministic
true-cost minima and the node's current child threshold labels. -/
noncomputable def CoarseAccuracyEvent {B : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α)) :
    {D : ℕ} → CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Prop
  | _, .leaf _, _, _, _ => True
  | D + 1, .branch children, (draws, below), allowance, start =>
    let data := List.ofFn (fun i => (children i, draws i, below i))
    let trueValue := fun child => coarseShiftCost k frame child
    let f := coarseStructuralFactor lam D
    CoarseDescendantEvents Q lam allowance
      (fun child => CoarseAccuracyEvent k Q lam frame child) data start ∧
    ∀ shift,
      (1 - (lam : ℝ)) *
          (((coarseChildrenCost k trueValue (data.map Prod.fst) start shift : ℕ) : ℝ) /
            (f * (1 + (lam : ℝ)))) - allowance ≤
        coarseTrueThresholdSum k Q trueValue allowance
          (fun cost => cost / (f * (1 + (lam : ℝ)))) data start shift ∧
      coarseTrueThresholdSum k Q trueValue allowance
          (fun cost => f * cost / (1 - (lam : ℝ))) data start shift ≤
        (1 + (lam : ℝ)) *
          (f * ((coarseChildrenCost k trueValue (data.map Prod.fst) start shift : ℕ) : ℝ) /
            (1 - (lam : ℝ))) + allowance

theorem CoarseDescendantEvents.to_accuracy {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam allowance : ℚ) (f : ℝ)
    (trueValue : CoarseSourceTree B α D → ℕ → Fin (2 * k + 1) → ℕ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (event : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Prop)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (hchild : ∀ child draw below, (child, draw, below) ∈ children → ∀ start,
      event child below (lam * coarseChildThreshold B Q allowance draw) start → ∀ shift,
        (trueValue child start shift : ℝ) / f -
          ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ) ≤
            value child below (lam * coarseChildThreshold B Q allowance draw) start shift ∧
        (value child below (lam * coarseChildThreshold B Q allowance draw) start shift : ℝ) ≤
          f * trueValue child start shift + ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ))
    (start : ℕ) (hevent : CoarseDescendantEvents Q lam allowance event children start) :
    CoarseChildAccuracy k Q lam trueValue value allowance f children start := by
  induction children generalizing start with
  | nil => trivial
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    exact ⟨hchild child draw below (by simp) start hevent.1,
      ih (fun child draw below hmem => hchild child draw below (by simp [hmem]))
        (start + child.word.length) hevent.2⟩

/-- On the concrete true-cost event, the literal rational pruned
estimator has exactly the claimed depth-dependent error at every shift. -/
theorem coarseThresholdEstimate_accurate {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α))
    (tree : CoarseSourceTree B α D) (draws : CoarseThresholdDraws B D)
    (allowance : ℚ) (start : ℕ)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) (hlamone : lam < 1) (ha : 0 ≤ allowance)
    (hevent : CoarseAccuracyEvent k Q lam frame tree draws allowance start) :
    ∀ shift : Fin (2 * k + 1),
      (coarseShiftCost k frame tree start shift : ℝ) / coarseStructuralFactor lam D - allowance ≤
          coarseThresholdEstimate k Q lam frame tree draws allowance start shift ∧
      (coarseThresholdEstimate k Q lam frame tree draws allowance start shift : ℝ) ≤
        coarseStructuralFactor lam D * coarseShiftCost k frame tree start shift + allowance := by
  induction tree generalizing allowance start with
  | leaf letter =>
    intro shift
    have haReal : (0 : ℝ) ≤ allowance := by exact_mod_cast ha
    simp only [coarseThresholdEstimate, coarseStructuralFactor, pow_zero, div_one, one_mul]
    split_ifs with hprune
    · have hwidth := coarseShiftCost_le_width k frame (.leaf (B := B) letter) start shift
      have hwidthQ : (coarseShiftCost k frame (.leaf (B := B) letter) start shift : ℚ) ≤
          (CoarseSourceTree.leaf (B := B) letter).word.length := by exact_mod_cast hwidth
      have hwidthReal : (coarseShiftCost k frame (.leaf (B := B) letter) start shift : ℝ) ≤ allowance := by
        exact_mod_cast hwidthQ.trans hprune
      simp only [Rat.cast_zero]
      constructor <;> linarith [show (0 : ℝ) ≤ coarseShiftCost k frame (.leaf (B := B) letter) start shift by positivity]
    · simp only [Rat.cast_natCast]
      constructor <;> linarith
  | @branch D children ih =>
    obtain ⟨draws, below⟩ := draws
    have hfactor := coarseStructuralFactor_one_le lam (D + 1) hlam hlamone
    have hfactorPos : 0 < coarseStructuralFactor lam (D + 1) := lt_of_lt_of_le zero_lt_one hfactor
    have haReal : (0 : ℝ) ≤ allowance := by exact_mod_cast ha
    intro shift
    by_cases hprune : ((CoarseSourceTree.branch children).word.length : ℚ) ≤ allowance
    · simp only [coarseThresholdEstimate, hprune, ↓reduceIte, Rat.cast_zero]
      have hwidth := coarseShiftCost_le_width k frame (.branch children) start shift
      have hwidthQ : (coarseShiftCost k frame (.branch children) start shift : ℚ) ≤
          (CoarseSourceTree.branch children).word.length := by exact_mod_cast hwidth
      have hwidthReal : (coarseShiftCost k frame (.branch children) start shift : ℝ) ≤ allowance := by
        exact_mod_cast hwidthQ.trans hprune
      have htrueNonnegative : (0 : ℝ) ≤ coarseShiftCost k frame (.branch children) start shift := by positivity
      have hdiv : (coarseShiftCost k frame (.branch children) start shift : ℝ) /
          coarseStructuralFactor lam (D + 1) ≤ coarseShiftCost k frame (.branch children) start shift := by
        apply (div_le_iff₀ hfactorPos).2
        nlinarith
      exact ⟨by linarith, by positivity⟩
    · have hdescendant := hevent.1
      have hchildAccuracy := CoarseDescendantEvents.to_accuracy k Q lam allowance
        (coarseStructuralFactor lam D) (fun child => coarseShiftCost k frame child)
        (fun child => coarseThresholdEstimate k Q lam frame child)
        (fun child => CoarseAccuracyEvent k Q lam frame child)
        (List.ofFn fun i => (children i, draws i, below i))
        (by
          intro child draw childBelow hmem childStart hchildEvent
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          exact ih i (below i) _ childStart
            (mul_nonneg hlam (coarseChildThreshold_nonneg (draws i) hQ ha)) hchildEvent)
        start hdescendant
      have hstep := coarseThresholdChildrenCost_reconstruction k Q lam
        (fun child => coarseShiftCost k frame child)
        (fun child => coarseThresholdEstimate k Q lam frame child)
        (List.ofFn fun i => (children i, draws i, below i)) allowance
        (coarseStructuralFactor lam D) hQ ha (coarseStructuralFactor_one_le lam D hlam hlamone)
        hlam hlamone start shift hchildAccuracy (hevent.2 shift).1 (hevent.2 shift).2
      simpa only [coarseThresholdEstimate, hprune, ↓reduceIte, List.map_ofFn,
        Function.comp_def, coarseShiftCost, coarseStructuralFactor_succ] using hstep

end EditApproximation

end OAI
