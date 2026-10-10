import OAI.Combinatorics.EditApproximation.Coarse.CoarseProbability
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Expected active work in the concrete pruned coarse tree

The counter records the array units of the actual execution; pruning stops
all descendant visits. Constant child overhead is charged to its expanded
parent. The linear-sweep proof converts these units to rational operations;
bit/RAM charging is separate.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

universe u



/- Array units actually incurred before pruning terminates a subtree. -/


/-- Finite conditional expectation recurrence for the same active work.
The root labels are independent uniforms, and each child uses its own
independent recursive label tree. -/
noncomputable def coarseExpectedArrayWork {B : ℕ} {α : Type u} (k : ℕ) (Q lam : ℚ) :
    {D : ℕ} → CoarseSourceTree B α D → ℚ → ℝ
  | _, tree, allowance =>
    if (tree.word.length : ℚ) ≤ allowance then 0 else
    match tree with
    | .leaf _ => (B * (2 * k + 1) : ℕ)
    | .branch children =>
      (B * (2 * k + 1) : ℕ) +
        ∑ i : Fin B, uniformMean (fun draw : Fin B =>
          coarseExpectedArrayWork k Q lam (children i)
            (lam * coarseChildThreshold B Q allowance draw))

noncomputable def coarseInverseAllowanceFactor (B : ℕ) (Q lam : ℚ) : ℝ :=
  (Q : ℝ) / lam * ∑ r ∈ Icc 1 B, (1 : ℝ) / r

noncomputable def coarseWorkMultiplier (factor : ℝ) (D : ℕ) : ℝ :=
  ∑ r ∈ range (D + 1), factor ^ r

theorem coarseWorkMultiplier_nonneg (factor : ℝ) (D : ℕ) (hfactor : 0 ≤ factor) :
    0 ≤ coarseWorkMultiplier factor D :=
  sum_nonneg (fun _ _ => pow_nonneg hfactor _)

theorem coarseWorkMultiplier_succ (factor : ℝ) (D : ℕ) :
    coarseWorkMultiplier factor (D + 1) = 1 + factor * coarseWorkMultiplier factor D := by
  simp only [coarseWorkMultiplier]
  rw [sum_range_succ']
  simp only [pow_zero, pow_succ', ← mul_sum]
  ring

theorem coarseWorkMultiplier_le (factor : ℝ) (D : ℕ) (hfactor : 1 ≤ factor) :
    coarseWorkMultiplier factor D ≤ (D + 1 : ℕ) * factor ^ D := by
  have hpoint : ∀ r ∈ range (D + 1), factor ^ r ≤ factor ^ D := by
    intro r hr
    exact pow_le_pow_right₀ hfactor (by obtain := mem_range.mp hr; omega)
  have hsum := sum_le_sum hpoint
  simpa only [coarseWorkMultiplier, sum_const, card_range, nsmul_eq_mul] using hsum

theorem uniformMean_mono {ι : Type*} [Fintype ι] (first second : ι → ℝ)
    (hle : ∀ i, first i ≤ second i) : uniformMean first ≤ uniformMean second := by
  exact div_le_div_of_nonneg_right (sum_le_sum (fun i _ => hle i)) (by positivity)

theorem uniformMean_const_mul {ι : Type*} [Fintype ι] (constant : ℝ) (value : ι → ℝ) :
    uniformMean (fun i => constant * value i) = constant * uniformMean value := by
  simp only [uniformMean, ← mul_sum]
  ring

/-- Exact expected inverse allowance under the literal integer threshold
law. This identity is independent of all estimated arrays and accuracy. -/
theorem coarse_inverse_allowance_mean (B : ℕ) [NeZero B] (Q lam allowance : ℚ)
    (hQ : 0 < Q) (hlam : 0 < lam) (ha : 0 < allowance) :
    uniformMean (fun draw : Fin B =>
      1 / ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ)) =
        coarseInverseAllowanceFactor B Q lam / allowance := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlr : (0 : ℝ) < lam := by exact_mod_cast hlam
  have har : (0 : ℝ) < allowance := by exact_mod_cast ha
  have hpoint (draw : Fin B) :
      1 / ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ) =
        ((B : ℝ) * Q / (lam * allowance)) * (1 / (draw.val + 1 : ℕ)) := by
    have hr : (0 : ℝ) < (draw.val + 1 : ℕ) := by positivity
    simp only [coarseChildThreshold, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast]
    field_simp
  simp_rw [hpoint]
  rw [uniformMean_const_mul]
  simp only [uniformMean, Fintype.card_fin]
  rw [coarse_sum_labels B (fun r => (1 : ℝ) / r)]
  unfold coarseInverseAllowanceFactor
  field_simp

theorem coarseBranch_word_length {B D : ℕ} {α : Type u}
    (children : Fin B → CoarseSourceTree B α D) :
    (CoarseSourceTree.branch children).word.length = ∑ i, (children i).word.length := by
  simp only [CoarseSourceTree.word, List.length_flatten, List.map_ofFn,
    Function.comp_def, List.sum_ofFn]

/-- The expected active work has the paper's inverse-allowance bound.
The inequality holds regardless of every coarse accuracy event. -/
theorem coarseExpectedArrayWork_bound {B D : ℕ} [NeZero B] {α : Type u}
    (k : ℕ) (Q lam : ℚ) (tree : CoarseSourceTree B α D) (allowance : ℚ)
    (hQ : 0 < Q) (hlam : 0 < lam) (ha : 0 < allowance) :
    coarseExpectedArrayWork k Q lam tree allowance ≤
      (B * (2 * k + 1) : ℕ) * (tree.word.length : ℝ) / allowance *
        coarseWorkMultiplier (coarseInverseAllowanceFactor B Q lam) D := by
  have hfactor : 0 ≤ coarseInverseAllowanceFactor B Q lam := by
    unfold coarseInverseAllowanceFactor
    apply mul_nonneg
    · exact div_nonneg (by exact_mod_cast hQ.le) (by exact_mod_cast hlam.le)
    · exact sum_nonneg (fun _ _ => by positivity)
  have haReal : (0 : ℝ) < allowance := by exact_mod_cast ha
  induction tree generalizing allowance with
  | leaf letter =>
    simp only [coarseExpectedArrayWork]
    split_ifs with hprune
    · exact mul_nonneg (div_nonneg (by positivity) haReal.le)
        (coarseWorkMultiplier_nonneg _ 0 hfactor)
    · have hwidth : (allowance : ℝ) < (CoarseSourceTree.leaf (B := B) letter).word.length := by
        exact_mod_cast lt_of_not_ge hprune
      simp only [coarseWorkMultiplier, zero_add, sum_range_one, pow_zero, mul_one]
      apply (le_div_iff₀ haReal).2
      nlinarith [show (0 : ℝ) ≤ (B * (2 * k + 1) : ℕ) by positivity]
  | @branch D children ih =>
    simp only [coarseExpectedArrayWork]
    split_ifs with hprune
    · exact mul_nonneg (div_nonneg (by positivity) haReal.le)
        (coarseWorkMultiplier_nonneg _ (D + 1) hfactor)
    · let charge : ℝ := (B * (2 * k + 1) : ℕ)
      let factor := coarseInverseAllowanceFactor B Q lam
      let multiplier := coarseWorkMultiplier factor D
      have hmeanBound (i : Fin B) :
          uniformMean (fun draw : Fin B => coarseExpectedArrayWork k Q lam (children i)
              (lam * coarseChildThreshold B Q allowance draw)) ≤
            charge * (children i).word.length * multiplier * (factor / allowance) := by
        have hpoint (draw : Fin B) :
            coarseExpectedArrayWork k Q lam (children i)
                (lam * coarseChildThreshold B Q allowance draw) ≤
              (charge * (children i).word.length * multiplier) *
                (1 / ((lam * coarseChildThreshold B Q allowance draw : ℚ) : ℝ)) := by
          have hchildAllowance := mul_pos hlam (coarseChildThreshold_pos draw hQ ha)
          have hbound := ih i _ hchildAllowance (by exact_mod_cast hchildAllowance)
          convert hbound using 1
          dsimp [charge, multiplier, factor]
          ring
        have hmean := uniformMean_mono _ _ hpoint
        rw [uniformMean_const_mul, coarse_inverse_allowance_mean B Q lam allowance hQ hlam ha] at hmean
        exact hmean
      have hmeanSum := sum_le_sum (s := univ) (fun i _ => hmeanBound i)
      have hlength : (∑ i, ((children i).word.length : ℝ)) =
          (CoarseSourceTree.branch children).word.length := by
        exact_mod_cast (coarseBranch_word_length children).symm
      have hsum : (∑ i, charge * (children i).word.length * multiplier * (factor / allowance)) =
          charge * (CoarseSourceTree.branch children).word.length / allowance * (factor * multiplier) := by
        calc
          _ = (charge * multiplier * (factor / allowance)) * ∑ i, ((children i).word.length : ℝ) := by
            rw [mul_sum]
            apply sum_congr rfl
            intro i hi
            ring
          _ = _ := by rw [hlength]; ring
      rw [hsum] at hmeanSum
      have hwidth : (allowance : ℝ) < (CoarseSourceTree.branch children).word.length := by
        exact_mod_cast lt_of_not_ge hprune
      have hcharge : charge ≤ charge * (CoarseSourceTree.branch children).word.length / allowance := by
        apply (le_div_iff₀ haReal).2
        dsimp [charge]
        nlinarith [show (0 : ℝ) ≤ (B * (2 * k + 1) : ℕ) by positivity]
      have htotal := add_le_add hcharge hmeanSum
      rw [coarseWorkMultiplier_succ]
      dsimp [charge, multiplier, factor] at htotal ⊢
      nlinarith

theorem coarseActiveChildrenWork_eq_sum {B D : ℕ} {α : Type u}
    (Q lam allowance : ℚ)
    (work : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D)) :
    coarseActiveChildrenWork Q lam allowance work children =
      (children.map (fun data =>
        work data.1 data.2.2 (lam * coarseChildThreshold B Q allowance data.2.1))).sum := by
  induction children with
  | nil => rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    simp only [coarseActiveChildrenWork, List.map_cons, List.sum_cons, ih]

theorem coarseActiveChildrenWork_ofFn {B D : ℕ} {α : Type u}
    (Q lam allowance : ℚ)
    (work : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ)
    (children : Fin B → CoarseSourceTree B α D)
    (draws : Fin B → Fin B) (below : Fin B → CoarseThresholdDraws B D) :
    coarseActiveChildrenWork Q lam allowance work
        (List.ofFn fun i => (children i, draws i, below i)) =
      ∑ i : Fin B, work (children i) (below i) (lam * coarseChildThreshold B Q allowance (draws i)) := by
  rw [coarseActiveChildrenWork_eq_sum]
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn]

/-- The finite expectation recurrence is exactly the expectation of the
actual pruning-stopped execution counter under the concrete recursive law. -/
theorem coarseActiveArrayWork_integral {B D : ℕ} [NeZero B] {α : Type u}
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (k : ℕ) (Q lam : ℚ) (tree : CoarseSourceTree B α D) (allowance : ℚ) :
    (∫ draws, (coarseActiveArrayWork k Q lam tree draws allowance : ℝ)
      ∂coarseDrawMeasure B D) = coarseExpectedArrayWork k Q lam tree allowance := by
  induction tree generalizing allowance with
  | leaf letter =>
    simp only [coarseActiveArrayWork, coarseExpectedArrayWork]
    split_ifs <;> simp
  | @branch D children ih =>
    by_cases hprune : ((CoarseSourceTree.branch children).word.length : ℚ) ≤ allowance
    · have hzero : (fun draws : CoarseThresholdDraws B (D + 1) =>
          (coarseActiveArrayWork k Q lam (.branch children) draws allowance : ℝ)) = fun _ => 0 := by
        funext draws
        obtain ⟨draws, below⟩ := draws
        simp only [coarseActiveArrayWork, hprune, ↓reduceIte, Nat.cast_zero]
      rw [hzero]
      simp only [integral_zero, coarseExpectedArrayWork, hprune, ↓reduceIte]
    · let μ := (PMF.uniformOfFintype (Fin B)).toMeasure
      let ν := coarseDrawMeasure B D
      change (∫ data : (Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D),
        (coarseActiveArrayWork k Q lam (.branch children) data allowance : ℝ)
        ∂((Measure.pi fun _ : Fin B => μ).prod (Measure.pi fun _ : Fin B => ν))) = _
      have hpoint (data : (Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D)) :
          (coarseActiveArrayWork k Q lam (.branch children) data allowance : ℝ) =
            (B * (2 * k + 1) : ℕ) + ∑ i : Fin B,
              (coarseActiveArrayWork k Q lam (children i) (data.2 i)
                (lam * coarseChildThreshold B Q allowance (data.1 i)) : ℝ) := by
        obtain ⟨draws, below⟩ := data
        simp only [coarseActiveArrayWork, hprune, ↓reduceIte,
          coarseActiveChildrenWork_ofFn, Nat.cast_add, Nat.cast_sum]
      simp_rw [hpoint]
      rw [integral_prod _ (.of_finite)]
      have hinner (draws : Fin B → Fin B) :
          (∫ below : Fin B → CoarseThresholdDraws B D,
            ((B * (2 * k + 1) : ℕ) + ∑ i : Fin B,
              (coarseActiveArrayWork k Q lam (children i) (below i)
                (lam * coarseChildThreshold B Q allowance (draws i)) : ℝ))
            ∂Measure.pi (fun _ : Fin B => ν)) =
          (B * (2 * k + 1) : ℕ) + ∑ i : Fin B,
            coarseExpectedArrayWork k Q lam (children i)
              (lam * coarseChildThreshold B Q allowance (draws i)) := by
        rw [integral_add (integrable_const _) (.of_finite), integral_const, probReal_univ, one_smul,
          integral_finsetSum]
        · congr 1
          apply sum_congr rfl
          intro i hi
          rw [integral_comp_eval (μ := fun _ : Fin B => ν) (i := i)
            (f := fun below => (coarseActiveArrayWork k Q lam (children i) below
              (lam * coarseChildThreshold B Q allowance (draws i)) : ℝ))
            (measurable_of_finite _).aestronglyMeasurable]
          exact ih i _
        · intro i hi
          exact .of_finite
      simp_rw [hinner]
      rw [integral_add (integrable_const _) (.of_finite), integral_const, probReal_univ, one_smul,
        integral_finsetSum]
      · simp only [coarseExpectedArrayWork, hprune, ↓reduceIte]
        congr 1
        apply sum_congr rfl
        intro i hi
        rw [integral_comp_eval (μ := fun _ : Fin B => μ) (i := i)
          (f := fun draw => coarseExpectedArrayWork k Q lam (children i)
            (lam * coarseChildThreshold B Q allowance draw))
          (measurable_of_finite _).aestronglyMeasurable, uniform_integral]
      · intro i hi
        exact .of_finite

/-- Expected active work, stated directly for the actual execution law,
without any conditioning on accuracy. -/
theorem coarseActiveArrayWork_expected_bound {B D : ℕ} [NeZero B] {α : Type u}
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (k : ℕ) (Q lam : ℚ) (tree : CoarseSourceTree B α D) (allowance : ℚ)
    (hQ : 0 < Q) (hlam : 0 < lam) (ha : 0 < allowance) :
    (∫ draws, (coarseActiveArrayWork k Q lam tree draws allowance : ℝ)
      ∂coarseDrawMeasure B D) ≤
        (B * (2 * k + 1) : ℕ) * (tree.word.length : ℝ) / allowance *
          coarseWorkMultiplier (coarseInverseAllowanceFactor B Q lam) D := by
  rw [coarseActiveArrayWork_integral]
  exact coarseExpectedArrayWork_bound k Q lam tree allowance hQ hlam ha

end EditApproximation

end OAI
