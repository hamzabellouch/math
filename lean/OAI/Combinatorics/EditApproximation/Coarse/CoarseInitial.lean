import OAI.Combinatorics.EditApproximation.Coarse.CoarsePadding
import OAI.Combinatorics.EditApproximation.Coarse.CoarseProbability
import OAI.Combinatorics.EditApproximation.Probability.ExactSampling
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# The executable initial integer estimate

The direct branches handle long targets and equality. The remaining branch
evaluates the concrete coarse recurrence at every dyadic guess, takes the
rational minimum, rounds up and clamps to the input length.
-/

namespace EditApproximation

open EditDistortion Finset MeasureTheory ProbabilityTheory

universe u

/-- A finite Bernoulli-inequality bound for the exact structural factor.
The paper's `lam = 1/(64H)` and `D ≤ H` satisfy these loose conditions. -/
theorem coarseStructuralFactor_le_two (lam : ℚ) (D : ℕ)
    (hlam : 0 ≤ lam) (hsmall : lam ≤ 1 / 4)
    (hdepth : 4 * (D : ℚ) * lam ≤ 1) : coarseStructuralFactor lam D ≤ 2 := by
  have hl : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hs : (lam : ℝ) ≤ 1 / 4 := by
    have hcast : (lam : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hsmall
    norm_num at hcast
    exact hcast
  have hd : 4 * (D : ℝ) * lam ≤ 1 := by exact_mod_cast hdepth
  have hden : 0 < 1 - (lam : ℝ) := by linarith
  have hdenTwo : 0 < 1 - 2 * (lam : ℝ) := by linarith
  have hbase : (1 + (lam : ℝ)) / (1 - (lam : ℝ)) ≤ 1 / (1 - 2 * (lam : ℝ)) := by
    apply (div_le_div_iff₀ hden hdenTwo).2
    nlinarith
  have hpower := pow_le_pow_left₀ (div_nonneg (by linarith) hden.le) hbase D
  rw [one_div_pow] at hpower
  have hbernoulli := one_add_mul_le_pow (a := -(2 * (lam : ℝ))) (by linarith) D
  have hlower : (1 : ℝ) / 2 ≤ (1 - 2 * (lam : ℝ)) ^ D := by
    simp only [mul_neg, ← sub_eq_add_neg] at hbernoulli
    nlinarith
  have hreciprocal : 1 / (1 - 2 * (lam : ℝ)) ^ D ≤ 2 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hlower)).2
    linarith
  exact hpower.trans hreciprocal















noncomputable def CoarseInitialAccuracyEvent {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (x y : List α)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B D) : Prop :=
  ∀ i, let k := coarseGuess (coarseEntryWidth x y) i
    CoarseAccuracyEvent k Q lam
      (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
      (coarseEntryTree B D x y) (draws i) k 0

theorem coarseEntryTree_word {α : Type u} (B D : ℕ) (x y : List α)
    (hcapacity : coarseEntryWidth x y ≤ B ^ D) :
    (coarseEntryTree B D x y).word = coarsePadTo (coarseEntryWidth x y) x := by
  apply coarseSourceTreeOfList_word_eq
  rw [coarsePadTo_length _ _ (le_max_left _ _)]
  exact hcapacity

theorem coarse_good_dyadic_guess (n d : ℕ) (hd : 0 < d) (hdn : d ≤ n) :
    ∃ i : CoarseGuessIndex n, d ≤ coarseGuess n i ∧ coarseGuess n i < 2 * d := by
  refine ⟨⟨Nat.clog 2 d, Nat.lt_succ_of_le (Nat.clog_mono_right 2 hdn)⟩, ?_⟩
  exact rejectionWord_range d hd

theorem coarseInitialValue_le_length {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (N : ℕ) (x y : List α)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B D) :
    coarseInitialValue B D Q lam N x y draws ≤ N := by
  unfold coarseInitialValue
  split_ifs
  · exact min_le_left _ _
  · exact Nat.zero_le _
  · exact min_le_left _ _

/-- Every original zero-cost instance returns zero on every execution. -/
theorem coarseInitialValue_zero {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (N : ℕ) (x y : List α)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B D)
    (hzero : edit x y = 0) : coarseInitialValue B D Q lam N x y draws = 0 := by
  have hxy : x = y := (cost_eq_zero_iff (s := true)).mp hzero
  subst y
  simp only [coarseInitialValue, ite_eq_right (by omega : ¬ 2 * x.length < x.length), ite_true]

/-- Every dyadic candidate lies above the original edit cost on its
literal pathwise event, even when the guess is below the true distance. -/
theorem coarseInitialCandidate_lower {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (x y : List α)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B D)
    (hcapacity : coarseEntryWidth x y ≤ B ^ D)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (hfactor : coarseStructuralFactor lam D ≤ 2)
    (hevent : let k := coarseGuess (coarseEntryWidth x y) i
      CoarseAccuracyEvent k Q lam
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B D x y) draws k 0) :
    (edit x y : ℚ) ≤ coarseInitialCandidate B D Q lam x y i draws := by
  let k := coarseGuess (coarseEntryWidth x y) i
  let tree := coarseEntryTree B D x y
  let target := coarsePadTo (coarseEntryWidth x y) y
  have hword := coarseEntryTree_word B D x y hcapacity
  have hlength : tree.word.length = target.length := by
    dsimp [tree, target]
    rw [hword, coarsePadTo_length _ _ (le_max_left _ _),
      coarsePadTo_length _ _ (le_max_right _ _)]
  have htrue := coarseTreeValue_edit_lower tree target k hlength
  have hpadding := (coarsePadding_distance_bounds x y).1
  rw [← hword] at hpadding
  have hcost : edit x y ≤ coarseTreeValue tree target k := hpadding.trans htrue
  have hcostReal : (edit x y : ℝ) ≤ coarseTreeValue tree target k := by exact_mod_cast hcost
  have haccuracy := (coarseThresholdEstimate_accurate k Q lam (coarseTargetFrame k target)
    tree draws k 0 hQ hlam hlamone (by positivity) hevent (coarseRootShift k)).1
  have hfpos : 0 < coarseStructuralFactor lam D :=
    lt_of_lt_of_le zero_lt_one (coarseStructuralFactor_one_le lam D hlam hlamone)
  have hdivide : (coarseTreeValue tree target k : ℝ) / 2 ≤
      coarseTreeValue tree target k / coarseStructuralFactor lam D :=
    div_le_div_of_nonneg_left (by positivity) hfpos hfactor
  have hcandidateReal : (edit x y : ℝ) ≤ (coarseInitialCandidate B D Q lam x y i draws : ℝ) := by
    simp only [coarseInitialCandidate, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast]
    change (edit x y : ℝ) ≤ 2 *
      ((coarseThresholdEstimate k Q lam (coarseTargetFrame k target) tree draws k 0
        (coarseRootShift k) : ℝ) + k)
    change (coarseTreeValue tree target k : ℝ) / coarseStructuralFactor lam D - k ≤ _ at haccuracy
    linarith
  exact_mod_cast hcandidateReal

/-- A dyadic guess in `[d,2d)` has the manuscript's coarse polynomial
distortion after actual threshold reconstruction and fresh padding. -/
theorem coarseInitialCandidate_upper {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (x y : List α)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B D)
    (hcapacity : coarseEntryWidth x y ≤ B ^ D)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (hfactor : coarseStructuralFactor lam D ≤ 2)
    (hevent : let k := coarseGuess (coarseEntryWidth x y) i
      CoarseAccuracyEvent k Q lam
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B D x y) draws k 0)
    (hguess : edit (coarsePadTo (coarseEntryWidth x y) x)
        (coarsePadTo (coarseEntryWidth x y) y) ≤ coarseGuess (coarseEntryWidth x y) i)
    (hguessUpper : coarseGuess (coarseEntryWidth x y) i <
      2 * edit (coarsePadTo (coarseEntryWidth x y) x) (coarsePadTo (coarseEntryWidth x y) y)) :
    coarseInitialCandidate B D Q lam x y i draws ≤ ((25 + 16 * B * D) * edit x y : ℕ) := by
  let k := coarseGuess (coarseEntryWidth x y) i
  let tree := coarseEntryTree B D x y
  let target := coarsePadTo (coarseEntryWidth x y) y
  have hword := coarseEntryTree_word B D x y hcapacity
  have htrue := coarseTreeValue_edit_upper tree target k (by simpa only [tree, target, k, hword] using hguess)
  have hpadding := (coarsePadding_distance_bounds x y).2
  rw [← hword] at hpadding hguessUpper
  have htrueReal : (coarseTreeValue tree target k : ℝ) ≤
      (1 + 2 * (B : ℝ) * D) * edit tree.word target := by exact_mod_cast htrue
  have hpaddingReal : (edit tree.word target : ℝ) ≤ 2 * edit x y := by exact_mod_cast hpadding
  have hguessReal : (k : ℝ) < 2 * edit tree.word target := by exact_mod_cast hguessUpper
  have haccuracy := (coarseThresholdEstimate_accurate k Q lam (coarseTargetFrame k target)
    tree draws k 0 hQ hlam hlamone (by positivity) hevent (coarseRootShift k)).2
  change _ ≤ coarseStructuralFactor lam D * (coarseTreeValue tree target k : ℝ) + k at haccuracy
  have hfactorBound : coarseStructuralFactor lam D * (coarseTreeValue tree target k : ℝ) ≤
      2 * coarseTreeValue tree target k := mul_le_mul_of_nonneg_right hfactor (by positivity)
  have hdistortion := mul_le_mul_of_nonneg_left hpaddingReal
    (show (0 : ℝ) ≤ 12 + 8 * (B : ℝ) * D by positivity)
  have hcandidateReal : (coarseInitialCandidate B D Q lam x y i draws : ℝ) ≤
      ((25 + 16 * B * D) * edit x y : ℕ) := by
    simp only [coarseInitialCandidate, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast]
    change 2 * ((coarseThresholdEstimate k Q lam (coarseTargetFrame k target)
      tree draws k 0 (coarseRootShift k) : ℝ) + k) ≤ _
    push_cast
    nlinarith [show (0 : ℝ) ≤ edit x y by positivity]
  exact_mod_cast hcandidateReal

/-- On the proved finite-tree events, the executable initial table entry
is an integer between the actual edit cost and its stated coarse factor. -/
theorem coarseInitialValue_bounds {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (N : ℕ) (x y : List α)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B D)
    (hcapacity : coarseEntryWidth x y ≤ B ^ D) (hN : coarseEntryWidth x y ≤ N)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) (hlamone : lam < 1)
    (hfactor : coarseStructuralFactor lam D ≤ 2)
    (hevent : CoarseInitialAccuracyEvent B D Q lam x y draws) :
    edit x y ≤ coarseInitialValue B D Q lam N x y draws ∧
      coarseInitialValue B D Q lam N x y draws ≤ (25 + 16 * B * D) * edit x y := by
  have hcN : edit x y ≤ N := (edit_le_max_length x y).trans hN
  by_cases hlong : 2 * x.length < y.length
  · have hlength := (cost_length_bounds (s := true) x y).2
    change y.length ≤ x.length + edit x y at hlength
    have hcost : edit x y ≤ y.length :=
      (edit_le_max_length x y).trans_eq (max_eq_right (by omega))
    simp only [coarseInitialValue, hlong, ↓reduceIte]
    have hlongUpper : y.length ≤ 2 * edit x y := by omega
    have hfactorNat : 2 ≤ 25 + 16 * B * D := by omega
    exact ⟨le_min hcN hcost, (min_le_right _ _).trans
      (hlongUpper.trans (Nat.mul_le_mul_right _ hfactorNat))⟩
  · by_cases hxy : x = y
    · subst y
      have hrefl : edit x x = 0 := cost_refl x
      simp only [coarseInitialValue, hlong, ↓reduceIte, hrefl, mul_zero, le_refl, and_self]
    · let d := edit (coarsePadTo (coarseEntryWidth x y) x) (coarsePadTo (coarseEntryWidth x y) y)
      have hc : 0 < edit x y := Nat.pos_of_ne_zero
        (fun hz => hxy ((cost_eq_zero_iff (s := true)).mp hz))
      have hpadding := (coarsePadding_distance_bounds x y).1
      have hd : 0 < d := lt_of_lt_of_le hc hpadding
      have hdn : d ≤ coarseEntryWidth x y := by
        have h := edit_le_max_length (coarsePadTo (coarseEntryWidth x y) x)
          (coarsePadTo (coarseEntryWidth x y) y)
        rw [coarsePadTo_length _ _ (le_max_left _ _),
          coarsePadTo_length _ _ (le_max_right _ _), max_self] at h
        exact h
      obtain ⟨i, hi, hiUpper⟩ := coarse_good_dyadic_guess (coarseEntryWidth x y) d hd hdn
      have hminimumLower : (edit x y : ℚ) ≤ coarseInitialMinimum B D Q lam x y draws := by
        unfold coarseInitialMinimum
        apply le_inf'
        intro j hj
        exact coarseInitialCandidate_lower B D Q lam x y j (draws j) hcapacity
          hQ hlam hlamone hfactor (hevent j)
      have hminimumUpper : coarseInitialMinimum B D Q lam x y draws ≤
          ((25 + 16 * B * D) * edit x y : ℕ) := by
        unfold coarseInitialMinimum
        exact (inf'_le (fun j => coarseInitialCandidate B D Q lam x y j (draws j)) (mem_univ i)).trans
          (coarseInitialCandidate_upper B D Q lam x y i (draws i) hcapacity
            hQ hlam hlamone hfactor (hevent i) hi hiUpper)
      have hceilLower : edit x y ≤ ⌈coarseInitialMinimum B D Q lam x y draws⌉₊ := by
        exact_mod_cast hminimumLower.trans (Nat.le_ceil _)
      have hceilUpper : ⌈coarseInitialMinimum B D Q lam x y draws⌉₊ ≤
          (25 + 16 * B * D) * edit x y := Nat.ceil_le.mpr hminimumUpper
      simp only [coarseInitialValue, hlong, hxy, ↓reduceIte]
      exact ⟨le_min hcN hceilLower, (min_le_right _ _).trans hceilUpper⟩

/-- Independent finite coarse streams for the listed dyadic guesses. -/


instance coarseInitialMeasure_isProbabilityMeasure (B D n : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] :
    IsProbabilityMeasure (coarseInitialMeasure B D n) := by
  unfold coarseInitialMeasure
  infer_instance

/-- The dyadic seed event has an explicit finite failure bound under
the scalar Bernstein hypothesis. -/
theorem coarseInitialAccuracyEvent_failure {B D : ℕ} [NeZero B] {α : Type u} [DecidableEq α]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (Q lam : ℚ) (x y : List α)
    (hQ : 2 ≤ Q) (hlam : 0 < lam) (hlamone : lam < 1)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (coarseInitialMeasure B D (coarseEntryWidth x y)).real
      {draws | ¬ CoarseInitialAccuracyEvent B D Q lam x y draws} ≤
      (Nat.clog 2 (coarseEntryWidth x y) + 1 : ℕ) * (coarseInternalNodes B D : ℝ) *
        (4 * (2 * 2 ^ Nat.clog 2 (coarseEntryWidth x y) + 1 : ℕ) *
          Real.exp (-(lam : ℝ) * Q / 12)) := by
  classical
  let n := coarseEntryWidth x y
  let μ := coarseInitialMeasure B D n
  let bad (i : CoarseGuessIndex n) : Set (CoarseThresholdDraws B D) :=
    {draws | ¬ CoarseAccuracyEvent (coarseGuess n i) Q lam
      (coarseTargetFrame (coarseGuess n i) (coarsePadTo n y))
      (coarseEntryTree B D x y) draws (coarseGuess n i) 0}
  have hsubset : {draws | ¬ CoarseInitialAccuracyEvent B D Q lam x y draws} ⊆
      ⋃ i, {draws | draws i ∈ bad i} := by
    intro draws hdraws
    obtain ⟨i, hi⟩ := not_forall.mp hdraws
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hprojection (i : CoarseGuessIndex n) :
      μ.real {draws | draws i ∈ bad i} = (coarseDrawMeasure B D).real (bad i) := by
    have hmap := (measurePreserving_eval (μ := fun _ : CoarseGuessIndex n => coarseDrawMeasure B D) i).map_eq
    have hpreimage := Measure.map_apply (μ := Measure.pi fun _ : CoarseGuessIndex n => coarseDrawMeasure B D)
      (measurable_pi_apply i) (Set.toFinite (bad i)).measurableSet
    rw [hmap] at hpreimage
    exact congrArg ENNReal.toReal hpreimage.symm
  have hpoint (i : CoarseGuessIndex n) : μ.real {draws | draws i ∈ bad i} ≤
      (coarseInternalNodes B D : ℝ) *
        (4 * (2 * 2 ^ Nat.clog 2 n + 1 : ℕ) * Real.exp (-(lam : ℝ) * Q / 12)) := by
    rw [hprojection]
    have hfailure := coarseAccuracyEvent_failure (coarseGuess n i) Q lam
      (coarseTargetFrame (coarseGuess n i) (coarsePadTo n y))
      (coarseEntryTree B D x y) (coarseGuess n i) 0 hQ hlam hlamone (by dsimp [coarseGuess]; positivity)
      bernstein
    have hk : coarseGuess n i ≤ 2 ^ Nat.clog 2 n :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by exact Nat.le_of_lt_succ i.isLt)
    apply hfailure.trans
    gcongr
  calc
    _ ≤ μ.real (⋃ i, {draws | draws i ∈ bad i}) := measureReal_mono hsubset
    _ ≤ ∑ i, μ.real {draws | draws i ∈ bad i} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : CoarseGuessIndex n, (coarseInternalNodes B D : ℝ) *
        (4 * (2 * 2 ^ Nat.clog 2 n + 1 : ℕ) * Real.exp (-(lam : ℝ) * Q / 12)) :=
      sum_le_sum (fun i _ => hpoint i)
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, CoarseGuessIndex, Fintype.card_fin]
      dsimp [n]
      ring

end EditApproximation

end OAI
