import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitial
import OAI.Combinatorics.EditApproximation.Coarse.CoarseWork
import Mathlib.NumberTheory.Harmonic.Bounds
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Expected array work of the actual dyadic initial estimator

These are expectations of the concrete pruning-stopped counters. The
linear penalty sweeps and representation bounds separately convert the
array units into arithmetic and RAM work.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

universe u

theorem coarseInverseAllowanceFactor_nonneg (B : ℕ) (Q lam : ℚ)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) : 0 ≤ coarseInverseAllowanceFactor B Q lam := by
  unfold coarseInverseAllowanceFactor
  exact mul_nonneg (div_nonneg (by exact_mod_cast hQ) (by exact_mod_cast hlam))
    (sum_nonneg (fun _ _ => by positivity))

theorem coarseInverseAllowanceFactor_log_bound (B : ℕ) (Q lam : ℚ)
    (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) :
    coarseInverseAllowanceFactor B Q lam ≤ (Q : ℝ) / lam * (1 + Real.log B) := by
  have hharmonic : (∑ r ∈ Icc 1 B, (1 : ℝ) / r) = harmonic B := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  unfold coarseInverseAllowanceFactor
  rw [hharmonic]
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log B)
    (div_nonneg (by exact_mod_cast hQ) (by exact_mod_cast hlam))

theorem coarseWorkMultiplier_mono (first second : ℝ) (D : ℕ)
    (hfirst : 0 ≤ first) (hle : first ≤ second) :
    coarseWorkMultiplier first D ≤ coarseWorkMultiplier second D := by
  exact sum_le_sum (fun _ _ => pow_le_pow_left₀ hfirst hle _)

/-- Root allowance equals the actual guessed distance. It cancels the
array width `2k+1` in expectation, uniformly over every positive guess. -/
theorem coarseRootArrayWork_expected_bound {B D : ℕ} [NeZero B] {α : Type u}
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (k : ℕ) (Q lam : ℚ) (tree : CoarseSourceTree B α D)
    (hk : 0 < k) (hQ : 0 < Q) (hlam : 0 < lam)
    (factor : ℝ) (hfactor : 1 ≤ factor)
    (hinverse : coarseInverseAllowanceFactor B Q lam ≤ factor) :
    (∫ draws, (coarseActiveArrayWork k Q lam tree draws k : ℝ)
      ∂coarseDrawMeasure B D) ≤
      3 * B * tree.word.length * (D + 1 : ℕ) * factor ^ D := by
  have hcounter := coarseActiveArrayWork_expected_bound k Q lam tree k hQ hlam (by exact_mod_cast hk)
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcoefficient : (B * (2 * k + 1) : ℕ) * (tree.word.length : ℝ) / k ≤
      3 * B * tree.word.length := by
    apply (div_le_iff₀ hkReal).2
    push_cast
    have hnonnegative : (0 : ℝ) ≤ (B : ℝ) * tree.word.length := by positivity
    nlinarith
  have hmultiplier := (coarseWorkMultiplier_mono _ factor D
    (coarseInverseAllowanceFactor_nonneg B Q lam hQ.le hlam.le) hinverse).trans
      (coarseWorkMultiplier_le factor D hfactor)
  apply hcounter.trans
  exact (mul_le_mul_of_nonneg_right hcoefficient
    (coarseWorkMultiplier_nonneg _ D (coarseInverseAllowanceFactor_nonneg B Q lam hQ.le hlam.le))).trans
    (by
      have hmul := mul_le_mul_of_nonneg_left hmultiplier
        (show (0 : ℝ) ≤ 3 * B * tree.word.length by positivity)
      simpa only [mul_assoc] using hmul)

/- The initial estimator's actual sum of active array units, with zero
array work in its two direct branches. -/


/-- The actual complete initial computation has the paper's expected
array-work shape, on every execution and without conditioning on accuracy. -/
theorem coarseInitialArrayWork_expected_bound {B D : ℕ} [NeZero B] {α : Type u} [DecidableEq α]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (Q lam : ℚ) (x y : List α) (hcapacity : coarseEntryWidth x y ≤ B ^ D)
    (hQ : 0 < Q) (hlam : 0 < lam)
    (factor : ℝ) (hfactor : 1 ≤ factor)
    (hinverse : coarseInverseAllowanceFactor B Q lam ≤ factor) :
    (∫ draws, (coarseInitialArrayWork B D Q lam x y draws : ℝ)
      ∂coarseInitialMeasure B D (coarseEntryWidth x y)) ≤
      3 * B * coarseEntryWidth x y * (Nat.clog 2 (coarseEntryWidth x y) + 1 : ℕ) *
        (D + 1 : ℕ) * factor ^ D := by
  classical
  have hnonnegative : (0 : ℝ) ≤
      3 * B * coarseEntryWidth x y * (Nat.clog 2 (coarseEntryWidth x y) + 1 : ℕ) *
        (D + 1 : ℕ) * factor ^ D := by positivity
  by_cases hlong : 2 * x.length < y.length
  · simpa only [coarseInitialArrayWork, hlong, ↓reduceIte, Nat.cast_zero, integral_zero] using hnonnegative
  by_cases hxy : x = y
  · have hzero (draws) : coarseInitialArrayWork B D Q lam x y draws = 0 := by
      unfold coarseInitialArrayWork
      rw [ite_eq_right hlong, ite_eq_left hxy]
    simp_rw [hzero, Nat.cast_zero, integral_zero]
    exact hnonnegative
  simp only [coarseInitialArrayWork, hlong, hxy, ↓reduceIte, Nat.cast_sum]
  rw [integral_finsetSum univ (by intro i hi; exact .of_finite)]
  have hpoint (i : CoarseGuessIndex (coarseEntryWidth x y)) :
      (∫ draws, (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i) Q lam
        (coarseEntryTree B D x y) (draws i) (coarseGuess (coarseEntryWidth x y) i) : ℝ)
        ∂coarseInitialMeasure B D (coarseEntryWidth x y)) ≤
      3 * B * coarseEntryWidth x y * (D + 1 : ℕ) * factor ^ D := by
    unfold coarseInitialMeasure
    rw [integral_comp_eval (μ := fun _ : CoarseGuessIndex (coarseEntryWidth x y) => coarseDrawMeasure B D)
      (i := i) (f := fun draws => (coarseActiveArrayWork (coarseGuess (coarseEntryWidth x y) i) Q lam
        (coarseEntryTree B D x y) draws (coarseGuess (coarseEntryWidth x y) i) : ℝ))
      (measurable_of_finite _).aestronglyMeasurable]
    have hbound := coarseRootArrayWork_expected_bound (coarseGuess (coarseEntryWidth x y) i)
      Q lam (coarseEntryTree B D x y) (by dsimp [coarseGuess]; positivity) hQ hlam factor hfactor hinverse
    rw [coarseEntryTree_word B D x y hcapacity,
      coarsePadTo_length _ _ (le_max_left _ _)] at hbound
    exact hbound
  have hsum := sum_le_sum (s := univ) (fun i _ => hpoint i)
  apply hsum.trans_eq
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end EditApproximation

end OAI
