import OAI.NumberTheory.Ostmann.Arithmetic.GuardedHistoryCancellation
import OAI.NumberTheory.Ostmann.Arithmetic.ClearedPolynomialRanges

namespace OAI

/-! # Fourier ranges and all additional history inequalities in one exact guard -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def fullHistoryPolynomials {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) : Fin ((n + n) + t) → Polynomial ℝ :=
  Fin.append (polynomialRangeBounds F) H

noncomputable def fullHistoryKeep {n t : ℕ} (keep : (Fin t → Bool) → Bool) :
    (Fin ((n + n) + t) → Bool) → Bool :=
  pairedPolynomialKeep (polynomialRangeKeep n) keep

theorem fullHistoryAmplitude_factor {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (x : ℝ) :
    polynomialAmplitude F (fullHistoryPolynomials F H) (fullHistoryKeep keep) x =
      (if keep (polynomialSupportCode H x) = true then (1 : ℂ) else 0) *
        polynomialAmplitude F (polynomialRangeBounds F) (polynomialRangeKeep n) x := by
  have hl : (fun i : Fin (n + n) => polynomialSupportCode (fullHistoryPolynomials F H) x
      (Fin.castAdd t i)) = polynomialSupportCode (polynomialRangeBounds F) x := by
    funext i
    simp only [fullHistoryPolynomials, polynomialSupportCode, Fin.append_left]
  have hr : (fun i : Fin t => polynomialSupportCode (fullHistoryPolynomials F H) x
      (Fin.natAdd (n + n) i)) = polynomialSupportCode H x := by
    funext i
    simp only [fullHistoryPolynomials, polynomialSupportCode, Fin.append_right]
  simp only [polynomialAmplitude, fullHistoryKeep, pairedPolynomialKeep, hl, hr, Bool.and_eq_true]
  split_ifs <;> simp_all

/-- The extension agrees with every original range/bin restriction, including
boundary points, before the one-sided cancellation estimate is invoked. -/
theorem fullHistoryAmplitude_exact {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (x : ℝ) :
    polynomialAmplitude F (fullHistoryPolynomials F H) (fullHistoryKeep keep) x =
      (if keep (polynomialSupportCode H x) = true ∧
        ∀ i, (F i).polynomial.eval x ∈ Set.Icc (F i).lo (F i).hi then (1 : ℂ) else 0) *
        ∏ i, (F i).profile ((F i).polynomial.eval x) := by
  rw [fullHistoryAmplitude_factor, polynomialAmplitude_range]
  split_ifs <;> simp_all

theorem fullHistoryPolynomials_complexity {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) :
    polynomialWeightComplexity F (fullHistoryPolynomials F H) ≤
      3 * (∑ i, (F i).polynomial.natDegree) + ∑ j, (H j).natDegree := by
  have hbase := polynomialRange_complexity F
  simp only [polynomialWeightComplexity, fullHistoryPolynomials, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right] at *
  omega

theorem guardedHistoryAmplitude_norm {σ I : Type*} [Fintype I] {n t : ℕ}
    (N : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ) (a : σ → ℤ) (i : σ)
    (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (x : ℤ) :
    ‖guardedHistoryAmplitude N d s a i F H keep x‖ ≤ smoothPolynomialBudget F := by
  unfold guardedHistoryAmplitude
  split_ifs
  · simpa only [one_mul] using polynomialAmplitude_norm F H keep (x : ℝ)
  · simpa only [zero_mul, norm_zero] using smoothPolynomialBudget_nonneg F

end Ostmann

end OAI
