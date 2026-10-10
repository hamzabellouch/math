import OAI.NumberTheory.Ostmann.Arithmetic.GuardedHistoryCancellation
import OAI.NumberTheory.Ostmann.Construction.ConstructedHistoryGuards

namespace OAI

/-! # The literal product of both reconstructed history supports -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem guardedHistoryAmplitude_pair {σ : Type*} {r s n m t u : ℕ}
    (N : Fin r → MvPolynomial σ ℤ) (d : Fin r → ℤ) (v : Fin r → ℕ)
    (N' : Fin s → MvPolynomial σ ℤ) (d' : Fin s → ℤ) (v' : Fin s → ℕ)
    (a : σ → ℤ) (coord : σ)
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (J : Fin u → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (keep' : (Fin u → Bool) → Bool) (x : ℤ) :
    guardedHistoryAmplitude (Fin.append N N') (Fin.append d d') (Fin.append v v')
      a coord (pairedPolynomialFactors F G) (Fin.append H J) (pairedPolynomialKeep keep keep') x =
    guardedHistoryAmplitude N d v a coord F H keep x *
      conj (guardedHistoryAmplitude N' d' v' a coord G J keep' x) := by
  unfold guardedHistoryAmplitude
  rw [pairedPolynomialAmplitude]
  simp only [Fin.forall_fin_add, Fin.append_left, Fin.append_right, map_mul]
  split_ifs <;> simp_all

theorem reconstructedHistoryAmplitude_pair {σ : Type*} {n m t u : ℕ}
    (steps steps' : List (HistoryPivotStep σ))
    (v : Fin steps.length → ℕ) (v' : Fin steps'.length → ℕ)
    (a : σ → ℤ) (coord : σ)
    (F : Fin n → ClippedPolynomialFactor) (G : Fin m → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (J : Fin u → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (keep' : (Fin u → Bool) → Bool) (x : ℤ) :
    reconstructedHistoryAmplitude steps v a coord F H keep x *
      conj (reconstructedHistoryAmplitude steps' v' a coord G J keep' x) =
    guardedHistoryAmplitude
      (Fin.append (fun i => (reconstructionFormulaAt steps .prime i).cleared.numerator)
        (fun i => (reconstructionFormulaAt steps' .prime i).cleared.numerator))
      (Fin.append (fun i => (reconstructionFormulaAt steps .prime i).cleared.denominator)
        (fun i => (reconstructionFormulaAt steps' .prime i).cleared.denominator))
      (Fin.append v v') a coord (pairedPolynomialFactors F G) (Fin.append H J)
      (pairedPolynomialKeep keep keep') x := by
  rw [reconstructedHistoryAmplitude_exact, reconstructedHistoryAmplitude_exact]
  exact (guardedHistoryAmplitude_pair _ _ _ _ _ _ a coord F G H J keep keep' x).symm

end Ostmann

end OAI
