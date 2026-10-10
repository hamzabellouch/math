import OAI.NumberTheory.DukePrimeDegree.Entropy.EntropyInverse
import OAI.NumberTheory.DukePrimeDegree.Entropy.EntropyBalance
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootWeights

namespace OAI

/-!
# Entropy symmetry for the actual diagonal action

The time-reversal theorem applies to right translations by diagonal
matrices. The final lemma combines it with the precise positive-root
entropy formula of EKL (2006), Proposition 3.1(3). That formula remains
an explicit hypothesis here; time reversal and the coefficient balance
are proved.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Time reversal for the diagonal action on the arithmetic quotient. -/
theorem diagonal_entropy_neg (d : ℕ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0)
    (μ : Measure (X (d + 1)))
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (t : ℝ) :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-t))) =
      measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell t)) := by
  apply measureEntropy_inverse
  · refine ⟨(continuous_rightAction _).measurable, ?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  · exact (continuous_rightAction _).measurable
  · intro x
    change rightAction (rightAction x (diagonalOneParameter ell hell t))
      (diagonalOneParameter ell hell (-t)) = x
    rw [rightAction_mul, diagonalOneParameter_neg]
    simp

lemma diagonalOneParameter_neg_weights {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ) :
    diagonalOneParameter (fun i => -ell i)
      (by simp only [Finset.sum_neg_distrib, hell, neg_zero]) t =
      diagonalOneParameter ell hell (-t) := by
  apply Subtype.ext
  change Matrix.diagonal (fun i => Real.exp (-ell i * t)) =
    Matrix.diagonal (fun i => Real.exp (ell i * -t))
  congr 1
  funext i
  congr 1
  ring

lemma rootEntropyForm_nonneg {ι : Type*} [Fintype ι]
    (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j) (ell : ι → ℝ) :
    0 ≤ rootEntropyForm w ell := by
  apply Finset.sum_nonneg
  intro i _
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hw i j) (le_max_right _ _)

/-- The exact entropy-formula input suffices to balance the coefficients;
no separate balance or time-reversal assumption is needed. -/
theorem balanced_of_diagonal_entropy_formula
    (d : ℕ) (μ : Measure (X (d + 1)))
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (w : Fin (d + 1) → Fin (d + 1) → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hformula : ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0),
      measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell 1)) =
        ENNReal.ofReal (rootEntropyForm w ell)) :
    ∀ i, ∑ j, w i j = ∑ j, w j i := by
  apply balanced_of_rootEntropyForm_symmetry w
  intro ell hell
  have hn : ∑ i, -ell i = 0 := by simp only [Finset.sum_neg_distrib, hell, neg_zero]
  have he : ENNReal.ofReal (rootEntropyForm w (fun i => -ell i)) =
      ENNReal.ofReal (rootEntropyForm w ell) := by
    rw [← hformula (fun i => -ell i) hn, ← hformula ell hell,
      diagonalOneParameter_neg_weights]
    exact diagonal_entropy_neg d ell hell μ hA 1
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (rootEntropyForm_nonneg w hw _)] using ht.symm

end DukePrimeDegree

end

end OAI
