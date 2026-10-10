import OAI.NumberTheory.DukePrimeDegree.Entropy.RootInformationBound
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootInvariantLeaves

namespace OAI

/-! # Mean root coefficients and their elementary properties

The coefficient is the mean leaf information at unit scale. Diagonal
covariance makes real-time mean information linear in time.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The actual mean information at unit scale, with zero diagonal. -/
def canonicalRootCoefficient (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (i j : Fin (d + 1)) : ℝ :=
  if hij : i = j then 0 else (rootInformationMean hij μ 1).toReal

variable (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

lemma canonicalRootCoefficient_diagonal (i : Fin (d + 1)) :
    canonicalRootCoefficient d μ i i = 0 := by simp [canonicalRootCoefficient]

lemma canonicalRootCoefficient_nonneg (i j : Fin (d + 1)) :
    0 ≤ canonicalRootCoefficient d μ i j := by
  unfold canonicalRootCoefficient
  split_ifs
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

include hA

lemma canonicalRootCoefficient_le_one (i j : Fin (d + 1)) :
    canonicalRootCoefficient d μ i j ≤ 1 := by
  unfold canonicalRootCoefficient
  split_ifs with hij
  · exact zero_le_one
  · exact (ENNReal.toReal_mono ENNReal.one_ne_top
      (rootInformationMean_le_one d hij μ hA)).trans_eq ENNReal.toReal_one

lemma canonicalRootCoefficient_zero_iff (i j : Fin (d + 1)) (hij : i ≠ j) :
    canonicalRootCoefficient d μ i j = 0 ↔
      ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  rw [canonicalRootCoefficient, dite_eq_right hij, ENNReal.toReal_eq_zero_iff]
  have hfin : rootInformationMean hij μ 1 ≠ ∞ :=
    ne_of_lt ((rootInformationMean_le_one d hij μ hA).trans_lt ENNReal.one_lt_top)
  simp only [hfin, or_false]
  exact rootInformationMean_eq_zero_iff_dirac d hij μ hA

lemma canonicalRootCoefficient_one_of_invariant (i j : Fin (d + 1)) (hij : i ≠ j)
    (hinv : ∀ t : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij t)) = μ) :
    canonicalRootCoefficient d μ i j = 1 := by
  rw [canonicalRootCoefficient, dite_eq_right hij, rootInformationMean_of_invariant d hij μ hA hinv]
  norm_num

/-- Actual real-time mean information is the root coefficient times time. -/
lemma rootInformationMean_eq_coefficient (i j : Fin (d + 1)) (hij : i ≠ j)
    {t : ℝ} (ht : 0 ≤ t) :
    rootInformationMean hij μ t =
      ENNReal.ofReal (t * canonicalRootCoefficient d μ i j) := by
  have hfin : rootInformationMean hij μ 1 ≠ ∞ :=
    ne_of_lt ((rootInformationMean_le_one d hij μ hA).trans_lt ENNReal.one_lt_top)
  rw [rootInformationMean_real d hij μ hA ht, canonicalRootCoefficient, dite_eq_right hij,
    ENNReal.ofReal_mul ht, ENNReal.ofReal_toReal hfin]

end DukePrimeDegree

end

end OAI
