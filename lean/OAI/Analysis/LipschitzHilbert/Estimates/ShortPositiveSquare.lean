import OAI.Analysis.LipschitzHilbert.Estimates.ShortPositiveEnergy
import OAI.Analysis.LipschitzHilbert.Packets.PositivePacketDerivative

namespace OAI

/-! Local L1 control of the squared positive packet square function. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.LinePacketFamily

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

theorem short_positive_square (P : LinePacketFamily N κ ι) (u r B : ℝ)
    (hr : 0 < r) (hB : 0 ≤ B) (hbudget : P.HasLocalBudget B) :
    (∫ x in Icc (u-r) (u+r), ∑ j, if P.length j ≤ r then P.positiveScale j x ^ 2 else 0) ≤
      (65536 * Real.pi) * (4 * Real.pi) ^ 6 * B * r := by
  let E := fun x => ∑ j, if P.length j ≤ r then P.coefficientEnergy j x else 0
  let S := fun x => ∑ j, if P.length j ≤ r then P.positiveScale j x ^ 2 else 0
  have hpoint (x : ℝ) : S x ≤ (4 * Real.pi) ^ 2 * E x := by
    dsimp [S,E]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : P.length j ≤ r
    · simpa only [ite_eq_left hj] using P.positiveScale_square j x
    · simp only [ite_eq_right hj, mul_zero, le_refl]
  have hecont : Continuous E := by
    apply continuous_finsetSum
    intro j _
    by_cases hj : P.length j ≤ r
    · simp only [ite_eq_left hj, coefficientEnergy]
      exact continuous_finsetSum _ (fun i _ => (P.envelope_continuous j i).const_mul _)
    · simp only [ite_eq_right hj]
      exact continuous_const
  have hscont : Continuous S := by
    apply continuous_finsetSum
    intro j _
    by_cases hj : P.length j ≤ r
    · simp only [ite_eq_left hj]
      exact (P.positiveScale_continuous j).pow 2
    · simp only [ite_eq_right hj]
      exact continuous_const
  have hi : IntegrableOn S (Icc (u-r) (u+r)) := hscont.continuousOn.integrableOn_Icc
  have hei : IntegrableOn E (Icc (u-r) (u+r)) := hecont.continuousOn.integrableOn_Icc
  change (∫ x in Icc (u-r) (u+r), S x) ≤ _
  calc
    _ ≤ ∫ x in Icc (u-r) (u+r), (4 * Real.pi) ^ 2 * E x :=
      integral_mono hi (hei.const_mul _) hpoint
    _ = (4 * Real.pi) ^ 2 * ∫ x in Icc (u-r) (u+r), E x := integral_const_mul _ _
    _ ≤ (4 * Real.pi) ^ 2 * ((65536 * Real.pi) * (B*r) * (4 * Real.pi) ^ 4) :=
      mul_le_mul_of_nonneg_left (P.short_coefficient_energy u r B hr hB hbudget) (sq_nonneg _)
    _ = _ := by ring

end LipschitzHilbert.LinePacketFamily

end

end OAI
