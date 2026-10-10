import OAI.MeasureTheory.Falconer.Slicing.GaussianMomentWeights

namespace OAI

/-! # A common fixed coefficient for the original finite-scale moment bounds -/

namespace Falconer

theorem exists_gaussian_moment_coefficient (h : ℕ) (t q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (4*gaussianVectorBandConstant)^h*L*gaussianFrostmanFactor h t ≤ C*L ∧
      (2*gaussianPairBandConstant)^h*L*gaussianFrostmanFactor h q ≤ C*L ∧
      (2*gaussianPairBandConstant)^h*(|L*gaussianFrostmanFactor h q|+1) ≤ C*L := by
  let P := (4*gaussianVectorBandConstant)^h*gaussianFrostmanFactor h t
  let Q := (2*gaussianPairBandConstant)^h*gaussianFrostmanFactor h q
  let U := (2*gaussianPairBandConstant)^h*(|gaussianFrostmanFactor h q|+1)
  let C := |P|+|Q|+U+1
  have hG := gaussianPairBandConstant_pos
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hPC : P ≤ C := by dsimp [C]; linarith [le_abs_self P,abs_nonneg Q]
  have hQC : Q ≤ C := by dsimp [C]; linarith [le_abs_self Q,abs_nonneg P]
  have hUC : U ≤ C := by dsimp [C]; linarith [abs_nonneg P,abs_nonneg Q]
  refine ⟨C,hC,?_⟩
  intro L hL
  have hL0 : 0 ≤ L := by linarith
  refine ⟨?_,?_,?_⟩
  · simpa only [P,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hPC hL0
  · simpa only [Q,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hQC hL0
  · calc
      _ = (2*gaussianPairBandConstant)^h*(L*|gaussianFrostmanFactor h q|+1) := by
        rw [abs_mul,abs_of_nonneg hL0]
      _ ≤ (2*gaussianPairBandConstant)^h*(L*|gaussianFrostmanFactor h q|+L) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hL _) (by positivity)
      _ = U*L := by dsimp [U]; ring
      _ ≤ C*L := mul_le_mul_of_nonneg_right hUC hL0

end Falconer

end OAI
