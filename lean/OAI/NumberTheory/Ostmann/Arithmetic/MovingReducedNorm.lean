import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedOuterFactor

namespace OAI

/-! # A concrete pointwise budget for the extracted original coefficient -/

namespace Ostmann
open scoped BigOperators Classical

theorem movingReducedResidueWeight_norm {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (a b : ℤ) (z : ℂ) :
    ‖movingReducedResidueWeight value outside T a b z‖ ≤ ‖z‖ := by
  unfold movingReducedResidueWeight
  split_ifs <;> simp

theorem movingReducedPairResidueCoefficient_norm {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (a b : ℕ) :
    ‖movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes a b‖ ≤
      (‖movingDataWeight (F false) (E false) (T false)‖ * ∏ i ∈ S, B i ^ (2 ^ n)) *
      (‖movingDataWeight (F true) (E true) (T true)‖ * ∏ i ∈ S, B i ^ (2 ^ n)) := by
  unfold movingReducedPairResidueCoefficient
  rw [norm_mul, Complex.norm_conj]
  apply mul_le_mul
  · exact (movingReducedResidueWeight_norm value outside _ a b _).trans
      (movingResidueCoefficient_norm q value _ _ g _ S B hB hg _ _ a b)
  · exact (movingReducedResidueWeight_norm value outside _ a b _).trans
      (movingResidueCoefficient_norm q value _ _ g _ S B hB hg _ _ a b)
  · exact norm_nonneg _
  · exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun i hi => pow_nonneg (hB i hi) _))

end Ostmann

end OAI
