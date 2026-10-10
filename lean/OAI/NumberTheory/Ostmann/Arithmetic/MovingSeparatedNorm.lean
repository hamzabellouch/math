import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedPair

namespace OAI

/-! # Pointwise bounds at the separated arithmetic modulus -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSeparatedResidueCoefficient_norm {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode)
    (R x y : ℤ) :
    ‖movingSeparatedResidueCoefficient q value outside F E g D S T nodes R x y‖ ≤
      ‖movingDataWeight F E T‖ * ∏ i ∈ S, B i ^ (2 ^ n) := by
  unfold movingSeparatedResidueCoefficient
  split_ifs
  · rw [norm_mul, norm_prod, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i hi => movingModularSpectator_norm value (q i) (g i) (D i)
        (B i) (hB i hi) (hg i hi) T x y)
  · simp only [norm_zero]
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i hi => pow_nonneg (hB i hi) _)

theorem movingSeparatedPairResidueCoefficient_norm {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (x y : ℕ) :
    ‖movingSeparatedPairResidueCoefficient q value outside F E g D S T nodes R x y‖ ≤
      (‖movingDataWeight (F false) (E false) (T false)‖ * ∏ i ∈ S, B i ^ (2 ^ n)) *
      (‖movingDataWeight (F true) (E true) (T true)‖ * ∏ i ∈ S, B i ^ (2 ^ n)) := by
  unfold movingSeparatedPairResidueCoefficient
  rw [norm_mul, Complex.norm_conj]
  apply mul_le_mul
  · exact movingSeparatedResidueCoefficient_norm q value outside _ _ g _ S B hB hg _ _ R x y
  · exact movingSeparatedResidueCoefficient_norm q value outside _ _ g _ S B hB hg _ _ R x y
  · exact norm_nonneg _
  · exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i hi => pow_nonneg (hB i hi) _)

end Ostmann

end OAI
