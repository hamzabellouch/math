import OAI.NumberTheory.Ostmann.Arithmetic.MovingRealResidues
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSignedSpectator
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportWeight

namespace OAI

/-! # Fixed residue factors separated from the real moving support -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingResidueFlag (nodes : List MovingFormulaNode) (a : Bool → ℤ) : ℂ :=
  if movingResidueGate nodes a then 1 else 0

noncomputable def movingArchimedeanFlag (nodes : List MovingFormulaNode) (x : Bool → ℝ) : ℂ :=
  if movingArchimedeanGate nodes x then 1 else 0

noncomputable def movingSpectatorResidue {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (g : ∀ i, ZMod (q i) → ℂ)
    (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I) {n : ℕ} (T : MovingSlotData σ n)
    (a b : ℤ) : ℂ := ∏ i ∈ S, movingSignedSpectator value (g i) (D i) T a b

theorem movingArithmeticIndicator_residue_real {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    movingArithmeticIndicator value childBound pivotBound T XL XR =
      movingResidueFlag nodes (topGiantInput a b) * movingArchimedeanFlag nodes (topGiantReal XL XR) := by
  dsimp only
  have h := movingArithmeticSupport_residue_real value hvalue childBound pivotBound T hf XL XR a b M hM hL hR
  unfold movingArithmeticIndicator movingResidueFlag movingArchimedeanFlag
  by_cases hr : movingResidueGate
      (T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)) (topGiantInput a b) <;>
    by_cases ha : movingArchimedeanGate
      (T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)) (topGiantReal XL XR) <;>
    simp only [h, hr, ha, and_self, and_false, false_and, ite_true, ite_false, mul_one, mul_zero]

/-- On a fixed top residue pair the original spectator coefficient is a
fixed signed-residue value. The only remaining variable gate is real. -/
theorem moving_arithmetic_spectator_residue_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) (g : ∀ i, ZMod (q i) → ℂ)
    (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    movingArithmeticIndicator value childBound pivotBound T XL XR *
        (∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR) =
      (movingResidueFlag nodes (topGiantInput a b) * movingArchimedeanFlag nodes (topGiantReal XL XR)) *
        movingSpectatorResidue q value g D S T a b := by
  dsimp only
  have hflag := movingArithmeticIndicator_residue_real value hvalue childBound pivotBound T hf XL XR a b M hM hL hR
  by_cases hs : T.ArithmeticSupport value childBound pivotBound XL XR
  · have hI := hs.integral value hvalue childBound pivotBound T XL XR
    have hspec : (∏ i ∈ S, movingSlotSpectator value (g i) (D i) T XL XR) =
        movingSpectatorResidue q value g D S T a b := by
      apply Finset.prod_congr rfl
      intro i hi
      exact movingSlotSpectator_eq_residue value hvalue (g i) (D i) T hf XL XR a b M hI (hMq i hi) hL hR
    rw [hspec, hflag]
  · have hz : movingArithmeticIndicator value childBound pivotBound T XL XR = 0 :=
      ite_eq_right hs
    rw [hz, zero_mul, ← hflag, hz, zero_mul]

end Ostmann

end OAI
