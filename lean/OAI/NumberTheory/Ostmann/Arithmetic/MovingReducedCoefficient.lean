import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedWeight

namespace OAI

/-! # Periodicity of the remaining arithmetic and spectator coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingResidueGate_modEq (nodes : List MovingFormulaNode) (x y : Bool → ℤ) (M : ℕ)
    (hM : movingArithmeticPeriod nodes ∣ M) (hxy : ∀ i, x i ≡ y i [ZMOD M]) :
    movingResidueGate nodes x ↔ movingResidueGate nodes y := by
  apply forall₂_congr
  intro f hf
  apply and_congr_left
  intro _
  exact f.residueTests_modEq x y (fun i => (hxy i).of_dvd
    (by exact_mod_cast (movingArithmeticPeriod_dvd nodes f hf).trans hM))

theorem movingResidueCoefficient_modEq {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (a b c d M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (a : ℤ) ≡ (c : ℤ) [ZMOD M]) (hR : (b : ℤ) ≡ (d : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    movingResidueCoefficient q value F E g D S T nodes a b =
      movingResidueCoefficient q value F E g D S T nodes c d := by
  dsimp only
  have hgates := movingResidueGate_modEq _ (topGiantInput a b) (topGiantInput c d) M hM
    (by intro i; cases i; exact hL; exact hR)
  have hs : movingSpectatorResidue q value g D S T a b = movingSpectatorResidue q value g D S T c d := by
    apply Finset.prod_congr rfl
    intro i hi
    exact movingSignedSpectator_modEq value hvalue (g i) (D i) T hf a b c d
      (hL.of_dvd (hMq i hi)) (hR.of_dvd (hMq i hi))
  simp only [movingResidueCoefficient, movingResidueFlag, hgates, hs]

theorem movingReducedResidueWeight_modEq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (a b c d : ℤ) (M : ℤ) (z w : ℂ)
    (hunit : movingAuxiliaryUnitPeriod value outside T ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hL : a ≡ c [ZMOD M]) (hR : b ≡ d [ZMOD M]) (hz : z = w) :
    movingReducedResidueWeight value outside T a b z = movingReducedResidueWeight value outside T c d w := by
  simp only [movingReducedResidueWeight, hz,
    movingReducedResidueSupport_modEq value hvalue outside T hf a b c d M hunit hsquare hL hR]

end Ostmann

end OAI
