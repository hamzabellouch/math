import OAI.NumberTheory.Ostmann.Arithmetic.MovingOutsideResidues
import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedCoefficient

namespace OAI

/-! # The original remainder coefficient in separated arithmetic coordinates -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingSeparatedSupport {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode)
    (R : ℤ) (x y : ℤ) : Prop :=
  movingRegularOutsidePairwise value outside T ∧ movingSquareLineSupport value T x y ∧
    (∀ f ∈ nodes, f.guard.frequencyBounds) ∧
      movingFrequencyGate value R T x y ∧ movingPrimeLineSupport value T x y

noncomputable def movingSeparatedResidueCoefficient {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (R : ℤ) (x y : ℤ) : ℂ :=
  if movingSeparatedSupport value outside T nodes R x y then
    (∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T x y) * movingDataWeight F E T
  else 0

theorem movingSpectatorResidue_eq_modularProduct {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : MovingSlotData σ n) (hden : ∀ i ∈ S, T.ModularDenominators value (q i))
    (x y : ℤ) (hI : T.SignedIntegral value x y) :
    movingSpectatorResidue q value g D S T x y =
      ∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T x y := by
  apply Finset.prod_congr rfl
  intro i hi
  exact movingSignedSpectator_eq_modular value (q i) (g i) (D i) T (hden i hi) x y hI

/-- Exact identity for the literal original reduced residue coefficient.
Its frequency factor has a frequency-only period; the other factors use
only internal-prime squares and individual spectator primes. -/
theorem movingReducedResidueCoefficient_eq_separated {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (hcover : ∀ p ∈ outside, ∃ i ∈ S, q i = p)
    (hg0 : ∀ i ∈ S, g i 0 = 0)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun f => IsCoprime f (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun f => (f : ZMod (value i)) ≠ 0))
    (R₀ : ℤ) (hR₀ : T.frequencyProduct ∣ R₀)
    (hsmallR : ∀ i, IsCoprime (value i : ℤ) R₀) (hdistinct : T.CompensationDistinct value)
    (hden : ∀ i ∈ S, T.ModularDenominators value (q i)) (a b : ℕ) :
    let nodes := T.formulaNodes value (fun i => (hprime i).ne_zero)
      childBound pivotBound hf (.prime false) (.prime true)
    movingReducedResidueWeight value outside T a b
        (movingResidueCoefficient q value F E g D S T nodes a b) =
      movingSeparatedResidueCoefficient q value outside F E g D S T nodes R₀ a b := by
  let hvalue := fun i => (hprime i).ne_zero
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  let input := topGiantInput a b
  let z := ∏ i ∈ S, movingModularSpectator value (q i) (g i) (D i) T (a : ℤ) (b : ℤ)
  have hL : (HistoryFormula.prime false).value (fun j => (input j : ℚ)) = (a : ℚ) := by
    simp [input, topGiantInput]
  have hR : (HistoryFormula.prime true).value (fun j => (input j : ℚ)) = (b : ℚ) := by
    simp [input, topGiantInput]
  have hbridge := moving_formula_residue_frequency_internal_iff tier value hprime hdisjoint
    R₀ hsmallR childBound pivotBound T hlevels hf hsmall hfmod hR₀ hdistinct
    (.prime false) (.prime true) input a b hL hR
  have hint := T.formulaNodes_signed_integral_iff value hvalue childBound pivotBound hf
    (.prime false) (.prime true) input a b hL hR
  have hspec (hI : T.SignedIntegral value a b) : movingSpectatorResidue q value g D S T a b = z :=
    movingSpectatorResidue_eq_modularProduct q value g D S T hden a b hI
  have hmask : movingReducedResidueWeight value outside T a b
        (movingResidueCoefficient q value F E g D S T nodes a b) =
      if movingReducedResidueSupport value outside T a b ∧ movingResidueGate nodes input then
        movingSpectatorResidue q value g D S T a b * movingDataWeight F E T else 0 := by
    change (if movingReducedResidueSupport value outside T a b then
      ((if movingResidueGate nodes input then 1 else 0) *
        movingSpectatorResidue q value g D S T a b) * movingDataWeight F E T else 0) = _
    by_cases ha : movingReducedResidueSupport value outside T a b <;>
      by_cases hb : movingResidueGate nodes input <;> simp [ha, hb]
  change movingReducedResidueWeight value outside T a b
      (movingResidueCoefficient q value F E g D S T nodes a b) = _
  rw [hmask]
  by_cases hold : movingReducedResidueSupport value outside T a b ∧ movingResidueGate nodes input
  · have haux := (movingSignedAuxiliaryUnits_split value outside T a b).mp hold.1.2.2
    have hs := hbridge.mp ⟨hold.2, haux.1⟩
    have hnew : movingSeparatedSupport value outside T nodes R₀ a b :=
      ⟨hold.1.1, hold.1.2.1, hs⟩
    have hI : T.SignedIntegral value a b := hint.mp (fun f hf =>
      (f.residueTests_iff input).mp (hold.2 f hf).1 |>.2)
    rw [ite_eq_left hold]
    change _ = if movingSeparatedSupport value outside T nodes R₀ a b then _ else 0
    rw [ite_eq_left hnew, hspec hI]
  · rw [ite_eq_right hold]
    unfold movingSeparatedResidueCoefficient
    by_cases hnew : movingSeparatedSupport value outside T nodes R₀ a b
    · rw [ite_eq_left hnew]
      have hs := (moving_frequency_internal_split tier value hprime hdisjoint R₀ hsmallR
        T hlevels hf hfmod hR₀ hdistinct a b).mp hnew.2.2.2
      have hres := (hbridge.mpr ⟨hnew.2.2.1, hnew.2.2.2⟩).1
      have hz : z = 0 := by
        by_contra hz
        have hout := movingModularSpectatorProduct_outside_units value q g D S hg0 outside hcover
          T hden a b hs.1 hz
        have haux := (movingSignedAuxiliaryUnits_split value outside T a b).mpr ⟨hs.2, hout⟩
        exact hold ⟨⟨hnew.1, hnew.2.1, haux⟩, hres⟩
      exact (show z * movingDataWeight F E T = 0 by rw [hz, zero_mul]).symm
    · rw [ite_eq_right hnew]

end Ostmann

end OAI
