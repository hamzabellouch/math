import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedCRT

namespace OAI

/-! # The separated two-history coefficient -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def movingSeparatedPairResidueCoefficient {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (a b : ℕ) : ℂ :=
  movingSeparatedResidueCoefficient q value outside (F false) (E false) g (Dq false) S
      (T false) (nodes false) R a b *
    conj (movingSeparatedResidueCoefficient q value outside (F true) (E true) g (Dq true) S
      (T true) (nodes true) R a b)

theorem movingSeparatedPairResidueCoefficient_modEq {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (hf : ∀ side, (T side).Frequencies (· ≠ 0))
    (hR : ∀ side, (T side).frequencyProduct ∣ R)
    (a b c d : ℕ) (M : ℤ) (hfrequency : R ^ (n + 1) ∣ M)
    (hsquare : ∀ side, ∀ o ∈ (T side).occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hspectator : ∀ i ∈ S, (q i : ℤ) ∣ M)
    (hL : (a : ℤ) ≡ (c : ℤ) [ZMOD M]) (hRight : (b : ℤ) ≡ (d : ℤ) [ZMOD M]) :
    movingSeparatedPairResidueCoefficient q value outside F E g Dq S T nodes R a b =
      movingSeparatedPairResidueCoefficient q value outside F E g Dq S T nodes R c d := by
  have he (side : Bool) := movingSeparatedResidueCoefficient_modEq q value outside
    (F side) (E side) g (Dq side) S (T side) (nodes side) R (hf side) (hR side)
    a b c d M hfrequency (hsquare side) hspectator hL hRight
  unfold movingSeparatedPairResidueCoefficient
  rw [he false, he true]

theorem movingReducedPairResidueCoefficient_eq_separated {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (hcover : ∀ p ∈ outside, ∃ i ∈ S, q i = p) (hg0 : ∀ i ∈ S, g i 0 = 0)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (hf : ∀ side, (T side).Frequencies (· ≠ 0))
    (hsmall : ∀ side i, (T side).Frequencies (fun f => IsCoprime f (value i : ℤ)))
    (hfmod : ∀ side i, (T side).Frequencies (fun f => (f : ZMod (value i)) ≠ 0))
    (R : ℤ) (hR : ∀ side, (T side).frequencyProduct ∣ R)
    (hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
    (hdistinct : ∀ side, (T side).CompensationDistinct value)
    (hden : ∀ side i, i ∈ S → (T side).ModularDenominators value (q i)) (a b : ℕ) :
    let nodes := fun side => (T side).formulaNodes value (fun i => (hprime i).ne_zero)
      childBound pivotBound (hf side) (.prime false) (.prime true)
    movingReducedPairResidueCoefficient q value outside F E g Dq S T nodes a b =
      movingSeparatedPairResidueCoefficient q value outside F E g Dq S T nodes R a b := by
  have he (side : Bool) := movingReducedResidueCoefficient_eq_separated q tier value hprime hdisjoint
    outside childBound pivotBound (F side) (E side) g (Dq side) S hcover hg0 (T side)
    (hlevels side) (hf side) (hsmall side) (hfmod side) R (hR side) hsmallR (hdistinct side)
    (hden side) a b
  dsimp only
  unfold movingReducedPairResidueCoefficient movingSeparatedPairResidueCoefficient
  rw [he false, he true]

end Ostmann

end OAI
