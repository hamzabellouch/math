import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedPeriod
import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedWeight

namespace OAI

/-! # The literal original weight at the separated modulus -/

namespace Ostmann
open scoped Classical SchwartzMap

theorem MovingSlotData.CompensationPrimeData.distinct {σ : Type*}
    {value : σ → ℕ} {n : ℕ} {T : MovingSlotData σ n}
    (h : T.CompensationPrimeData value) : T.CompensationDistinct value := by
  induction T with
  | leaf => trivial
  | node s CL CR U left right ihL ihR =>
    exact ⟨h.2.1, ihL h.2.2.2.1, ihR h.2.2.2.2⟩

/-- The original moving weight factors through the separated modulus.
No cleared ancestor denominator or internal prime enters the frequency
period assumed here; all remaining periods are prime squares or spectators. -/
theorem movingOriginalGiantWeight_separated_factor {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg0 : ∀ i, g i 0 = 0)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (hcover : ∀ p ∈ outside, ∃ i ∈ S, q i = p)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hlevels : T.Levels tier) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (R : ℤ) (hR : T.frequencyProduct ∣ R) (hsmallR : ∀ i, IsCoprime (value i : ℤ) R)
    (hden : ∀ i ∈ S, T.ModularDenominators value (q i))
    (XL XR a b M : ℕ) (hfrequency : R ^ (n + 1) ∣ (M : ℤ))
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hspectator : ∀ i ∈ S, (q i : ℤ) ∣ M)
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hRight : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value (fun i => (hprime i).ne_zero)
      childBound pivotBound hf (.prime false) (.prime true)
    movingSupportedWeight value outside T XL XR
      (movingOriginalGiantWeight q value childBound pivotBound F E g Dq S ψ X lo hi φ G T t XL XR) =
      if XL.Coprime XR ∧
          XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
          XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) then
        movingSeparatedResidueCoefficient q value outside F E g Dq S T nodes R a b *
          movingRealKernel value T nodes ψ X lo hi hlo hhi φ G XL XR else 0 := by
  let nodes := T.formulaNodes value (fun i => (hprime i).ne_zero)
    childBound pivotBound hf (.prime false) (.prime true)
  have he := movingOriginalGiantWeight_reduced_factor q tier value hprime hdisjoint outside
    childBound pivotBound F E g hg0 Dq S ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    T t hT hlevels hcoh hc hf hsmall hfmod XL XR XL XR 0
    (dvd_zero _) (fun _ _ => dvd_zero _) (dvd_zero _) (fun _ _ _ _ => dvd_zero _)
    (Int.ModEq.refl _) (Int.ModEq.refl _)
  dsimp only at he ⊢
  have hcsep := movingReducedResidueCoefficient_eq_separated q tier value hprime hdisjoint outside
    childBound pivotBound F E g Dq S hcover (fun i _ => hg0 i) T hlevels hf hsmall hfmod
    R hR hsmallR hc.distinct hden XL XR
  have hperiod := movingSeparatedResidueCoefficient_modEq q value outside F E g Dq S T nodes R hf hR
    XL XR a b M hfrequency hsquare hspectator hL hRight
  rw [hcsep, hperiod] at he
  exact he

end Ostmann

end OAI
