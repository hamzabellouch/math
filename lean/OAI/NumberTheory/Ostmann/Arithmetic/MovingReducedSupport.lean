import OAI.NumberTheory.Ostmann.Arithmetic.MovingAuxiliaryCoprime

namespace OAI

/-! # The recursive residue support after extracting the regular-prime units -/

namespace Ostmann
open scoped Classical

noncomputable def movingReducedResidueSupport {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℤ) : Prop :=
  movingRegularOutsidePairwise value outside T ∧ movingSquareLineSupport value T XL XR ∧
    movingSignedAuxiliaryUnits value outside T XL XR

theorem movingReducedResidueSupport_modEq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR YL YR M : ℤ)
    (hunit : movingAuxiliaryUnitPeriod value outside T ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    movingReducedResidueSupport value outside T XL XR ↔
      movingReducedResidueSupport value outside T YL YR := by
  unfold movingReducedResidueSupport
  rw [movingSquareLineSupport_modEq value T XL XR YL YR M hsquare hL hR,
    movingSignedAuxiliaryUnits_modEq value hvalue outside T hf XL XR YL YR
      (hL.of_dvd hunit) (hR.of_dvd hunit)]

theorem movingFullSupport_reduced_iff {σ : Type*} (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hlevels : T.Levels tier) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR : ℕ) (hI : T.Integral value XL XR) :
    movingFullSupport value outside T XL XR ↔
      XL.Coprime XR ∧
      XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
      XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
      movingReducedResidueSupport value outside T XL XR := by
  rw [movingFullSupport_auxiliary_square_iff value outside T hcoh hc hsmall XL XR hI,
    T.currentPairwise_iff value XL XR,
    T.squareTests_iff_lines tier value hprime hdisjoint hlevels hfmod XL XR hI,
    ← movingSignedAuxiliaryUnits_nat value (fun i => (hprime i).ne_zero) outside T hf XL XR hI]
  have hstatic : movingRegularOutsidePairwise value outside T →
      (T.regularSlots.map value).Pairwise Nat.Coprime := by
    intro h
    have hr : (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
      cases T with
      | leaf => exact h
      | node => exact h.1
    exact (List.pairwise_append.mp hr).1
  simp only [movingReducedResidueSupport, movingSquareLineSupport, Int.cast_natCast]
  tauto

noncomputable def movingReducedResidueWeight {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (a b : ℤ) (z : ℂ) : ℂ :=
  if movingReducedResidueSupport value outside T a b then z else 0

theorem movingSupportedWeight_reduced_residue {σ : Type*} (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hlevels : T.Levels tier) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR a b : ℕ) (M : ℤ) (z : ℂ) (hI : z ≠ 0 → T.Integral value XL XR)
    (hunit : movingAuxiliaryUnitPeriod value outside T ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    movingSupportedWeight value outside T XL XR z =
      if XL.Coprime XR ∧
          XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
          XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) then
        movingReducedResidueWeight value outside T a b z else 0 := by
  by_cases hz : z = 0
  · simp [movingSupportedWeight, movingReducedResidueWeight, hz]
  · have hs := movingFullSupport_reduced_iff tier value hprime hdisjoint outside T hlevels hcoh hc
      hf hsmall hfmod XL XR (hI hz)
    rw [movingReducedResidueSupport_modEq value (fun i => (hprime i).ne_zero) outside T hf
      XL XR a b M hunit hsquare hL hR] at hs
    unfold movingSupportedWeight movingReducedResidueWeight
    rw [hs]
    split_ifs <;> simp_all

end Ostmann

end OAI
