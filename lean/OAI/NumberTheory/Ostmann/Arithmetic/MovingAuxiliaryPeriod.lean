import OAI.NumberTheory.Ostmann.Arithmetic.MovingAuxiliaryUnits

namespace OAI

/-! # A residue period that omits inherited regular-slot unit tests -/

namespace Ostmann
open scoped Classical

noncomputable def movingSignedAuxiliaryUnits {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → Prop
  | _, T@(.leaf _ _), XL, XR => movingAuxiliaryLocalUnits outside T XL XR
  | _, T@(.node s CL CR U left right), XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).signedPivot value XL XR
      movingAuxiliaryLocalUnits outside T XL XR ∧
        movingSignedAuxiliaryUnits value outside left p XL ∧ movingSignedAuxiliaryUnits value outside right p XR

def movingAuxiliaryUnitPeriod {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ
  | _, T@(.leaf _ _) => T.frequencyProduct * outside.prod
  | _, T@(.node s _ _ U left right) =>
      (T.frequencyProduct * outside.prod) * (s * (MovingSlotReversal.naturalProduct value U : ℤ)) *
        movingAuxiliaryUnitPeriod value outside left * movingAuxiliaryUnitPeriod value outside right

theorem movingSignedAuxiliaryUnits_nat {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (hI : T.Integral value XL XR) :
    movingSignedAuxiliaryUnits value outside T XL XR ↔ movingAuxiliaryUnits value outside T XL XR := by
  induction T generalizing XL XR with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedAuxiliaryUnits, movingAuxiliaryUnits,
      (MovingSlotData.step s CL CR U left right false).signedPivot_nat value hvalue hf.1 XL XR hI.1,
      ihL hf.2.1 _ _ hI.2.1, ihR hf.2.2 _ _ hI.2.2]

theorem movingAuxiliaryLocalUnits_modEq {σ : Type*} (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR YL YR : ℤ)
    (hL : XL ≡ YL [ZMOD T.frequencyProduct * outside.prod])
    (hR : XR ≡ YR [ZMOD T.frequencyProduct * outside.prod]) :
    movingAuxiliaryLocalUnits outside T XL XR ↔ movingAuxiliaryLocalUnits outside T YL YR := by
  unfold movingAuxiliaryLocalUnits
  rw [int_modEq_isCoprime_iff (hL.of_dvd (dvd_mul_right _ _)),
    int_modEq_isCoprime_iff (hR.of_dvd (dvd_mul_right _ _)),
    int_modEq_isCoprime_iff (hL.of_dvd (dvd_mul_left _ _)),
    int_modEq_isCoprime_iff (hR.of_dvd (dvd_mul_left _ _))]

theorem movingSignedAuxiliaryUnits_modEq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR YL YR : ℤ)
    (hL : XL ≡ YL [ZMOD movingAuxiliaryUnitPeriod value outside T])
    (hR : XR ≡ YR [ZMOD movingAuxiliaryUnitPeriod value outside T]) :
    movingSignedAuxiliaryUnits value outside T XL XR ↔ movingSignedAuxiliaryUnits value outside T YL YR := by
  induction T generalizing XL XR YL YR with
  | leaf s regular => exact movingAuxiliaryLocalUnits_modEq outside _ _ _ _ _ hL hR
  | node s CL CR U left right ihL ihR =>
    let T := MovingSlotData.node s CL CR U left right
    let a := T.frequencyProduct * (outside.prod : ℤ)
    let c := s * (MovingSlotReversal.naturalProduct value U : ℤ)
    let dl := movingAuxiliaryUnitPeriod value outside left
    let dr := movingAuxiliaryUnitPeriod value outside right
    have hd : movingAuxiliaryUnitPeriod value outside T = a * c * dl * dr := rfl
    have hl : movingAuxiliaryLocalUnits outside T XL XR ↔ movingAuxiliaryLocalUnits outside T YL YR :=
      movingAuxiliaryLocalUnits_modEq outside T XL XR YL YR
        (hL.of_dvd ⟨c * dl * dr, by rw [hd]; ring⟩)
        (hR.of_dvd ⟨c * dl * dr, by rw [hd]; ring⟩)
    let step := MovingSlotData.step s CL CR U left right false
    let p := step.signedPivot value XL XR
    let r := step.signedPivot value YL YR
    have hp : p ≡ r [ZMOD a * dl * dr] :=
      step.signedPivot_modEq value hvalue hf.1 XL XR YL YR _
        (hL.of_dvd ⟨1, by change a * c * dl * dr = c * (a * dl * dr) * 1; ring⟩)
        (hR.of_dvd ⟨1, by change a * c * dl * dr = c * (a * dl * dr) * 1; ring⟩)
    exact and_congr hl (and_congr
      (ihL hf.2.1 p XL r YL (hp.of_dvd ⟨a * dr, by ring⟩)
        (hL.of_dvd ⟨a * c * dr, by rw [hd]; ring⟩))
      (ihR hf.2.2 p XR r YR (hp.of_dvd ⟨a * dl, by ring⟩)
        (hR.of_dvd ⟨a * c * dl, by rw [hd]; ring⟩)))

theorem movingAuxiliaryUnitPeriod_dvd_full {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) :
    movingAuxiliaryUnitPeriod value outside T ∣ movingGiantUnitPeriod value outside T := by
  induction T with
  | leaf s regular =>
    refine ⟨MovingSlotReversal.naturalProduct value regular, ?_⟩
    simp only [movingAuxiliaryUnitPeriod, movingGiantUnitPeriod, MovingSlotData.regularSlots]
    ring
  | node s CL CR U left right ihL ihR =>
    have hlocal : (MovingSlotData.node s CL CR U left right).frequencyProduct * (outside.prod : ℤ) ∣
        (MovingSlotData.node s CL CR U left right).frequencyProduct *
          (MovingSlotReversal.naturalProduct value (CL ++ CR) : ℤ) * outside.prod :=
      ⟨MovingSlotReversal.naturalProduct value (CL ++ CR), by ring⟩
    exact mul_dvd_mul (mul_dvd_mul (mul_dvd_mul hlocal (dvd_refl _)) ihL) ihR

end Ostmann

end OAI
