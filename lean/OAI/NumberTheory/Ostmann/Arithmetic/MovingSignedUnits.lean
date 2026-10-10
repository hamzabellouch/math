import OAI.NumberTheory.Ostmann.Arithmetic.MovingSignedSpectator
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPairwiseSupport

namespace OAI

/-! # The giant unit tests on signed residue representatives -/

namespace Ostmann
open scoped Classical

theorem int_modEq_isCoprime_iff {x y m : ℤ} (h : x ≡ y [ZMOD m]) :
    IsCoprime x m ↔ IsCoprime y m := by
  have transport {a b : ℤ} (hab : a ≡ b [ZMOD m]) (ha : IsCoprime a m) :
      IsCoprime b m := by
    obtain ⟨k, hk⟩ := hab.dvd
    obtain ⟨u, v, huv⟩ := ha
    refine ⟨u, v - u * k, ?_⟩
    linear_combination huv + u * hk
  exact ⟨transport h, transport h.symm⟩

/-- The product records every frequency at or below this state. -/
def MovingSlotData.frequencyProduct {σ : Type*} : {n : ℕ} → MovingSlotData σ n → ℤ
  | _, .leaf s _ => s
  | _, .node s _ _ _ left right => s * left.frequencyProduct * right.frequencyProduct

theorem MovingSlotData.frequencies_isCoprime {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (x : ℤ) :
    T.Frequencies (fun s => IsCoprime x s) ↔ IsCoprime x T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    simp only [Frequencies, frequencyProduct, IsCoprime.mul_right_iff, ihL, ihR, and_assoc]

/-- Tests the two giants against every subtree frequency, every current
regular slot, and the fixed outside list. Mutual coprimality of the two
current giants is deliberately separate. -/
def movingLocalGiantUnits {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℤ) : Prop :=
  IsCoprime XL T.frequencyProduct ∧ IsCoprime XR T.frequencyProduct ∧
    IsCoprime XL (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) ∧
    IsCoprime XR (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) ∧
    IsCoprime XL (outside.prod : ℤ) ∧ IsCoprime XR (outside.prod : ℤ)

/-- Signed evaluation uses exact Euclidean division and hence is defined on
all residue representatives, including representatives off the real support. -/
noncomputable def movingSignedGiantUnits {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → Prop
  | _, T@(.leaf _ _), XL, XR => movingLocalGiantUnits value outside T XL XR
  | _, T@(.node s CL CR U left right), XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).signedPivot value XL XR
      movingLocalGiantUnits value outside T XL XR ∧
        movingSignedGiantUnits value outside left p XL ∧
        movingSignedGiantUnits value outside right p XR

def movingNaturalGiantUnits {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, T@(.leaf _ _), XL, XR => movingLocalGiantUnits value outside T XL XR
  | _, T@(.node s CL CR U left right), XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      movingLocalGiantUnits value outside T XL XR ∧
        movingNaturalGiantUnits value outside left p XL ∧
        movingNaturalGiantUnits value outside right p XR

theorem movingSignedGiantUnits_nat {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (hI : T.Integral value XL XR) :
    movingSignedGiantUnits value outside T XL XR ↔ movingNaturalGiantUnits value outside T XL XR := by
  induction T generalizing XL XR with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    simp only [movingSignedGiantUnits, movingNaturalGiantUnits,
      (MovingSlotData.step s CL CR U left right false).signedPivot_nat value hvalue hf.1 XL XR hI.1,
      ihL hf.2.1 _ _ hI.2.1, ihR hf.2.2 _ _ hI.2.2]

/-- A period for precisely the current unit tests and their descendant
Euclidean divisions. No real inequalities are used in this definition. -/
def movingGiantUnitPeriod {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ
  | _, T@(.leaf _ _) =>
      T.frequencyProduct * (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) * outside.prod
  | _, T@(.node s _ _ U left right) =>
      (T.frequencyProduct * (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) * outside.prod) *
        (s * (MovingSlotReversal.naturalProduct value U : ℤ)) *
        movingGiantUnitPeriod value outside left * movingGiantUnitPeriod value outside right

theorem movingLocalGiantUnits_modEq {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR YL YR : ℤ)
    (hL : XL ≡ YL [ZMOD T.frequencyProduct *
      (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) * outside.prod])
    (hR : XR ≡ YR [ZMOD T.frequencyProduct *
      (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) * outside.prod]) :
    movingLocalGiantUnits value outside T XL XR ↔ movingLocalGiantUnits value outside T YL YR := by
  have hfreq : T.frequencyProduct ∣ T.frequencyProduct *
      (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) * outside.prod :=
    ⟨(MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) * outside.prod, by ring⟩
  have hreg : (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) ∣ T.frequencyProduct *
      (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) * outside.prod := ⟨T.frequencyProduct * outside.prod, by ring⟩
  have hout : (outside.prod : ℤ) ∣ T.frequencyProduct *
      (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) * outside.prod := ⟨T.frequencyProduct * (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ), by ring⟩
  unfold movingLocalGiantUnits
  rw [int_modEq_isCoprime_iff (hL.of_dvd hfreq), int_modEq_isCoprime_iff (hR.of_dvd hfreq),
    int_modEq_isCoprime_iff (hL.of_dvd hreg), int_modEq_isCoprime_iff (hR.of_dvd hreg),
    int_modEq_isCoprime_iff (hL.of_dvd hout), int_modEq_isCoprime_iff (hR.of_dvd hout)]

theorem movingSignedGiantUnits_modEq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR YL YR : ℤ)
    (hL : XL ≡ YL [ZMOD movingGiantUnitPeriod value outside T])
    (hR : XR ≡ YR [ZMOD movingGiantUnitPeriod value outside T]) :
    movingSignedGiantUnits value outside T XL XR ↔ movingSignedGiantUnits value outside T YL YR := by
  induction T generalizing XL XR YL YR with
  | leaf s regular => exact movingLocalGiantUnits_modEq value outside _ _ _ _ _ hL hR
  | node s CL CR U left right ihL ihR =>
    let T := MovingSlotData.node s CL CR U left right
    let a := T.frequencyProduct * (MovingSlotReversal.naturalProduct value T.regularSlots : ℤ) * outside.prod
    let c := s * (MovingSlotReversal.naturalProduct value U : ℤ)
    let dl := movingGiantUnitPeriod value outside left
    let dr := movingGiantUnitPeriod value outside right
    have hd : movingGiantUnitPeriod value outside T = a * c * dl * dr := rfl
    have hl : movingLocalGiantUnits value outside T XL XR ↔ movingLocalGiantUnits value outside T YL YR :=
      movingLocalGiantUnits_modEq value outside T XL XR YL YR
        (hL.of_dvd ⟨c * dl * dr, by rw [hd]; ring⟩)
        (hR.of_dvd ⟨c * dl * dr, by rw [hd]; ring⟩)
    let step := MovingSlotData.step s CL CR U left right false
    let p := step.signedPivot value XL XR
    let r := step.signedPivot value YL YR
    have hp : p ≡ r [ZMOD a * dl * dr] :=
      step.signedPivot_modEq value hvalue hf.1 XL XR YL YR _
        (hL.of_dvd ⟨1, by change a * c * dl * dr = c * (a * dl * dr) * 1; ring⟩)
        (hR.of_dvd ⟨1, by change a * c * dl * dr = c * (a * dl * dr) * 1; ring⟩)
    have hleft := ihL hf.2.1 p XL r YL
      (hp.of_dvd ⟨a * dr, by ring⟩) (hL.of_dvd ⟨a * c * dr, by rw [hd]; ring⟩)
    have hright := ihR hf.2.2 p XR r YR
      (hp.of_dvd ⟨a * dl, by ring⟩) (hR.of_dvd ⟨a * c * dl, by rw [hd]; ring⟩)
    exact and_congr hl (and_congr hleft hright)

end Ostmann

end OAI
