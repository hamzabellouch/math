import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullSupport

namespace OAI

/-! # The full moving support as one explicit residue mask -/

namespace Ostmann
open scoped Classical

noncomputable def movingSquareLineSupport {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℤ) : Prop :=
  ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
    let φ := MovingSlotReversal.naturalReduction (value i ^ 2) value
    φ (movingSlotLine o.path o.current).a * (XL : ZMod (value i ^ 2)) +
      φ (movingSlotLine o.path o.current).b * (XR : ZMod (value i ^ 2)) ≠ 0

theorem movingSquareLineSupport_modEq {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR YL YR M : ℤ)
    (hM : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    movingSquareLineSupport value T XL XR ↔ movingSquareLineSupport value T YL YR := by
  apply forall₂_congr
  intro o ho
  apply forall₂_congr
  intro i hi
  have hl : (XL : ZMod (value i ^ 2)) = (YL : ZMod (value i ^ 2)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hL.of_dvd (by exact_mod_cast hM o ho i hi))
  have hr : (XR : ZMod (value i ^ 2)) = (YR : ZMod (value i ^ 2)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hR.of_dvd (by exact_mod_cast hM o ho i hi))
  dsimp only
  rw [hl, hr]

/-- All terms here are periodic; the mutual top-giant gcd is kept outside. -/
noncomputable def movingFullResidueSupport {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℤ) : Prop :=
  movingRegularOutsidePairwise value outside T ∧ movingSquareLineSupport value T XL XR ∧
    movingSignedGiantUnits value outside T XL XR

theorem movingFullResidueSupport_modEq {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (XL XR YL YR M : ℤ)
    (hunit : movingGiantUnitPeriod value outside T ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hL : XL ≡ YL [ZMOD M]) (hR : XR ≡ YR [ZMOD M]) :
    movingFullResidueSupport value outside T XL XR ↔ movingFullResidueSupport value outside T YL YR := by
  unfold movingFullResidueSupport
  rw [movingSquareLineSupport_modEq value T XL XR YL YR M hsquare hL hR,
    movingSignedGiantUnits_modEq value hvalue outside T hf XL XR YL YR
      (hL.of_dvd hunit) (hR.of_dvd hunit)]

/-- The manuscript's pairwise, outside-list and all-subtree-frequency tests
are identified exactly, on the integral support already forced by the weight. -/
theorem movingFullSupport_residue_iff {σ : Type*} (tier : σ → ℕ) (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hlevels : T.Levels tier) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR a b : ℕ) (M : ℤ) (hI : T.Integral value XL XR)
    (hunit : movingGiantUnitPeriod value outside T ∣ M)
    (hsquare : ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, (value i ^ 2 : ℤ) ∣ M)
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    (movingFullOutsidePairwise value outside T XL XR ∧ movingNaturalGiantUnits value outside T XL XR) ↔
      XL.Coprime XR ∧ movingFullResidueSupport value outside T a b := by
  have hvalue : ∀ i, value i ≠ 0 := fun i => (hprime i).ne_zero
  rw [movingFullOutsidePairwise_square_iff value outside T hcoh hc hsmall XL XR hI,
    T.squareTests_iff_lines tier value hprime hdisjoint hlevels hfmod XL XR hI]
  have hsq : (∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
      let φ := MovingSlotReversal.naturalReduction (value i ^ 2) value
      φ (movingSlotLine o.path o.current).a * (XL : ZMod (value i ^ 2)) +
        φ (movingSlotLine o.path o.current).b * (XR : ZMod (value i ^ 2)) ≠ 0) ↔
      movingSquareLineSupport value T XL XR := by
    simp only [movingSquareLineSupport, Int.cast_natCast]
  rw [hsq, ← movingSignedGiantUnits_nat value hvalue outside T hf XL XR hI]
  change XL.Coprime XR ∧ movingFullResidueSupport value outside T XL XR ↔ _
  rw [movingFullResidueSupport_modEq value hvalue outside T hf XL XR a b M hunit hsquare hL hR]

end Ostmann

end OAI
