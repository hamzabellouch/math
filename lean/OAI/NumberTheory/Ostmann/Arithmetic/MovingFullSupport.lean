import OAI.NumberTheory.Ostmann.Arithmetic.MovingSignedUnits
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOccurrenceSquares

namespace OAI

/-! # Full pairwise and subtree-frequency support, with the top giant pair separated -/

namespace Ostmann
open scoped Classical

private theorem coprime_naturalProduct {σ : Type*} (value : σ → ℕ) (s : ℤ) (L : List σ)
    (h : ∀ i ∈ L, IsCoprime s (value i : ℤ)) :
    IsCoprime s (MovingSlotReversal.naturalProduct value L : ℤ) := by
  induction L with
  | nil => simpa [MovingSlotReversal.naturalProduct] using (isCoprime_one_right (x := s))
  | cons a L ih =>
    simpa only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons, Nat.cast_mul]
      using (h a List.mem_cons_self).mul_right (ih (fun i hi => h i (List.mem_cons_of_mem a hi)))

theorem movingNaturalGiantUnits_cross {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n)
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ))) (XL XR : ℕ)
    (hu : movingNaturalGiantUnits value outside T XL XR) :
    T.CrossFrequencyUnits value XL XR := by
  induction T generalizing XL XR with
  | leaf => trivial
  | node s CL CR U left right ihL ihR =>
    have hXL := (left.frequencies_isCoprime (XL : ℤ)).mpr
      (hu.1.1.of_isCoprime_of_dvd_right ⟨s * right.frequencyProduct, by
        simp only [MovingSlotData.frequencyProduct]; ring⟩)
    have hXR := (right.frequencies_isCoprime (XR : ℤ)).mpr
      (hu.1.2.1.of_isCoprime_of_dvd_right ⟨s * left.frequencyProduct, by
        simp only [MovingSlotData.frequencyProduct]; ring⟩)
    refine ⟨?_, ?_, ihL (fun i => (hsmall i).2.1) _ _ hu.2.1,
      ihR (fun i => (hsmall i).2.2) _ _ hu.2.2⟩
    · simpa only [Nat.cast_mul] using hXL.root.symm.mul_right
        (coprime_naturalProduct value left.frequency CL (fun i _ => (hsmall i).2.1.root))
    · simpa only [Nat.cast_mul] using hXR.root.symm.mul_right
        (coprime_naturalProduct value right.frequency CR (fun i _ => (hsmall i).2.2.root))

theorem MovingSlotData.currentPairwise_iff {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℕ) :
    T.CurrentPairwise value XL XR ↔ XL.Coprime XR ∧
      (T.regularSlots.map value).Pairwise Nat.Coprime ∧
      XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
      XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) := by
  simp only [CurrentPairwise, currentSlots, List.pairwise_cons, List.mem_cons,
    forall_eq_or_imp, MovingSlotReversal.naturalProduct, Nat.coprime_list_prod_right_iff]
  tauto

/-- The outside list is fixed while the current regular slots change. These
small-slot tests are independent of both top giant values. -/
def movingRegularOutsidePairwise {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, T@(.leaf _ _) => (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime
  | _, T@(.node _ _ _ _ left right) =>
      (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime ∧
        movingRegularOutsidePairwise value outside left ∧ movingRegularOutsidePairwise value outside right

/-- Literal pairwise support at every current state, including the fixed
outside list from the manuscript's recursive average. -/
def movingFullOutsidePairwise {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, T@(.leaf _ _), XL, XR => (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime
  | _, T@(.node s CL CR U left right), XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime ∧
        movingFullOutsidePairwise value outside left p XL ∧ movingFullOutsidePairwise value outside right p XR

private theorem currentOutsidePairwise_iff {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hu : movingLocalGiantUnits value outside T XL XR) :
    (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime ↔
      T.CurrentPairwise value XL XR ∧ (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
  have hXL := Nat.coprime_list_prod_right_iff.mp (hu.2.2.2.2.1.natCoprime)
  have hXR := Nat.coprime_list_prod_right_iff.mp (hu.2.2.2.2.2.natCoprime)
  simp only [MovingSlotData.currentSlots, MovingSlotData.CurrentPairwise,
    List.cons_append, List.pairwise_cons, List.mem_cons, List.mem_append,
    forall_eq_or_imp]
  constructor
  · rintro ⟨⟨hp, hl⟩, hr, hs⟩
    exact ⟨⟨⟨hp, fun a ha => hl a (Or.inl ha)⟩,
      (fun a ha => hr a (Or.inl ha)), (List.pairwise_append.mp hs).1⟩, hs⟩
  · rintro ⟨⟨⟨hp, hl⟩, hr, _⟩, hs⟩
    exact ⟨⟨hp, fun a ha => ha.elim (hl a) (hXL a)⟩,
      (fun a ha => ha.elim (hr a) (hXR a)), hs⟩

theorem movingFullOutsidePairwise_iff {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hu : movingNaturalGiantUnits value outside T XL XR) :
    movingFullOutsidePairwise value outside T XL XR ↔
      T.FullPairwise value XL XR ∧ movingRegularOutsidePairwise value outside T := by
  induction T generalizing XL XR with
  | leaf s regular => exact currentOutsidePairwise_iff value outside _ XL XR hu
  | node s CL CR U left right ihL ihR =>
    simp only [movingFullOutsidePairwise, MovingSlotData.FullPairwise,
      movingRegularOutsidePairwise, currentOutsidePairwise_iff value outside _ XL XR hu.1,
      ihL _ _ hu.2.1, ihR _ _ hu.2.2]
    tauto

/-- The only nonperiodic coprimality test left after descent is the mutual
coprimality of the two top giants. All subtree and outside tests remain. -/
theorem movingFullOutsidePairwise_square_iff {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hcoh : T.RegularCoherent)
    (hc : T.CompensationPrimeData value)
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ))) (XL XR : ℕ)
    (hI : T.Integral value XL XR) :
    (movingFullOutsidePairwise value outside T XL XR ∧ movingNaturalGiantUnits value outside T XL XR) ↔
      XL.Coprime XR ∧ movingRegularOutsidePairwise value outside T ∧
        T.PrimeSquareTests value XL XR ∧ movingNaturalGiantUnits value outside T XL XR := by
  have htop (hu : movingNaturalGiantUnits value outside T XL XR) :
      XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) ∧
      XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) := by
    cases T with
    | leaf => exact ⟨hu.2.2.1.natCoprime, hu.2.2.2.1.natCoprime⟩
    | node => exact ⟨hu.1.2.2.1.natCoprime, hu.1.2.2.2.1.natCoprime⟩
  have hregular (hs : movingRegularOutsidePairwise value outside T) :
      (T.regularSlots.map value).Pairwise Nat.Coprime := by
    have h : (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
      cases T with
      | leaf => exact hs
      | node => exact hs.1
    exact (List.pairwise_append.mp h).1
  constructor
  · rintro ⟨hp, hu⟩
    obtain ⟨hf, hs⟩ := (movingFullOutsidePairwise_iff value outside T XL XR hu).mp hp
    obtain ⟨ht, hsq⟩ := (T.fullPairwise_iff_squareTests value hcoh hc XL XR hI
      (movingNaturalGiantUnits_cross value outside T hsmall XL XR hu)).mp hf
    exact ⟨(T.currentPairwise_iff value XL XR).mp ht |>.1, hs, hsq, hu⟩
  · rintro ⟨hpair, hs, hsq, hu⟩
    refine ⟨(movingFullOutsidePairwise_iff value outside T XL XR hu).mpr ⟨?_, hs⟩, hu⟩
    apply (T.fullPairwise_iff_squareTests value hcoh hc XL XR hI
      (movingNaturalGiantUnits_cross value outside T hsmall XL XR hu)).mpr
    exact ⟨(T.currentPairwise_iff value XL XR).mpr ⟨hpair, hregular hs, htop hu⟩, hsq⟩

end Ostmann

end OAI
