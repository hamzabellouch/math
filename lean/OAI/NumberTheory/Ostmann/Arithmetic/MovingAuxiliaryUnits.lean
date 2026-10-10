import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportedWeight

namespace OAI

/-! # Separating inherited regular-slot units from the recursive residue tests -/

namespace Ostmann
open scoped Classical

def movingAuxiliaryLocalUnits {σ : Type*} (outside : List ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℤ) : Prop :=
  IsCoprime XL T.frequencyProduct ∧ IsCoprime XR T.frequencyProduct ∧
    IsCoprime XL (outside.prod : ℤ) ∧ IsCoprime XR (outside.prod : ℤ)

def movingAuxiliaryUnits {σ : Type*} (value : σ → ℕ) (outside : List ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, T@(.leaf _ _), XL, XR => movingAuxiliaryLocalUnits outside T XL XR
  | _, T@(.node s CL CR U left right), XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      movingAuxiliaryLocalUnits outside T XL XR ∧
        movingAuxiliaryUnits value outside left p XL ∧ movingAuxiliaryUnits value outside right p XR

theorem movingNaturalGiantUnits_auxiliary {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (h : movingNaturalGiantUnits value outside T XL XR) : movingAuxiliaryUnits value outside T XL XR := by
  induction T generalizing XL XR with
  | leaf => exact ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  | node s CL CR U left right ihL ihR =>
    exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2⟩,
      ihL _ _ h.2.1, ihR _ _ h.2.2⟩

private theorem localGiantUnits_of_pairwise {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hp : (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime)
    (hu : movingAuxiliaryLocalUnits outside T XL XR) : movingLocalGiantUnits value outside T XL XR := by
  have hcur : T.CurrentPairwise value XL XR := (List.pairwise_append.mp hp).1
  have h := (T.currentPairwise_iff value XL XR).mp hcur
  exact ⟨hu.1, hu.2.1, h.2.2.1.isCoprime, h.2.2.2.isCoprime, hu.2.2.1, hu.2.2.2⟩

theorem movingFullOutsidePairwise_giantUnits {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hp : movingFullOutsidePairwise value outside T XL XR)
    (hu : movingAuxiliaryUnits value outside T XL XR) : movingNaturalGiantUnits value outside T XL XR := by
  induction T generalizing XL XR with
  | leaf => exact localGiantUnits_of_pairwise value outside _ _ _ hp hu
  | node s CL CR U left right ihL ihR =>
    exact ⟨localGiantUnits_of_pairwise value outside _ _ _ hp.1 hu.1,
      ihL _ _ hp.2.1 hu.2.1, ihR _ _ hp.2.2 hu.2.2⟩

theorem movingFullSupport_auxiliary_iff {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    movingFullSupport value outside T XL XR ↔
      movingFullOutsidePairwise value outside T XL XR ∧ movingAuxiliaryUnits value outside T XL XR :=
  ⟨fun h => ⟨h.1, movingNaturalGiantUnits_auxiliary value outside T XL XR h.2⟩,
    fun h => ⟨h.1, movingFullOutsidePairwise_giantUnits value outside T XL XR h.1 h.2⟩⟩

private theorem currentOutsidePairwise_auxiliary_iff {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hu : movingAuxiliaryLocalUnits outside T XL XR) :
    (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime ↔
      T.CurrentPairwise value XL XR ∧ (T.regularSlots.map value ++ outside).Pairwise Nat.Coprime := by
  have hXL := Nat.coprime_list_prod_right_iff.mp hu.2.2.1.natCoprime
  have hXR := Nat.coprime_list_prod_right_iff.mp hu.2.2.2.natCoprime
  simp only [MovingSlotData.currentSlots, MovingSlotData.CurrentPairwise,
    List.cons_append, List.pairwise_cons, List.mem_cons, List.mem_append, forall_eq_or_imp]
  constructor
  · rintro ⟨⟨hp, hl⟩, hr, hs⟩
    exact ⟨⟨⟨hp, fun a ha => hl a (Or.inl ha)⟩,
      (fun a ha => hr a (Or.inl ha)), (List.pairwise_append.mp hs).1⟩, hs⟩
  · rintro ⟨⟨⟨hp, hl⟩, hr, _⟩, hs⟩
    exact ⟨⟨hp, fun a ha => ha.elim (hl a) (hXL a)⟩,
      (fun a ha => ha.elim (hr a) (hXR a)), hs⟩

theorem movingFullOutsidePairwise_auxiliary_iff {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hu : movingAuxiliaryUnits value outside T XL XR) :
    movingFullOutsidePairwise value outside T XL XR ↔
      T.FullPairwise value XL XR ∧ movingRegularOutsidePairwise value outside T := by
  induction T generalizing XL XR with
  | leaf => exact currentOutsidePairwise_auxiliary_iff value outside _ _ _ hu
  | node s CL CR U left right ihL ihR =>
    simp only [movingFullOutsidePairwise, MovingSlotData.FullPairwise,
      movingRegularOutsidePairwise, currentOutsidePairwise_auxiliary_iff value outside _ _ _ hu.1,
      ihL _ _ hu.2.1, ihR _ _ hu.2.2]
    tauto

private theorem naturalProduct_coprime_of_members {σ : Type*} (value : σ → ℕ) (s : ℤ)
    (L : List σ) (h : ∀ i ∈ L, IsCoprime s (value i : ℤ)) :
    IsCoprime s (MovingSlotReversal.naturalProduct value L : ℤ) := by
  induction L with
  | nil => simpa [MovingSlotReversal.naturalProduct] using (isCoprime_one_right (x := s))
  | cons a L ih =>
    simpa only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons, Nat.cast_mul]
      using (h a List.mem_cons_self).mul_right (ih (fun i hi => h i (List.mem_cons_of_mem a hi)))

theorem movingAuxiliaryUnits_cross {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n)
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ))) (XL XR : ℕ)
    (hu : movingAuxiliaryUnits value outside T XL XR) : T.CrossFrequencyUnits value XL XR := by
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
        (naturalProduct_coprime_of_members value left.frequency CL (fun i _ => (hsmall i).2.1.root))
    · simpa only [Nat.cast_mul] using hXR.root.symm.mul_right
        (naturalProduct_coprime_of_members value right.frequency CR (fun i _ => (hsmall i).2.2.root))

/-- All descendant regular-slot units have disappeared; only the top current
pair, the explicit square tests, and frequency/outside tests remain. -/
theorem movingFullSupport_auxiliary_square_iff {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hsmall : ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ))) (XL XR : ℕ)
    (hI : T.Integral value XL XR) :
    movingFullSupport value outside T XL XR ↔
      T.CurrentPairwise value XL XR ∧ movingRegularOutsidePairwise value outside T ∧
        T.PrimeSquareTests value XL XR ∧ movingAuxiliaryUnits value outside T XL XR := by
  rw [movingFullSupport_auxiliary_iff]
  constructor
  · rintro ⟨hp, hu⟩
    obtain ⟨hpair, hs⟩ := (movingFullOutsidePairwise_auxiliary_iff value outside T XL XR hu).mp hp
    obtain ⟨ht, hsq⟩ := (T.fullPairwise_iff_squareTests value hcoh hc XL XR hI
      (movingAuxiliaryUnits_cross value outside T hsmall XL XR hu)).mp hpair
    exact ⟨ht, hs, hsq, hu⟩
  · rintro ⟨ht, hs, hsq, hu⟩
    refine ⟨(movingFullOutsidePairwise_auxiliary_iff value outside T XL XR hu).mpr ⟨?_, hs⟩, hu⟩
    exact (T.fullPairwise_iff_squareTests value hcoh hc XL XR hI
      (movingAuxiliaryUnits_cross value outside T hsmall XL XR hu)).mpr ⟨ht, hsq⟩

end Ostmann

end OAI
