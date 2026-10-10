import OAI.NumberTheory.Ostmann.Arithmetic.MovingSignedFormulas

namespace OAI

/-! # The original formula gate in frequency and internal-prime coordinates -/

namespace Ostmann
open scoped Classical

theorem movingNodeGuard_signed_values {σ : Type*}
    (value : σ → ℕ) (step : MovingSlotReversal σ) (hs : step.rootFrequency ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ)) :
    let g := movingNodeGuard (MovingSlotReversal.naturalProduct value step.leftSlots)
      (MovingSlotReversal.naturalProduct value step.rightSlots)
      step.rootFrequency step.leftFrequency step.rightFrequency hs childBound pivotBound L R
    g.pivot.value (fun b => (a b : ℚ)) =
        (step.signedNumerator value x y : ℚ) / step.rootFrequency ∧
      g.rightProduct.value (fun b => (a b : ℚ)) =
        ((y * MovingSlotReversal.naturalProduct value step.rightSlots : ℤ) : ℚ) := by
  dsimp only
  simp only [movingNodeGuard, wordTransferGuard, wordTransferStep, HistoryPivotStep.formula,
    movingNodeWord, HistoryFormula.value_bind, HistoryFormula.value_solve,
    HistoryFormula.value_listProduct, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, HistoryFormula.value_prime, Bool.false_eq_true, ite_false, ite_true,
    HistoryFormula.value_product, HistoryFormula.value_external, hL, hR,
    MovingSlotReversal.signedNumerator, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    mul_one, and_self]

theorem movingNodeGuard_residue_of_signedIntegral {σ : Type*}
    (value : σ → ℕ) (step : MovingSlotReversal σ) (hs : step.rootFrequency ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ))
    (hI : step.SignedIntegralAt value x y)
    (hroot : IsCoprime step.rootFrequency
      (y * MovingSlotReversal.naturalProduct value step.rightSlots : ℤ))
    (hpivot : IsCoprime step.rightFrequency
      ((MovingSlotReversal.naturalProduct value step.compensationSlots : ℤ) * step.signedPivot value x y)) :
    (movingNodeGuard (MovingSlotReversal.naturalProduct value step.leftSlots)
      (MovingSlotReversal.naturalProduct value step.rightSlots)
      step.rootFrequency step.leftFrequency step.rightFrequency hs childBound pivotBound L R).residueAt a := by
  let g := movingNodeGuard (MovingSlotReversal.naturalProduct value step.leftSlots)
    (MovingSlotReversal.naturalProduct value step.rightSlots)
    step.rootFrequency step.leftFrequency step.rightFrequency hs childBound pivotBound L R
  have hv := movingNodeGuard_signed_values value step hs childBound pivotBound L R a x y hL hR
  have hP : g.pivot.value (fun b => (a b : ℚ)) =
      (((MovingSlotReversal.naturalProduct value step.compensationSlots : ℤ) * step.signedPivot value x y : ℤ) : ℚ) := by
    rw [hv.1, hI]
    push_cast
    field_simp
  change g.residueAt a
  unfold WordTransferGuard.residueAt
  rw [g.pivot.smallDivisionTest_of_value a _ hP,
    g.rightProduct.smallDivisionTest_of_value a _ hv.2]
  constructor
  · change IsUnit (((MovingSlotReversal.naturalProduct value step.compensationSlots : ℤ) *
      step.signedPivot value x y : ℤ) : ZMod step.rightFrequency.natAbs)
    rwa [ZMod.coe_int_isUnit_iff_isCoprime, Int.natCast_natAbs, IsCoprime.abs_left_iff]
  · change IsUnit ((y * (MovingSlotReversal.naturalProduct value step.rightSlots : ℤ) : ℤ) :
      ZMod step.rootFrequency.natAbs)
    rwa [ZMod.coe_int_isUnit_iff_isCoprime, Int.natCast_natAbs, IsCoprime.abs_left_iff]

theorem movingSignedFrequencyUnits_local {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ)
    (h : movingSignedFrequencyUnits value T x y) : movingFrequencyLocalUnits T x y := by
  cases T with
  | leaf => exact h
  | node => exact h.1

theorem MovingSlotData.formulaNodes_residue_of_signedIntegral {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun f => IsCoprime f (value i : ℤ)))
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ))
    (hI : T.SignedIntegral value x y) (hunit : movingSignedFrequencyUnits value T x y) :
    ∀ f ∈ T.formulaNodes value hvalue childBound pivotBound hf L R, f.residueTests a := by
  induction T generalizing L R x y with
  | leaf => simp [formulaNodes]
  | @node n s CL CR U left right ihL ihR =>
    let step := MovingSlotData.step s CL CR U left right false
    have hU := MovingSlotReversal.naturalProduct_ne_zero value hvalue U
    let G := step.giantFormula value hf.1 hU L R
    have hG := step.giantFormula_of_signed_integral value hf.1 hU L R a x y hL hR hI.1
    have hroot : IsCoprime s (y * (MovingSlotReversal.naturalProduct value CR : ℤ)) := by
      apply IsCoprime.mul_right
      · exact ((MovingSlotData.node s CL CR U left right).frequencies_isCoprime y |>.mpr hunit.1.2).root.symm
      · exact (movingNaturalProduct_coprime value CR s
          (fun i _ => (hsmall i).root.symm)).symm
    have hpivot : IsCoprime right.frequency
        ((MovingSlotReversal.naturalProduct value U : ℤ) * step.signedPivot value x y) := by
      apply IsCoprime.mul_right
      · exact (movingNaturalProduct_coprime value U right.frequency
          (fun i _ => (hsmall i).2.2.root.symm)).symm
      · exact ((right.frequencies_isCoprime (step.signedPivot value x y)).mpr
          (movingSignedFrequencyUnits_local value right _ _ hunit.2.2).1).root.symm
    have hguard := movingNodeGuard_residue_of_signedIntegral value step hf.1
      (childBound (n + 1)) (pivotBound (n + 1)) L R a x y hL hR hI.1 hroot hpivot
    have hl := ihL hf.2.1 (fun i => (hsmall i).2.1) G L _ _ hG hL hI.2.1 hunit.2.1
    have hr := ihR hf.2.2 (fun i => (hsmall i).2.2) G R _ _ hG hR hI.2.2 hunit.2.2
    intro f hmem
    rcases List.mem_cons.mp hmem with hmem | hmem
    · subst f
      exact (MovingFormulaNode.residueTests_iff _ a).mpr
        ⟨hguard, step.giantFormula_signed_integral_iff value hf.1 hU L R a x y hL hR |>.mpr hI.1⟩
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact hl f hmem
      · exact hr f hmem

theorem moving_formula_residue_frequency_internal_iff {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j) (R₀ : ℤ)
    (hsmallR : ∀ i, IsCoprime (value i : ℤ) R₀)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hlevels : T.Levels tier) (hf : T.Frequencies (· ≠ 0))
    (hsmall : ∀ i, T.Frequencies (fun f => IsCoprime f (value i : ℤ)))
    (hfmod : ∀ i, T.Frequencies (fun f => (f : ZMod (value i)) ≠ 0))
    (hR₀ : T.frequencyProduct ∣ R₀) (hdistinct : T.CompensationDistinct value)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ)) :
    let nodes := T.formulaNodes value (fun i => (hprime i).ne_zero) childBound pivotBound hf L R
    movingResidueGate nodes a ∧ movingSignedFrequencyUnits value T x y ↔
      (∀ f ∈ nodes, f.guard.frequencyBounds) ∧
        movingFrequencyGate value R₀ T x y ∧ movingPrimeLineSupport value T x y := by
  let hvalue := fun i => (hprime i).ne_zero
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf L R
  have hint := T.formulaNodes_signed_integral_iff value hvalue childBound pivotBound hf L R a x y hL hR
  have hsplit := moving_frequency_internal_split tier value hprime hdisjoint R₀ hsmallR
    T hlevels hf hfmod hR₀ hdistinct x y
  change (movingResidueGate nodes a ∧ _) ↔ (∀ f ∈ nodes, _) ∧ _ ∧ _
  constructor
  · rintro ⟨hres, hunit⟩
    have hI : T.SignedIntegral value x y := hint.mp (fun f hf =>
      (f.residueTests_iff a).mp (hres f hf).1 |>.2)
    exact ⟨fun f hf => (hres f hf).2, hsplit.mpr ⟨hI, hunit⟩⟩
  · rintro ⟨hb, hg, hl⟩
    obtain ⟨hI, hunit⟩ := hsplit.mp ⟨hg, hl⟩
    have htests := T.formulaNodes_residue_of_signedIntegral value hvalue childBound pivotBound
      hf hsmall L R a x y hL hR hI hunit
    exact ⟨fun f hf => ⟨htests f hf, hb f hf⟩, hunit⟩

end Ostmann

end OAI
