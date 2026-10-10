import OAI.NumberTheory.Ostmann.Characters.CharacterEnumerationCount

namespace OAI

/-! # The actual zero set with multiplicity labels

Each copy is a genuine zero together with an integer smaller than its analytic
order. Any bijective numbering of these copies automatically has the correct
multiplicity bound and finite bounded-height ranges.
-/

namespace Ostmann

open Set
open scoped Classical

abbrev CharacterZeroCopy (χ : PrimitiveComplexCharacter) :=
  {p : ℂ × ℕ // p.1 ∈ complexCharacterZeros χ ∧ p.2 < analyticOrderNatAt χ.L p.1}

theorem characterZeroCopy_finite_height (χ : PrimitiveComplexCharacter) (T : ℝ) :
    {c : CharacterZeroCopy χ | |c.val.1.im| ≤ T}.Finite := by
  let V : Set (ℂ × ℕ) := ⋃ z ∈ {z : ℂ | z ∈ complexCharacterZeros χ ∧ |z.im| ≤ T},
    ({z} ×ˢ {n : ℕ | n < analyticOrderNatAt χ.L z})
  have hV : V.Finite := (χ.strip_zeros_finite T).biUnion
    (fun z _ => (finite_singleton z).prod (finite_lt_nat _))
  apply (hV.preimage (fun _ _ _ _ h => Subtype.ext h)).subset
  intro c hc
  exact Set.mem_iUnion.mpr ⟨c.val.1, Set.mem_iUnion.mpr
    ⟨⟨c.property.1, hc⟩, ⟨rfl, c.property.2⟩⟩⟩

noncomputable def characterZeroEnumeration (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) : ComplexZeroEnumeration χ where
  zeros i := (e i).val.1
  in_strip i := ⟨(e i).property.1.1, (e i).property.1.2.1⟩
  actual_zero i := (e i).property.1.2.2
  finite_height T := (characterZeroCopy_finite_height χ T).preimage
    (fun _ _ _ _ h => e.injective h)

theorem characterZeroEnumeration_respectsMultiplicity (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) : (characterZeroEnumeration χ e).RespectsMultiplicity := by
  intro S z
  change (S.filter (fun i => (e i).val.1 = z)).card ≤ analyticOrderNatAt χ.L z
  rw [← Finset.card_range (analyticOrderNatAt χ.L z)]
  apply Finset.card_le_card_of_injOn (fun i => (e i).val.2)
  · intro i hi
    have hzi := (Finset.mem_filter.mp hi).2
    have hbound := (e i).property.2
    rw [hzi] at hbound
    exact Finset.mem_range.mpr hbound
  · intro i hi j hj hindex
    apply e.injective
    apply Subtype.ext
    exact Prod.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) hindex

/-- Every genuine zero and every one of its multiplicity labels occurs once. -/
theorem characterZeroEnumeration_complete (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) (z : ℂ) (hz : z ∈ complexCharacterZeros χ)
    (k : ℕ) (hk : k < analyticOrderNatAt χ.L z) :
    ∃! i : ℕ, (e i).val = (z, k) := by
  let c : CharacterZeroCopy χ := ⟨(z, k), hz, hk⟩
  refine ⟨e.symm c, ?_, ?_⟩
  · simp [c]
  · intro i hi
    apply e.injective
    apply Subtype.ext
    simpa [c] using hi

end Ostmann

end OAI
