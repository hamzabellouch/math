import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

namespace OAI

noncomputable section
namespace SevenEighths.HeckePrimitiveSupremum
open HeckeFamily HeckeZeroSupremum

def primitiveZeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), FiniteFourier.IsPrimitiveOnIdeals χ.residue ∧
    (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧
    LFunction χ s = 0 ∧ s.re = x}

def primitiveSetWithSentinel : Set ℝ := insert (1 / 2) primitiveZeroRealParts

theorem primitiveSet_subset : primitiveSetWithSentinel ⊆ zeroSetWithSentinel := by
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact Set.mem_insert _ _
  · obtain ⟨χ, s, _, hhalf, _, hpole, hz, rfl⟩ := hx
    exact Set.mem_insert_of_mem _ ⟨χ, s, by linarith, hpole, hz, rfl⟩

theorem primitiveSet_bddAbove : BddAbove primitiveSetWithSentinel :=
  zeroSet_bddAbove.mono primitiveSet_subset

theorem primitiveSet_nonempty : primitiveSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem beta_eq_primitive_supremum : beta = sSup primitiveSetWithSentinel := by
  apply le_antisymm
  · apply csSup_le zeroSet_nonempty
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact le_csSup primitiveSet_bddAbove (Set.mem_insert _ _)
    · by_cases hhalf : (1 / 2 : ℝ) ≤ x
      · obtain ⟨χ, s, hpos, hpole, hz, rfl⟩ := hx
        obtain ⟨ψ, hp, hpoleψ, hzψ⟩ :=
          HeckeFiniteDeletion.exists_primitive_zero χ hpos hpole hz
        apply le_csSup primitiveSet_bddAbove
        exact Set.mem_insert_of_mem _ ⟨ψ, s, hp, hhalf,
          zeroRealParts_le_one ⟨χ, s, hpos, hpole, hz, rfl⟩, hpoleψ, hzψ, rfl⟩
      · exact (le_of_not_ge hhalf).trans
          (le_csSup primitiveSet_bddAbove (Set.mem_insert _ _))
  · exact csSup_le_csSup zeroSet_bddAbove primitiveSet_nonempty primitiveSet_subset

theorem exists_primitive_zero_near_beta {ε : ℝ} (hε : 0 < ε)
    (hsmall : (1 / 2 : ℝ) ≤ beta - ε) :
    ∃ (χ : Character) (s : ℂ), FiniteFourier.IsPrimitiveOnIdeals χ.residue ∧
      (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧
      LFunction χ s = 0 ∧ beta - ε < s.re := by
  rw [beta_eq_primitive_supremum] at hsmall ⊢
  obtain ⟨x, hx, hlt⟩ := Supremum.exists_gt_supremum_sub_of_insert
    primitiveSet_bddAbove hε hsmall
  obtain ⟨χ, s, hp, hhalf, hone, hpole, hz, rfl⟩ := hx
  exact ⟨χ, s, hp, hhalf, hone, hpole, hz, hlt⟩

end SevenEighths.HeckePrimitiveSupremum

end

end OAI
