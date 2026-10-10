import OAI.GroupTheory.PolycyclicRecognition.Lattices.TwoStepLatticeRealization

namespace OAI

/-! # Finite-index lattice realization for two-step nilpotent groups -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative commutatorElement

theorem commutator_le_center_of_injective {H G : Type*} [Group H] [Group G]
    (f : H →* G) (hf : Function.Injective f) (h2 : commutator G ≤ Subgroup.center G) :
    commutator H ≤ Subgroup.center H := by
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro a _ b _
  apply Subgroup.mem_center_iff.mpr
  intro c
  apply hf
  rw [map_mul, map_mul, map_commutatorElement]
  have hab : ⁅f a, f b⁆ ∈ commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  exact Subgroup.mem_center_iff.mp (h2 hab) (f c)

theorem twoStep_finiteIndex_lattice_realization {G : Type} [Group G] [Group.FG G]
    (h2 : commutator G ≤ Subgroup.center G) :
    ∃ (Γ : Subgroup G), Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  let : IsMulCommutative (G ⧸ Subgroup.center G) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr h2
  let : Group.IsNilpotent G :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (Subgroup.center G)) (by
      rw [QuotientGroup.ker_mk'])
  obtain ⟨Γ, hΓ, htf⟩ :=
    (isPolycyclic_of_finitelyGenerated_nilpotent G).exists_torsionFree_finiteIndex
  let := hΓ
  obtain ⟨S, Λ, hΛ, e⟩ := twoStep_torsionFree_lattice_realization
    (commutator_le_center_of_injective Γ.subtype Subtype.val_injective h2) htf
  exact ⟨Γ, hΓ, S, Λ, hΛ, e⟩

end PolycyclicRecognition

end

end OAI
