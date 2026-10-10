import OAI.GroupTheory.PolycyclicRecognition.Lattices.VectorLatticeModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree

namespace OAI

/-! # Solvable lattice realization for virtually abelian groups

The finite-index torsion-free subgroup is an integral lattice. Its embedding
into the actual additive vector Lie group has a compact fundamental cover.
This discharges the virtually abelian case of Dekimpe's realization input.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative Manifold
variable {P : Type} [Group P] [Group.FG P]

theorem solvable_lattice_realization_of_finiteIndex_abelian
    (H : Subgroup P) [H.FiniteIndex] [IsMulCommutative H] :
    ∃ Γ : Subgroup P, Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  have hH : IsPolycyclic H := isPolycyclic_of_finitelyGenerated_commGroup H
  obtain ⟨K, hKi, hKtf⟩ := hH.exists_torsionFree_finiteIndex
  let := hKi
  obtain ⟨n, ⟨e⟩⟩ := exists_integralLattice_equiv hKtf
  let Γ := K.map H.subtype
  have hΓi : Γ.FiniteIndex := ⟨by
    change (K.map H.subtype).index ≠ 0
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hKi.index_ne_zero (inferInstance : H.FiniteIndex).index_ne_zero⟩
  let eK : K ≃* Γ := K.equivMapOfInjective H.subtype H.subtype_injective
  exact ⟨Γ, hΓi, vectorSolvableLieModel n, standardVectorLattice n,
    standardVectorLattice_uniform n,
    ⟨(eK.symm.trans e.symm).trans (standardVectorLatticeEquiv n)⟩⟩

theorem dekimpe_realization_of_finiteIndex_abelian
    (H : Subgroup P) [H.FiniteIndex] [IsMulCommutative H] :
    ∃ Γ : Subgroup P, Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        DiscreteTopology Λ ∧ CompactSpace (S.carrier ⧸ Λ) ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨Γ, hΓ, S, Λ, hΛ, e⟩ := solvable_lattice_realization_of_finiteIndex_abelian H
  let : IsTopologicalGroup S.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  exact ⟨Γ, hΓ, S, Λ, hΛ.1, hΛ.compactSpace_quotient, e⟩

end PolycyclicRecognition

end

end OAI
