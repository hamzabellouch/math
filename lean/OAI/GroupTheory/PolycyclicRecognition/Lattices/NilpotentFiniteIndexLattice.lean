import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeInduction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree

namespace OAI

/-! # The virtually nilpotent case of solvable lattice realization -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {G : Type} [Group G] [Group.FG G]

theorem nilpotent_finiteIndex_uniform_lattice [Group.IsNilpotent G] :
    ∃ Γ : Subgroup G, Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨Γ, hΓ, htf⟩ :=
    (isPolycyclic_of_finitelyGenerated_nilpotent G).exists_torsionFree_finiteIndex
  let := hΓ
  obtain ⟨S, Λ, hΛ, e⟩ := torsionFree_nilpotent_uniform_lattice htf
  exact ⟨Γ, hΓ, S, Λ, hΛ, e⟩

theorem virtuallyNilpotent_uniform_lattice (hG : Group.IsVirtuallyNilpotent G) :
    ∃ Γ : Subgroup G, Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨N, hn, hi⟩ := hG
  let := hn
  let := hi
  obtain ⟨K, hK, S, Λ, hΛ, ⟨e⟩⟩ := nilpotent_finiteIndex_uniform_lattice (G := N)
  let Γ := K.map N.subtype
  have hΓ : Γ.FiniteIndex := ⟨by
    change (K.map N.subtype).index ≠ 0
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hK.index_ne_zero hi.index_ne_zero⟩
  let eK : K ≃* Γ := K.equivMapOfInjective N.subtype N.subtype_injective
  exact ⟨Γ, hΓ, S, Λ, hΛ, ⟨eK.symm.trans e⟩⟩

theorem virtuallyNilpotent_dekimpe_realization (hG : Group.IsVirtuallyNilpotent G) :
    ∃ Γ : Subgroup G, Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        DiscreteTopology Λ ∧ CompactSpace (S.carrier ⧸ Λ) ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨Γ, hΓ, S, Λ, hΛ, e⟩ := virtuallyNilpotent_uniform_lattice hG
  let : IsTopologicalGroup S.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  exact ⟨Γ, hΓ, S, Λ, hΛ.1, hΛ.compactSpace_quotient, e⟩

end PolycyclicRecognition

end

end OAI
