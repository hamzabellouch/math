import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeAbelianExtension
import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentFiniteIndexLattice
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CharacteristicSemidirectSubgroup

namespace OAI

/-! # Realizing split nilpotent-by-free-abelian groups as virtual Lie lattices -/

noncomputable section
namespace PolycyclicRecognition
variable {H : Type} [Group H] [Group.FG H] [Group.IsNilpotent H]

theorem nilpotent_by_freeAbelian_split_uniform_lattice {n : ℕ}
    (ρ : IntegralLatticeGroup n →* MulAut H) :
    ∃ Γ : Subgroup (H ⋊[ρ] IntegralLatticeGroup n), Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨N, hN, htf⟩ :=
    (isPolycyclic_of_finitelyGenerated_nilpotent H).exists_torsionFree_finiteIndex
  let := hN
  obtain ⟨K, hKN, hKchar, hKi⟩ := exists_characteristic_finiteIndex_le N
  let := hKchar
  let := hKi
  have htK : HasNoNontrivialTorsion K := htf.of_injective (Subgroup.inclusion hKN)
    (Subgroup.inclusion_injective hKN)
  obtain ⟨C⟩ := nilpotent_lattice_coordinates htK
  obtain ⟨Γ, hΓ, S, Λ, hΛ, ⟨e⟩⟩ :=
    C.abelian_extension_finiteIndex_lattice ((MulAut.characteristic K).comp ρ)
  let f := characteristicSemidirectMap K ρ
  have hfi : f.range.FiniteIndex := characteristicSemidirectMap_finiteIndex K ρ
  have hf : Function.Injective f := characteristicSemidirectMap_injective K ρ
  have hΓ' : (Γ.map f).FiniteIndex := ⟨by
    rw [Γ.index_map_of_injective hf]
    exact mul_ne_zero hΓ.index_ne_zero hfi.index_ne_zero⟩
  let eΓ := Γ.equivMapOfInjective f hf
  exact ⟨Γ.map f, hΓ', S, Λ, hΛ, ⟨eΓ.symm.trans e⟩⟩

end PolycyclicRecognition

end

end OAI
