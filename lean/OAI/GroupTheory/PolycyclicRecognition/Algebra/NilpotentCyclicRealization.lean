import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentCyclicFiniteIndexLattice
import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentFiniteIndexLattice
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicCyclicSubgroup

namespace OAI

/-! # Unconditional lattice realization for finitely generated nilpotent-by-cyclic groups -/

noncomputable section
namespace PolycyclicRecognition
variable {H : Type} [Group H] [Group.FG H] [Group.IsNilpotent H]

theorem nilpotent_cyclic_finiteIndex_uniform_lattice (a : MulAut H) :
    ∃ Γ : Subgroup (H ⋊[integerPowerAction a] Multiplicative ℤ), Γ.FiniteIndex ∧
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
  obtain ⟨Γ, hΓ, S, Λ, hΛ, ⟨e⟩⟩ := C.cyclic_finiteIndex_lattice (MulAut.characteristic K a)
  let f := characteristicCyclicMap K a
  have hfi : f.range.FiniteIndex := characteristicCyclicMap_finiteIndex K a
  have hf : Function.Injective f := characteristicCyclicMap_injective K a
  have hΓ' : (Γ.map f).FiniteIndex := ⟨by
    rw [Γ.index_map_of_injective hf]
    exact mul_ne_zero hΓ.index_ne_zero hfi.index_ne_zero⟩
  let eΓ := Γ.equivMapOfInjective f hf
  exact ⟨Γ.map f, hΓ', S, Λ, hΛ, ⟨eΓ.symm.trans e⟩⟩

end PolycyclicRecognition

end

end OAI
