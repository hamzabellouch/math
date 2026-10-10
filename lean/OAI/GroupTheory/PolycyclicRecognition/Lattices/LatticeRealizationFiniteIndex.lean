import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentExtensionRealization
import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeInduction

namespace OAI

/-! # Finite-index transport and integral-quotient realization -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem uniform_lattice_realization_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (hH : ∃ K : Subgroup H, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ)) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  obtain ⟨K, hK, S, Λ, hΛ, ⟨e⟩⟩ := hH
  have hi : (K.map H.subtype).FiniteIndex := ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hK.index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))⟩
  let eK := K.equivMapOfInjective H.subtype H.subtype_injective
  exact ⟨K.map H.subtype, hi, S, Λ, hΛ, ⟨eK.symm.trans e⟩⟩

theorem nilpotent_integer_extension_realization {n : ℕ}
    (q : G →* IntegralLatticeGroup n) (hq : Function.Surjective q)
    [Group.FG q.ker] [Group.IsNilpotent q.ker] (ht : HasNoNontrivialTorsion q.ker) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  let E : GroupExtension q.ker G (IntegralLatticeGroup n) :=
    { inl := q.ker.subtype
      rightHom := q
      inl_injective := Subtype.val_injective
      range_inl_eq_ker_rightHom := Subgroup.range_subtype _
      rightHom_surjective := hq }
  obtain ⟨C⟩ := nilpotent_lattice_coordinates ht
  exact C.extension_realization E (normalizedExtensionSection E) (normalizedExtensionSection_one E)

end PolycyclicRecognition

end

end OAI
