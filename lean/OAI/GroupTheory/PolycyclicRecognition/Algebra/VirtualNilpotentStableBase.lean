import OAI.GroupTheory.PolycyclicRecognition.Algebra.EndomorphismInvariantFiniteIndex
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPolyZ

namespace OAI

/-! # A stable nilpotent base for an ascending extension -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.FG G]

theorem exists_endomorphismInvariant_nilpotent_finiteIndex
    (hG : Group.IsVirtuallyNilpotent G) :
    ∃ D : Subgroup G, D.FiniteIndex ∧ Group.IsNilpotent D ∧
      HasNoNontrivialTorsion D ∧ (∀ f : G →* G, D.map f ≤ D) ∧
      HasFiniteIntegralCohomologicalDimension D := by
  obtain ⟨N, hNnil, hNindex⟩ := hG
  let := hNnil
  let := hNindex
  have hNpoly : IsPolycyclic N := isPolycyclic_of_finitelyGenerated_nilpotent N
  obtain ⟨K, hKindex, hKtf⟩ := hNpoly.exists_torsionFree_finiteIndex
  let := hKindex
  let H : Subgroup G := K.map N.subtype
  have hHindex : H.FiniteIndex := ⟨by
    change (K.map N.subtype).index ≠ 0
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hKindex.index_ne_zero hNindex.index_ne_zero⟩
  let := hHindex
  let e : K ≃* H := K.equivMapOfInjective N.subtype N.subtype_injective
  have hHnil : Group.IsNilpotent H := Group.nilpotent_of_mulEquiv e
  let := hHnil
  have hHtf := hKtf.of_injective e.symm.toMonoidHom e.symm.injective
  obtain ⟨D, hDH, hDindex, hstable⟩ := exists_endomorphismInvariant_finiteIndex_le H
  let := hDindex
  have hDnil : Group.IsNilpotent D :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDH)
  let := hDnil
  have hDtf := hHtf.of_injective (Subgroup.inclusion hDH) (Subgroup.inclusion_injective hDH)
  obtain ⟨d, hd⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree hDtf
  exact ⟨D, hDindex, hDnil, hDtf, hstable, hd.finiteCohomologicalDimension D⟩

end PolycyclicRecognition

end

end OAI
