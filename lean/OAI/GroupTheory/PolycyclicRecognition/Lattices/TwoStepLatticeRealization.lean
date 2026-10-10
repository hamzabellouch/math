import OAI.GroupTheory.PolycyclicRecognition.Algebra.FreeAbelianCentralExtension
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentCentralRoots
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree

namespace OAI

/-! # Lattice realization for groups of nilpotency class at most two -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]

theorem twoStep_torsionFree_lattice_realization
    (h2 : commutator G ≤ Subgroup.center G) (htf : HasNoNontrivialTorsion G) :
    ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
      IsUniformLattice Λ ∧ Nonempty (G ≃* Λ) := by
  let Z := Subgroup.center G
  let : IsMulCommutative (G ⧸ Z) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr h2
  let : Group.IsNilpotent G :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' Z) (by
      rw [QuotientGroup.ker_mk'])
  let : Group.FG Z := CriticalPercolation.nilpotent_subgroup_fg G Z
  obtain ⟨d, ⟨eQ⟩⟩ := exists_integralLattice_equiv
    (nilpotent_centerQuotient_torsionFree htf)
  let q : G →* Multiplicative (Fin d → ℤ) :=
    eQ.symm.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hq : Function.Surjective q := eQ.symm.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : q.ker = Z := by
    ext g
    change eQ.symm ((QuotientGroup.mk' Z) g) = 1 ↔ g ∈ Z
    rw [← map_one eQ.symm, eQ.symm.injective.eq_iff]
    exact QuotientGroup.eq_one_iff g
  let : Group.FG q.ker := hker.symm ▸ (inferInstance : Group.FG Z)
  let : IsMulCommutative q.ker := hker.symm ▸ (inferInstance : IsMulCommutative Z)
  have hktf : HasNoNontrivialTorsion q.ker :=
    htf.of_injective q.ker.subtype Subtype.val_injective
  obtain ⟨e, ⟨eZ⟩⟩ := exists_integralLattice_equiv hktf
  exact freeAbelianCentralExtension_realization q hq (by rw [hker]) eZ

end PolycyclicRecognition

end

end OAI
