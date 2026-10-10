import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocalSolvableRadical
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SolvableSubgroupFiniteExtension
import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightKernelTorsionBound

namespace OAI

/-! # Virtual solvability for the full locally virtually nilpotent height kernel

The rational dimension and torsion bounds come from the actual FP-infinity
coefficient argument. A characteristic soluble subgroup permits passage
from the kernel to the ambient extension.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]

theorem TypeFPInfinity.heightKernel_virtualSolvable
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    [IsMulCommutative (G ⧸ N)]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let : Countable G := countable_of_group_fg G
  obtain ⟨d, hd⟩ := hG.heightKernel_rationalHomologyDimension M N hQ hN
  have hb := hG.heightKernel_boundedFiniteSubgroupOrders M N hQ hN
  have hlocal : ∀ J : Subgroup N, J.FG → Group.IsVirtuallyNilpotent J := by
    intro J hJ
    exact virtuallyNilpotent_of_mulEquiv
      (J.equivMapOfInjective N.subtype Subtype.val_injective).symm
      (hN (J.map N.subtype) (Subgroup.map_subtype_le J) (fg_subgroup_map hJ N.subtype))
  obtain ⟨R, hRc, hRi, hRs⟩ := locallyVirtuallyNilpotent_characteristic_solvable d
    (hd.subgroup N) (hb.subgroup N) hlocal
  let := hRc
  let := hRi
  let := hRs
  let S := R.map N.subtype
  let : S.Normal := by dsimp [S]; infer_instance
  let e := R.equivMapOfInjective N.subtype Subtype.val_injective
  let : Group.IsSolvable S :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let : (S.subgroupOf N).FiniteIndex := by
    change (S.comap N.subtype).FiniteIndex
    dsimp only [S]
    rw [Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
    infer_instance
  exact virtuallySolvable_of_relative_finiteIndex_solvable S N (Subgroup.map_subtype_le R)

end PolycyclicRecognition

end

end OAI
