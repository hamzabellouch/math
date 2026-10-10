import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentTorsionSubgroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicKernelQuotient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianQuotientFiniteDimension

namespace OAI

/-! # The finite-dimensional endgame modulo nilpotent torsion

Finite rational kernel rank gives a characteristic locally finite normal
subgroup whose removal leaves finite virtual integral cohomological dimension.
Neither the finiteness of this torsion subgroup nor the rank implication from
ambient FP-infinity is asserted here.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]

def normalNilpotentTorsionSubgroup : Subgroup G :=
  (nilpotentTorsionSubgroup (G := N)).map N.subtype

instance normalNilpotentTorsionSubgroup_normal : (normalNilpotentTorsionSubgroup N).Normal := by
  dsimp [normalNilpotentTorsionSubgroup]
  infer_instance

theorem nilpotent_abelianization_mod_torsion_virtual_finite_dimension
    [Group.FG G] [IsMulCommutative (G ⧸ N)]
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization N))] :
    ∃ V : Subgroup (G ⧸ normalNilpotentTorsionSubgroup N),
      V.FiniteIndex ∧ Group.IsSolvable V ∧ HasFiniteIntegralCohomologicalDimension V := by
  let : Group.IsSolvable G := Group.isSolvable_of_subgroup_quotient N
  let : Countable G := countable_of_group_fg G
  let T := nilpotentTorsionSubgroup (G := N)
  let f := finiteIndexKernelQuotientMap N T
  let e : (N ⧸ T) ≃* f.ker := characteristicKernelQuotientEquiv N T
  obtain ⟨d, hd⟩ := nilpotentTorsionQuotient_finiteDimension_of_finite_abelianization (G := N)
  let := hd
  have hker : HasFiniteIntegralCohomologicalDimension f.ker :=
    ⟨d, cohomologicalDimension_le_of_equiv e d⟩
  exact abelian_quotient_virtual_finite_dimension f
    (finiteIndexKernelQuotientMap_surjective N T) hker

end PolycyclicRecognition

end

end OAI
