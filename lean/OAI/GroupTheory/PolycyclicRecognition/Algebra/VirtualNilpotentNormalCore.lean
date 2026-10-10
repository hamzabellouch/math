import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Nilpotent

namespace OAI

/-! # A torsion-free nilpotent normal core -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.FG G]

theorem exists_normal_torsionFree_nilpotent_finiteIndex
    (hG : Group.IsVirtuallyNilpotent G) :
    ∃ F : Subgroup G, F.Normal ∧ F.FiniteIndex ∧ Group.IsNilpotent F ∧ HasNoNontrivialTorsion F := by
  obtain ⟨N, hN, hNi⟩ := hG
  let := hN
  let := hNi
  obtain ⟨U, hUi, hU⟩ :=
    (isPolycyclic_of_finitelyGenerated_nilpotent N).exists_torsionFree_finiteIndex
  let := hUi
  let P := U.map N.subtype
  let e := U.equivMapOfInjective N.subtype Subtype.val_injective
  let : P.FiniteIndex := ⟨by
    change (U.map N.subtype).index ≠ 0
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hUi.index_ne_zero hNi.index_ne_zero⟩
  let f : P.normalCore →* U := e.symm.toMonoidHom.comp (Subgroup.inclusion P.normalCore_le)
  have hf : Function.Injective f := e.symm.injective.comp (Subgroup.inclusion_injective _)
  have hnil : Group.IsNilpotent P.normalCore :=
    Subgroup.isNilpotent_of_ker_le_center f (by rw [f.ker_eq_bot hf]; exact bot_le)
  exact ⟨P.normalCore, inferInstance, inferInstance, hnil, hU.of_injective f hf⟩

end PolycyclicRecognition

end

end OAI
