import OAI.GroupTheory.PolycyclicRecognition.Algebra.Solvable
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PoincareDualityBase

namespace OAI

/-! # Solvable finite extensions of polycyclic groups

Take the normal core of a polycyclic finite-index subgroup. Its quotient is
finite and solvable, and thus has a cyclic series. The extension construction
then gives a cyclic series for the original group.
-/

namespace PolycyclicRecognition

variable {G : Type} [Group G]

theorem isPolycyclic_of_finite_solvable [Finite G] [Group.IsSolvable G] : IsPolycyclic G :=
  isPolycyclic_of_solvable_subgroups_fg (fun _ => inferInstance)

theorem IsVirtuallyPolycyclic.polycyclic_of_solvable [Group.IsSolvable G]
    (hG : IsVirtuallyPolycyclic G) : IsPolycyclic G := by
  obtain ⟨H, hindex, hH⟩ := hG
  let := hindex
  let N := H.normalCore
  have hN : IsPolycyclic N := hH.of_injective
    (Subgroup.inclusion H.normalCore_le) (Subgroup.inclusion_injective _)
  exact isPolycyclic_of_normal_subgroup N hN isPolycyclic_of_finite_solvable

theorem IsIntegralPoincareDualityGroup.polycyclic_of_virtuallyNilpotent
    [Group.IsSolvable G] {n : ℕ} (hG : IsIntegralPoincareDualityGroup G n)
    (hnil : Group.IsVirtuallyNilpotent G) : IsPolycyclic G := by
  let := hG.1.fg
  exact (isVirtuallyPolycyclic_of_finitelyGenerated_virtuallyNilpotent G hnil).polycyclic_of_solvable

end PolycyclicRecognition

end OAI
