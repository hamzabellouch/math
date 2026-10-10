import OAI.GroupTheory.PolycyclicRecognition.Algebra.Solvable
import OAI.Probability.CriticalPercolation.Nilpotent.NilpotentSubgroupFG
import Mathlib.GroupTheory.Schreier

namespace OAI

/-!
# The nilpotent conclusion in recognition

Finitely generated nilpotent groups are polycyclic. Consequently a finitely
generated virtually nilpotent group is virtually polycyclic, by finite
generation of the finite-index nilpotent subgroup.
-/

namespace PolycyclicRecognition

variable (G : Type*) [Group G] [Group.FG G]

/-- Finite generation and nilpotence yield an actual finite cyclic subnormal series. -/
theorem isPolycyclic_of_finitelyGenerated_nilpotent [Group.IsNilpotent G] :
    IsPolycyclic G := by
  apply isPolycyclic_of_solvable_subgroups_fg
  exact CriticalPercolation.nilpotent_subgroup_fg G

/-- Schreier finite generation applies to the nilpotent finite-index subgroup. -/
theorem isVirtuallyPolycyclic_of_finitelyGenerated_virtuallyNilpotent
    (hG : Group.IsVirtuallyNilpotent G) : IsVirtuallyPolycyclic G := by
  obtain ⟨N, hnil, hindex⟩ := hG
  let := hnil
  let := hindex
  exact ⟨N, hindex, isPolycyclic_of_finitelyGenerated_nilpotent N⟩

end PolycyclicRecognition

end OAI
