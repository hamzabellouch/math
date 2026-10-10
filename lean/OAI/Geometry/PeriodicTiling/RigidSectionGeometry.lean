import OAI.Geometry.PeriodicTiling.ResidueTransversal
import OAI.Geometry.PeriodicTiling.SeparatedCenters
import Mathlib.Tactic.NormNum

namespace OAI

namespace PeriodicTilingThree

theorem rigidSection_rigidDifferences : RigidDifferences 64 rigidSection.Tstar := by
  intro d hbound hdiv
  apply rigidSection_Tstar_difference d
  refine ⟨hbound, ?_⟩
  intro hall
  obtain ⟨i, hi⟩ := hdiv
  exact hi (hall i)

theorem rigidSection_Tstar_subset_T0 : rigidSection.Tstar ⊆ rigidSection.T0 :=
  Finset.erase_subset _ _

theorem rigidSection_Tstar_subset_T1 (w : Lattice 3) :
    rigidSection.Tstar ⊆ rigidSection.T1 w := by
  rw [rigidSection.T1_eq_insert w]
  exact Finset.subset_insert _ _

theorem rigidSection_Tstar_nonempty : rigidSection.Tstar.Nonempty := by
  apply Finset.card_pos.mp
  rw [rigidSection.card_Tstar]
  norm_num

theorem rigidSection_T0_card : rigidSection.T0.card = 64 ^ 3 :=
  rigidSection.card_T0

theorem rigidSection_T1_card (w : Lattice 3) : (rigidSection.T1 w).card = 64 ^ 3 :=
  rigidSection.card_T1 w

end PeriodicTilingThree

end OAI
