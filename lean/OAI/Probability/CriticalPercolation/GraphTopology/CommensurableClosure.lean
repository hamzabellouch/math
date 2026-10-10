import Mathlib

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]

lemma isOpen_of_isClosed_relIndex (K H : Subgroup A) (hK : IsOpen (K:Set A))
    (hH : IsClosed (H:Set A)) (hi : H.relIndex K≠0) : IsOpen (H:Set A) := by
  let J := H.subgroupOf K
  let : J.FiniteIndex := ⟨hi⟩
  have hJ : IsOpen (J:Set K) := J.isOpen_of_isClosed_of_finiteIndex
    (hH.preimage continuous_subtype_val)
  have hI : IsOpen ((J.map K.subtype):Set A) := hK.isOpenMap_subtype_val _ hJ
  exact Subgroup.isOpen_mono (by rintro _ ⟨k,hk,rfl⟩; exact hk) hI

lemma topologicalClosure_open_of_relIndex (K N : Subgroup A) (hK : IsOpen (K:Set A))
    (hi : N.relIndex K≠0) : IsOpen (N.topologicalClosure:Set A) := by
  apply isOpen_of_isClosed_relIndex K N.topologicalClosure hK N.isClosed_topologicalClosure
  exact fun h => hi (Subgroup.relIndex_eq_zero_of_le_left N.le_topologicalClosure h)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
