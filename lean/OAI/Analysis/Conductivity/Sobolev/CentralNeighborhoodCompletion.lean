import Mathlib
import OAI.Analysis.Conductivity.Sobolev.ChildH10Transport
import OAI.Analysis.Conductivity.Branching.CentralJoinCover

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : Fin 3 → ℝ} (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)

def centralNeighborhoodCompletion : centralEnergySpace s →L[ℝ] H1 :=
  centralInteriorCompletion s (centralJoinPartition_smooth 0)
    centralJoinPartition_interior_compact centralJoinPartition_interior_support
    (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy))+
  parentCompletionJoin s hs ha₀ (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
    centralJoinPartition_parent_support+
  ∑ k : Fin 2,physicalChildCompletionJoin s hs (ha k) k (centralJoinChildCutoff_smooth k)
    (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k) (centralJoinChildCutoff_support k)

lemma centralNeighborhoodCompletion_mem_H10 (u : centralEnergySpace s) :
    centralNeighborhoodCompletion s hs ha₀ ha u∈H10 := by
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact centralInteriorCompletion_mem_H10 s _ _ _ _ u
    · exact parentCompletionJoin_mem_H10 s hs ha₀ _ _ _ _ u
  · rw [Fin.sum_univ_two]
    exact H10.add_mem
      (physicalChildCompletionJoin_mem_H10 s hs (ha 0) 0 _ _ _ _ u)
      (physicalChildCompletionJoin_mem_H10 s hs (ha 1) 1 _ _ _ _ u)

end ScalarConductivity

end

end OAI
