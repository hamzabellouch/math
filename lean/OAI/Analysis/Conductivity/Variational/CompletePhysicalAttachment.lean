import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalJoin
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedAssembly

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def attachedPhysicalJet (s a κ : Fin 3 → ℝ) (p : centralEnergySpace s)
    (i : Fin 3) (x : R3) : JetFiber :=
  Fin.cases
    (physicalJet (fullAttachedEndValue s (centralT s 0 p) (a 0) centralThickness
      (κ 0) (WithLp.ofLp x))
      (fullAttachedEndGradient s (centralT s 0 p) (a 0) centralThickness
        (κ 0) (WithLp.ofLp x)))
    (fun k => physicalJet
      (fullAttachedEndValue s (centralT s k.succ p) (a k.succ) (-centralThickness)
        (κ k.succ) ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)))
      (fun j => sourceScale⁻¹*fullAttachedEndGradient s (centralT s k.succ p)
        (a k.succ) (-centralThickness) (κ k.succ)
        ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) (childAxis j))) i

theorem complete_physical_attachment (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (a κ : Fin 3 → ℝ) (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)
    (p : centralEnergySpace s) :
    ∃ w : H1,w∈H10 ∧
      H1JetOn w centralPhysical (centralFullJetCLM s p.val) ∧
      ∀ i : Fin 3,H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i) := by
  let zi := centralInteriorCompletion s (centralJoinPartition_smooth 0)
    centralJoinPartition_interior_compact centralJoinPartition_interior_support
    (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy)) p
  let zp := parentCompletionJoin s hs ha₀ (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
    centralJoinPartition_parent_support p
  let zc (k : Fin 2) := physicalChildCompletionJoin s hs (ha k) k (centralJoinChildCutoff_smooth k)
    (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
    (centralJoinChildCutoff_support k) p
  obtain ⟨dp,hdp,hds,hdpZ,hdpE⟩ := parentAttachedCorrection_supported s hs ha₀ (κ 0) p
  have hdcEx (k : Fin 2) := physicalChildAttachedCorrection_supported s hs (ha k) k (κ k.succ) p
  choose dc hdc hdcZ hdcE using hdcEx
  let w : H1 := zi+(zp+dp)+((zc 0+dc 0)+(zc 1+dc 1))
  have hw : w∈H10 := H10.add_mem
    (H10.add_mem (centralInteriorCompletion_mem_H10 s _ _ _ _ p)
      (H10.add_mem (parentCompletionJoin_mem_H10 s hs ha₀ _ _ _ _ p) hdp))
    (H10.add_mem
      (H10.add_mem (physicalChildCompletionJoin_mem_H10 s hs (ha 0) 0 _ _ _ _ p) (hdc 0))
      (H10.add_mem (physicalChildCompletionJoin_mem_H10 s hs (ha 1) 1 _ _ _ _ p) (hdc 1)))
  have hpC : H1JetOn dp centralPhysical (fun _ => 0) :=
    (H1JetOn.zero_of_weak (D:={y | centralThickness≤ sourceCollarTime y}) hdpZ).mono
      (fun y hy => ((centralPhysical_time_iff y).mp hy).1)
  have hcC (k : Fin 2) : H1JetOn (dc k) centralPhysical (fun _ => 0) :=
    (H1JetOn.zero_of_weak (D:={y | sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y)≤-centralThickness}) (hdcZ k)).mono
      (fun y hy => ((centralPhysical_time_iff y).mp hy).2 k)
  have hpO (k : Fin 2) : H1JetOn (zp+dp) (physicalEndRegion k.succ) (fun _ => 0) := by
    apply H1JetOn.add_zero
    · exact H1JetOn.zero_of_weak (parent_join_zero_on_children s hs ha₀ p k)
    · apply (H1JetOn.zero_of_weak (D:={y | centralThickness≤ sourceCollarTime y}) hdpZ).mono
      intro y hy
      exact (show centralThickness≤2*centralThickness by norm_num [centralThickness]).trans
        (physicalChildEnd_parent_time k hy)
  have hcO (k : Fin 2) (i : Fin 3) (hik : i≠k.succ) :
      H1JetOn (zc k+dc k) (physicalEndRegion i) (fun _ => 0) := by
    apply H1JetOn.add_zero
    · exact H1JetOn.zero_of_weak (physical_child_join_zero_on_other_ends s hs (ha k) p k i hik)
    · apply (H1JetOn.zero_of_weak (D:={y | sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y)≤-centralThickness}) (hdcZ k)).mono
      intro y hy
      exact (physicalOtherEnd_child_time k i hik hy).le.trans
        (by norm_num [centralThickness])
  have hiO (i : Fin 3) : H1JetOn zi (physicalEndRegion i) (fun _ => 0) :=
    H1JetOn.zero_of_weak (central_interior_join_zero_on_ends s p i)
  have hpE : H1JetOn (zp+dp) (physicalEndRegion 0) (attachedPhysicalJet s a κ p 0) :=
    H1JetOn.of_weak hdpE
  have hcE (k : Fin 2) : H1JetOn (zc k+dc k) (physicalEndRegion k.succ)
      (attachedPhysicalJet s a κ p k.succ) := H1JetOn.of_weak (hdcE k)
  refine ⟨w,hw,?_,?_⟩
  · have he : w=centralNeighborhoodCompletion s hs ha₀ ha p+(dp+(dc 0+dc 1)) := by
      simp only [w,centralNeighborhoodCompletion,Fin.sum_univ_two,add_apply]
      change zi+(zp+dp)+((zc 0+dc 0)+(zc 1+dc 1))=zi+zp+(zc 0+zc 1)+(dp+(dc 0+dc 1))
      abel
    rw [he]
    have hc : H1JetOn (centralNeighborhoodCompletion s hs ha₀ ha p) centralPhysical
        (centralFullJetCLM s p.val) := centralNeighborhoodCompletion_central_ae s hs ha₀ ha p
    exact hc.add_zero (hpC.add_zero ((hcC 0).add_zero (hcC 1)))
  · intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact ((hiO 0).zero_add hpE).add_zero
        ((hcO 0 0 (by decide)).add_zero (hcO 1 0 (by decide)))
    · fin_cases k
      · exact ((hiO 1).add_zero (hpO 0)).zero_add
          ((hcE 0).add_zero (hcO 1 1 (by decide)))
      · exact ((hiO 2).add_zero (hpO 1)).zero_add
          ((hcO 0 2 (by decide)).zero_add (hcE 1))

end ScalarConductivity
end

end

end OAI
