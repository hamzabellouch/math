import Mathlib
import OAI.Probability.SKBarriers.Locking.FourBlockTent
import OAI.Probability.SKBarriers.Locking.NarrowTentBound
import OAI.Probability.SKBarriers.Hierarchy.WeightedPrefixBound

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

abbrev fourBlockCommon (κ : ℝ) (b l : List (ℝ × ℝ)) := zeroWeightChain b++constantWeightChain κ l
abbrev fourBlockFuture (κ : ℝ) (j k : List (ℝ × ℝ)) := constantWeightChain κ j++zeroWeightChain k

theorem fourBlockQuadratic_tent_le (κ η : ℝ) (b l j k t : List (ℝ × ℝ))
    (hm : ∀ p∈(b++l)++(j++k)++t,p.1∈Icc (0:ℝ) 1)
    (hs : ((b++l)++(j++k)++t).Pairwise (fun p q => p.1≤q.1))
    (hmean : 0≤weightedMean (fourBlockFuture η j k))
    {d B : ℝ} (hd : 0<d) (hB : 0≤B) (hκ : κ*d=1)
    (hl : rawVariance l=B*d) (hj : rawVariance j=B*d) :
    narrowBaseQuadratic (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k) t≤
      narrowVariance (fourBlockCommon κ b l) (fourBlockFuture η j k) (fourBlockFuture (-κ) j k)*
        narrowSusceptibility (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
      2*weightedMean (fourBlockFuture η j k)*B*narrowJointMoment (fourBlockCommon κ b l) (fourBlockFuture (-κ) j k) t+
      6*(weightedAbsCross (fourBlockFuture η j k))^2+
      2*weightedMean (fourBlockFuture η j k)*B*scalarTentAtomMass (fourBlockTent κ b l j k).length
        (fun i => ((fourBlockTent κ b l j k).get i).1) (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k)+
      (B*scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
        (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k))^2+
      B^2*scalarTentAtomMass (fourBlockTent κ b l j k).length (fun i => ((fourBlockTent κ b l j k).get i).1)
        (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k) := by
  let c := fourBlockCommon κ b l
  let v := fourBlockFuture η j k
  let w := fourBlockFuture (-κ) j k
  have hc : weightedUnderlying c=b++l := by simp [c,fourBlockCommon]
  have hv : weightedUnderlying v=j++k := by simp [v,fourBlockFuture]
  have hw : weightedUnderlying w=j++k := by simp [w,fourBlockFuture]
  have hcw : weightedUnderlying (c++w)=(b++l)++(j++k) := by rw [weightedUnderlying_append,hc,hw]
  have hmcw : ∀ p∈c++w,p.1∈Icc (0:ℝ) 1 := by
    apply (weighted_mass_iff _ (P:=fun x => x∈Icc (0:ℝ) 1)).mpr
    rw [hcw]
    intro p hp; exact hm p (List.mem_append_left _ hp)
  have hscw : (c++w).Pairwise (fun p q => p.1≤q.1) := by
    apply (weighted_sorted_iff _).mpr
    rw [hcw]
    exact (List.pairwise_append.mp hs).1
  have hmv : ∀ p∈v,p.1∈Icc (0:ℝ) 1 := by
    apply (weighted_mass_iff _ (P:=fun x => x∈Icc (0:ℝ) 1)).mpr
    rw [hv]
    intro p hp; exact hm p (List.mem_append_left _ (List.mem_append_right _ hp))
  have hsv : v.Pairwise (fun p q => p.1≤q.1) := by
    apply (weighted_sorted_iff _).mpr
    rw [hv]
    exact (List.pairwise_append.mp (List.pairwise_append.mp hs).1).2.1
  have hR : 0≤weightedAbsCross v := by
    unfold weightedAbsCross
    apply List.sum_nonneg
    intro x hx; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx; positivity
  have he : (⟨c.length,by simp only [List.length_append]; omega⟩ : Fin ((c++w).length+1))=
      fourBlockMiddle κ b l j k := by
    apply Fin.ext
    simp [c,fourBlockCommon,zeroWeightChain,constantWeightChain]
  apply narrowBaseQuadratic_tent_le c v w t (hv.trans hw.symm) hmcw hscw
    (fun p hp => hm p (List.mem_append_right _ hp)) (List.pairwise_append.mp hs).2.1 hmv hsv hmean
    (fourBlockLeft κ b l j k) (fourBlockRight κ b l j k)
  · rw [he]; change b.length≤b.length+l.length; omega
  · rw [he]; change b.length+l.length≤b.length+l.length+j.length; omega
  · exact hd
  · exact hB
  · exact hR
  · rw [he,fourBlockTent_middle_variance,fourBlockTent_left_variance,hl]; ring
  · rw [he,fourBlockTent_middle_variance,fourBlockTent_right_variance,hj]; ring
  · rw [he]; exact fourBlockTent_vector (ne_of_gt hd) hκ b l j k
  · exact weightedList_field_bound v

end SK.Analytic

end
end

end OAI
