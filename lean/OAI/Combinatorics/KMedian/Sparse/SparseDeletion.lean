import Mathlib
import OAI.Combinatorics.KMedian.Reduction.DeletionGeometry

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance sparseDeletionPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

noncomputable def denseBall (O : Finset (Fin I.n)) (i : Fin I.n) : Finset (Fin I.n) :=
  I.clients.filter (fun j => dist j i < nearest I i O/3)

def Sparse (F O : Finset (Fin I.n)) (ρ : ℝ) : Prop :=
  ∀ i ∈ F, nearest I i O*(denseBall (I:=I) O i).card ≤ ρ*cost I O

namespace Serving
variable {U O F : Finset (Fin I.n)} {ρ δ : ℝ}

theorem sparse_deletion (D : Serving (I:=I) U) (hUF : U ⊆ F) (hsp : Sparse (I:=I) F O ρ)
    (hδ : 0 ≤ δ) (t : ↥U) (hbad : δ*D.radius t ≤ nearest I t O) :
    δ*(cost I (U.erase t.val)-cost I U) ≤ ρ*cost I O+3*D.groupCost t := by
  classical
  let N : Finset ↥I.clients := (D.group t).filter (fun (j : ↥I.clients) => nearest I j U < δ*D.radius t/3)
  have hNsub : N.image (fun j => j.val) ⊆ denseBall (I:=I) O t := by
    intro j hj
    obtain ⟨j',hj',rfl⟩ := mem_image.mp hj
    obtain ⟨hg,hn⟩ := mem_filter.mp hj'
    have hassign : D.assignment j'=t := (mem_filter.mp hg).2
    have hdist : dist j'.val t.val=nearest I j' U := by
      simpa only [hassign] using D.assignment_cost j'
    apply mem_filter.mpr
    refine ⟨j'.property,?_⟩
    rw [hdist]
    exact hn.trans_le (div_le_div_of_nonneg_right hbad (by norm_num))
  have hcard : N.card ≤ (denseBall (I:=I) O t).card := by
    rw [← card_image_of_injective N (f:=fun j : ↥I.clients => j.val) Subtype.val_injective]
    exact card_le_card hNsub
  have hnear : (N.card:ℝ)*(δ*D.radius t) ≤ ρ*cost I O := by
    calc
      _ ≤ N.card*nearest I t O := mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg _)
      _ ≤ (denseBall (I:=I) O t).card*nearest I t O :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (I.nearest_nonneg t O)
      _ ≤ _ := by simpa only [mul_comm] using hsp t (hUF t.property)
  have hp : ∀ j ∈ D.group t, δ*D.radius t ≤
      (if nearest I j U < δ*D.radius t/3 then δ*D.radius t else 0)+3*nearest I j U := by
    intro j _
    split_ifs with hj
    · have hn := I.nearest_nonneg j U
      linarith only [hn]
    · have hn := le_of_not_gt hj
      linarith only [hn]
  have hsum := sum_le_sum hp
  have heleft : (∑ _j ∈ D.group t, δ*D.radius t)=(D.group t).card*(δ*D.radius t) := by
    simp only [sum_const,nsmul_eq_mul]
  have heright : (∑ j ∈ D.group t,
      ((if nearest I j U < δ*D.radius t/3 then δ*D.radius t else 0)+3*nearest I j U)) =
      N.card*(δ*D.radius t)+3*D.groupCost t := by
    rw [sum_add_distrib,← mul_sum,← sum_filter]
    simp only [N,groupCost,sum_const,nsmul_eq_mul]
  rw [heleft,heright] at hsum
  have hdel := mul_le_mul_of_nonneg_left (D.deletion_bound t) hδ
  calc
    _ ≤ δ*((D.group t).card*D.radius t) := hdel
    _ = (D.group t).card*(δ*D.radius t) := by ring
    _ ≤ N.card*(δ*D.radius t)+3*D.groupCost t := hsum
    _ ≤ _ := add_le_add hnear le_rfl

theorem bad_count_charge (D : Serving (I:=I) U) (hUF : U ⊆ F)
    (hsp : Sparse (I:=I) F O ρ) (hδ : 0 ≤ δ) (B : ℝ)
    (hstuck : ∀ t : ↥U, B ≤ cost I (U.erase t.val)-cost I U) :
    let H := univ.filter (fun t : ↥U => δ*D.radius t ≤ nearest I t O)
    (H.card:ℝ)*(δ*B-ρ*cost I O) ≤ 3*cost I U := by
  classical
  dsimp only
  let H := univ.filter (fun t : ↥U => δ*D.radius t ≤ nearest I t O)
  have hpoint : ∀ t ∈ H, δ*B-ρ*cost I O ≤ 3*D.groupCost t := by
    intro t ht
    have hc := D.sparse_deletion hUF hsp hδ t (mem_filter.mp ht).2
    have hd := mul_le_mul_of_nonneg_left (hstuck t) hδ
    linarith only [hc,hd]
  have hsum := sum_le_sum hpoint
  simp only [sum_const,nsmul_eq_mul,← mul_sum] at hsum
  have hcost : (∑ t ∈ H, D.groupCost t) ≤ cost I U := by
    rw [← D.groupCost_total]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun t _ _ => D.groupCost_nonneg t)
  exact hsum.trans (mul_le_mul_of_nonneg_left hcost (by norm_num))

end Serving
end MetricKMedian.Reduction
end
end

end OAI
