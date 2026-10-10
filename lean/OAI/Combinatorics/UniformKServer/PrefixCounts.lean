import Mathlib
import OAI.Combinatorics.UniformKServer.PrefixMovement

namespace OAI

                                   
section

/-! Literal subtree-count costs are controlled by labeled coordinate-key edits,
without a tree-height or cardinality factor. -/
noncomputable section
namespace UniformKServer.PrefixMovement
open Finset TreeRounding TreeAncestry TreeLeaves PrefixTree
open scoped Classical
variable {A : Type*} [Fintype A] {J k : ℕ}

theorem diff_triangle {T : Type*} (a b c : T) : diff a c≤diff a b+diff b c := by
  unfold diff
  split_ifs <;> simp_all

theorem count_cast (p : Fin k→Fin J→A) (v : Vertex (size A J)) :
    (TreeLeaves.count (S:=shape A J) (fun a => endpoint (p a)) v : ℝ)=∑ a,mark v (p a) := by
  simp only [TreeLeaves.count,Nat.cast_sum,TreeLeaves.indicator,mark]
  apply sum_congr rfl
  intro a _
  split_ifs <;> norm_num

theorem count_variation (p q : Fin k→Fin J→A) (r : ℕ→ℝ)
    (hr : ∀ i, 0≤r i) (hdec : ∀ i, 2*r (i+1)≤r i) :
    (∑ v : Vertex (size A J), edgeWeight r (depth (shape A J) v)*
      |(TreeLeaves.count (S:=shape A J) (fun a => endpoint (p a)) v : ℝ)-
       TreeLeaves.count (S:=shape A J) (fun a => endpoint (q a)) v|)≤
    4*∑ a,∑ i : Fin J,r i.val*diff (p a i) (q a i) := by
  have hw (v : Vertex (size A J)) : 0≤edgeWeight r (depth (shape A J) v) := by
    unfold edgeWeight; split_ifs; exact le_rfl; exact hr _
  calc
    _ ≤ ∑ v : Vertex (size A J),edgeWeight r (depth (shape A J) v)*
      ∑ a,|mark v (p a)-mark v (q a)| := by
        apply sum_le_sum
        intro v _
        rw [count_cast,count_cast,←sum_sub_distrib]
        exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (hw v)
    _ = ∑ a,∑ v : Vertex (size A J),edgeWeight r (depth (shape A J) v)*
      |mark v (p a)-mark v (q a)| := by simp only [mul_sum]; rw [sum_comm]
    _ ≤ ∑ a,4*∑ i : Fin J,r i.val*diff (p a i) (q a i) :=
      sum_le_sum fun a _ => spatial_variation (p a) (q a) r hr hdec
    _ = _ := (mul_sum _ _ _).symm

theorem count_split (p q u : Fin k→Fin J→A) (r : ℕ→ℝ)
    (hr : ∀ i, 0≤r i) (hdec : ∀ i, 2*r (i+1)≤r i) :
    (∑ v : Vertex (size A J), edgeWeight r (depth (shape A J) v)*
      |(TreeLeaves.count (S:=shape A J) (fun a => endpoint (p a)) v : ℝ)-
       TreeLeaves.count (S:=shape A J) (fun a => endpoint (q a)) v|)≤
    4*(∑ a,∑ i : Fin J,r i.val*diff (p a i) (u a i))+
    4*(∑ a,∑ i : Fin J,r i.val*diff (u a i) (q a i)) := by
  have h := count_variation p q r hr hdec
  have hh := sum_le_sum (s:=univ) (fun a _ => sum_le_sum (s:=univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (diff_triangle (p a i) (u a i) (q a i)) (hr i.val)))
  simp only [mul_add,sum_add_distrib] at hh
  linarith

end UniformKServer.PrefixMovement

end


end

end OAI
