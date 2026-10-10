import Mathlib
import OAI.Combinatorics.UniformKServer.PartitionTransport
import OAI.Combinatorics.UniformKServer.CommonAnchorTravel

namespace OAI

                                        
section

/-! Literal metric coupling of the actual consecutive allocated trees. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry BalancedStar
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem actual_rounding_step (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (hdiam : ∀ p q : X,dist p q≤40*A.R)
    (P : Distribution (actualAllocation A D hk z t ω)) :
    ∃ C : Coupling (actualAllocation A D hk z t ω) (actualAllocation A D hk z (t+1) ω) P,
      C.joint.expect (fun st=>stateDistance (anchor A D hk z t ω) (anchor A D hk z (t+1) ω) st.1 st.2)≤
        15840*variation (weight A) (actualAllocation A D hk z t ω) (actualAllocation A D hk z (t+1) ω)+
          anchorTravel A D hk z t ω := by
  obtain ⟨C,hC⟩ := distribution_step (weight A) (fun v=>radius_nonneg A _) (weight_separated A)
    (actualAllocation A D hk z t ω) (actualAllocation A D hk z (t+1) ω)
    (anchor A D hk z t ω) (anchor A D hk z (t+1) ω) 120 (by norm_num)
    (fun u v hu hv hne=>distinct_anchor_cost A D hk z t ω u v hne
      (park_witness A D hk z t ω u hu) (park_witness A D hk z (t+1) ω v hv) hdiam) P
  refine ⟨C,?_⟩
  have hc := common_travel_le A D hk z t ω
  norm_num only [show (120:ℝ)*132=15840 by norm_num] at hC
  linarith

theorem endpoint_anchor (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (hJ : 0<J)
    (hsmall : ∀ p q : X,p≠q → 20*radius A J<dist p q) (p : X) :
    anchor A D hk z t ω ((map A D hk z).toLeaf t ω p)=p := by
  let v := (map A D hk z).toLeaf t ω p
  have hd : depth (shape A k J) v=J := PrefixTree.depth_at _ J (le_refl _)
  have hv : v≠0 := by intro he; rw [he,depth_root] at hd; omega
  have hm : p∈region A D hk z t ω v := mem_filter.mpr ⟨mem_univ _,desc_refl _⟩
  have ha := anchor_distance A D hk z t ω v hv p hm
  rw [hd] at ha
  by_contra hn
  have hh := hsmall p (anchor A D hk z t ω v) (Ne.symm hn)
  linarith

theorem realized_leaf_occupied {n : ℕ} {S : Shape n} (a : Allocation S k)
    (s : State S k) (hs : Rounded a s.value) (v : Vertex n) (hv : TreeLeaves.leaf (S:=S) v)
    (ha : 1≤a.amount v) : ∃ i,s.realization.tuple i=v := by
  have hsum : (∑ i : Children S v,s.value i.val)=0 := sum_eq_zero (fun i _=>(hv i).elim)
  have hx : 1 ≤ s.value v := by
    have hb := (balanced_bounds (hs.2.1 v)).1
    have hf : (1:ℤ)≤⌊a.amount v⌋ := Int.le_floor.mpr (by exact_mod_cast ha)
    omega
  have hp : 0 < intPark S s.value v := by rw [intPark,hsum]; omega
  have he := s.realization.sum (fun w=>if w=v then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true] at he
  by_contra hn
  have he' : (∑ i : Fin k,if s.realization.tuple i=v then (1:ℝ) else 0)=0 :=
    sum_eq_zero (fun i _=>ite_eq_right (fun hi=>hn ⟨i,hi⟩))
  rw [he'] at he
  have : (0:ℝ)<(intPark S s.value v:ℝ) := by exact_mod_cast hp
  linarith

theorem rounded_serves (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (hJ : 0<J)
    (hsmall : ∀ p q : X,p≠q → 20*radius A J<dist p q)
    (s : State (shape A k J) k) (hs : Rounded (actualAllocation A D hk z (t+1) ω) s.value) :
    ∃ i,anchor A D hk z (t+1) ω (s.realization.tuple i)=D.request t ω := by
  obtain ⟨i,hi⟩ := realized_leaf_occupied (actualAllocation A D hk z (t+1) ω) s hs
    ((map A D hk z).toLeaf (t+1) ω (D.request t ω)) ((map A D hk z).leaf _ _ _)
    (TreeCountData.serves D (map A D hk z) (by omega) t ω)
  refine ⟨i,?_⟩
  rw [hi]
  exact endpoint_anchor A D hk z (t+1) ω hJ hsmall _

end UniformKServer.PartitionTree

end


end

end OAI
