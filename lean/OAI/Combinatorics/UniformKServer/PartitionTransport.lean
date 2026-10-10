import Mathlib
import OAI.Combinatorics.UniformKServer.LevelAnchorContinuity

namespace OAI

                                         
section

/-! Metric realization between occupied vertices in consecutive literal maps.
Intermediate nonexistent prefixes are never used as validity witnesses. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance ixPT (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairPT : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)

theorem supported_anchor_step (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J))
    (p q : X) (hp : p∈region A D hk z t ω v) (hq : q∈region A D hk z (t+1) ω v) :
    dist (anchor A D hk z t ω v) (anchor A D hk z (t+1) ω v)≤40*radius A (depth (shape A k J) v) := by
  by_cases hv : v=0
  · subst v
    change dist A.base A.base≤40*radius A (depth (shape A k J) 0)
    rw [dist_self]
    exact mul_nonneg (by norm_num) (radius_nonneg A _)
  let j : Fin J := ⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v hv; omega⟩
  have ho := last_region A D hk z t ω v hv p hp
  have hn := last_region A D hk z (t+1) ω v hv q hq
  have h := LevelMap.Data.supported_distance ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p q (lastLabel A v) ho.symm hn.symm
  have hj : j.val+1=depth (shape A k J) v := by dsimp [j]; have := depth_positive A v hv; omega
  change dist _ _≤40*(A.R*A.q^(j.val+1)) at h
  simpa only [anchor,dite_eq_right hv,radius,hj] using h

theorem distinct_anchor_cost (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (u v : Vertex (size A k J)) (hne : u≠v)
    (hu : (region A D hk z t ω u).Nonempty) (hv : (region A D hk z (t+1) ω v).Nonempty)
    (hdiam : ∀ p q : X,dist p q≤40*A.R) :
    dist (anchor A D hk z t ω u) (anchor A D hk z (t+1) ω v)≤
      120*pathCost (S:=shape A k J) (weight A) u v := by
  obtain ⟨p,c,hpu,hpv,hc,hdep,hcut⟩ := separating_edge (S:=shape A k J) u v hne
  have hpedge := edge_le_path (weight A) (fun c=>radius_nonneg A _) u v c hc hcut
  have hed : depth (shape A k J) ((shape A k J).parent c)=depth (shape A k J) p := by
    rw [depth_child c hc] at hdep
    omega
  change radius A (depth (shape A k J) ((shape A k J).parent c))≤_ at hpedge
  rw [hed] at hpedge
  by_cases hp : p=0
  · subst p
    have hd := hdiam (anchor A D hk z t ω u) (anchor A D hk z (t+1) ω v)
    rw [depth_root,radius,pow_zero,mul_one] at hpedge
    nlinarith [A.R_pos]
  · obtain ⟨a,ha⟩ := hu
    obtain ⟨b,hb⟩ := hv
    have hap := nested A D hk z t ω p u hpu ha
    have hbp := nested A D hk z (t+1) ω p v hpv hb
    have hu0 : u≠0 := by intro he; subst u; have := desc_depth hpu; rw [depth_root] at this; have := depth_positive A p hp; omega
    have hv0 : v≠0 := by intro he; subst v; have := desc_depth hpv; rw [depth_root] at this; have := depth_positive A p hp; omega
    have hau := anchor_distance A D hk z t ω u hu0 a ha
    have hapd := anchor_distance A D hk z t ω p hp a hap
    have hbpd := anchor_distance A D hk z (t+1) ω p hp b hbp
    have hbv := anchor_distance A D hk z (t+1) ω v hv0 b hb
    have hpp := supported_anchor_step A D hk z t ω p a b hap hbp
    have hru := radius_antitone A (desc_depth hpu)
    have hrv := radius_antitone A (desc_depth hpv)
    have h₁ := dist_triangle (anchor A D hk z t ω u) a (anchor A D hk z t ω p)
    have h₂ := dist_triangle (anchor A D hk z t ω u) (anchor A D hk z t ω p) (anchor A D hk z (t+1) ω p)
    have h₃ := dist_triangle (anchor A D hk z t ω u) (anchor A D hk z (t+1) ω p) b
    have h₄ := dist_triangle (anchor A D hk z t ω u) b (anchor A D hk z (t+1) ω v)
    rw [dist_comm (anchor A D hk z t ω u) a] at h₁
    rw [dist_comm (anchor A D hk z (t+1) ω p) b] at h₃
    linarith

end UniformKServer.PartitionTree

end


end

end OAI
