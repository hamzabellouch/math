import Mathlib
import OAI.Combinatorics.UniformKServer.PartitionGeometry

namespace OAI

                                       
section

/-! Literal last-key representatives and validity from actual posterior domination. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def lastWord {B : Type} (base : B) (w : PrefixTree.Word B J) : B :=
  if h : 0<w.1.val then w.2 ⟨w.1.val-1,by omega⟩ else base

def lastLabel (A : ActualPartitions.Config X) (v : Vertex (size A k J)) : Label X A.C k :=
  lastWord (Sum.inr (Sum.inr A.base)) (PrefixTree.chart (Label X A.C k) J v)

omit [MetricSpace X] in
theorem last_at (A : ActualPartitions.Config X) (p : Fin J→Label X A.C k)
    (d : ℕ) (hd : d≤J) (hp : 0<d) :
    lastLabel A (PrefixTree.atLevel p d hd)=p ⟨d-1,by omega⟩ := by
  calc
    _ = lastWord (Sum.inr (Sum.inr A.base)) (PrefixTree.wordPrefix p d hd) :=
      congrArg (lastWord (Sum.inr (Sum.inr A.base)))
        ((PrefixTree.chart (Label X A.C k) J).apply_symm_apply _)
    _ = _ := by
      dsimp only [lastWord,PrefixTree.wordPrefix]
      split_ifs
      rfl

theorem last_region (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) (hv : v≠0)
    (p : X) (hp : p∈region A D hk z t ω v) :
    lastLabel A v=word A D hk z t ω p
      ⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v hv; omega⟩ := by
  have hd := depth_positive A v hv
  have he := region_prefix A D hk z t ω v p hp
  calc
    lastLabel A v=lastLabel A (PrefixTree.atLevel (word A D hk z t ω p)
      (depth (shape A k J) v) (PrefixTree.depth_bound v)) := congrArg (lastLabel A) he
    _ = _ := last_at A _ _ _ hd

def anchor (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) : X :=
  if hv : v=0 then A.base else
    let j : Fin J := ⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v hv; omega⟩
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.anchor (z j) t (lastLabel A v)

theorem anchor_distance (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) (hv : v≠0)
    (p : X) (hp : p∈region A D hk z t ω v) :
    dist p (anchor A D hk z t ω v)≤20*radius A (depth (shape A k J) v) := by
  let j : Fin J := ⟨depth (shape A k J) v-1,by have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v; have := depth_positive A v hv; omega⟩
  have he := last_region A D hk z t ω v hv p hp
  rw [anchor,dite_eq_right hv]
  change dist p (((A.input (N:=N) (J:=J) D hk ω).level j.val).data.anchor (z j) t (lastLabel A v))≤_
  erw [he]
  have hh := LevelMap.Data.covers ((A.input (N:=N) (J:=J) D hk ω).level j.val).data
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p
  change dist p _≤20*(A.R*A.q^(j.val+1)) at hh
  have hj : j.val+1=depth (shape A k J) v := by dsimp [j]; have := depth_positive A v hv; omega
  simpa only [word,hj,radius] using hh

theorem witness (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J))
    (hp : 0<TreeAllocator.amount (TreeCountData.data D (map A D hk z)) (by omega) t ω v) :
    (region A D hk z t ω v).Nonempty := by
  by_contra he
  have hz := Finset.not_nonempty_iff_eq_empty.mp he
  have hd := TreePosteriorRegions.domination D (map A D hk z) (by omega) t ω v
  change _≤132*ParkCapacity.mass (HiddenFlow.current D t ω) (region A D hk z t ω v) at hd
  rw [hz,ParkCapacity.mass,sum_empty,mul_zero] at hd
  linarith

end UniformKServer.PartitionTree

end


end

end OAI
