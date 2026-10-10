import Mathlib
import OAI.Combinatorics.UniformKServer.ActualPartitions
import OAI.Combinatorics.UniformKServer.PartitionCausal
import OAI.Combinatorics.UniformKServer.PrefixTree
import OAI.Combinatorics.UniformKServer.TreePosteriorRegions

namespace OAI

                                    
section

/-! The actual fixed full-prefix tree associated with the literal partition.
The alphabet, tree and independent tape domains are instance-dependent but
law- and horizon-independent (apart from a finite tape restriction). -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

def height (k : ℕ) : ℕ := DyadicTiers.last (Real.log k)+1
abbrev Label (X : Type) [Fintype X] (C : ℝ) (k : ℕ) :=
  LevelMap.HeavySlot X ⊕ ((i : Fin (height k)) × TierLabeledKeys.Slot X (TierParameters.cutoff C (DyadicTiers.value i.val))) ⊕ X

abbrev LevelTape (A : ActualPartitions.Config X) (k N j : ℕ) :=
  (Fin N→HeavyRadius.Sample (X:=X) (GeometricMass.radius A.R A.q j)) ×
    (∀ i : Fin (height k), TierLifetimes.Tape N × (Fin N→TierRadius.Sample (X:=X)
      (Real.log (1+(TierParameters.cutoff A.C (DyadicTiers.value i.val):ℝ)^2)) (GeometricMass.radius A.R A.q j)))
abbrev Tape (A : ActualPartitions.Config X) (k N J : ℕ) := ∀ j : Fin J, LevelTape A k N j.val
abbrev size (A : ActualPartitions.Config X) (k J : ℕ) := PrefixTree.size (Label X A.C k) J
def shape (A : ActualPartitions.Config X) (k J : ℕ) : Shape (size A k J) := PrefixTree.shape (Label X A.C k) J

def word (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (p : X) : Fin J→Label X A.C k := fun j =>
  ((A.input (N:=N) (J:=J) D hk ω).level j.val).data.key
    ((A.input (N:=N) (J:=J) D hk ω).level j.val).order (z j) t p

def map (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) : TreeCountData.Map D (shape A k J) where
  toLeaf t ω p := PrefixTree.endpoint (word A D hk z t ω p)
  leaf t ω p := PrefixTree.endpoint_leaf _
  causal t ω v he := by
    funext p
    apply congrArg PrefixTree.endpoint
    funext j
    exact A.key_measurable D hk ω v t j.val he (z j) p

def region (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) : Finset X :=
  TreePosteriorRegions.region D (map A D hk z) t ω v

theorem root_region (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) : region A D hk z t ω 0=univ := by
  ext p
  simp only [region,TreePosteriorRegions.region,mem_filter,mem_univ,true_and]
  exact iff_true_intro (TreeLeaves.root_descends _)

theorem nested (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (u v : Vertex (size A k J))
    (huv : descends (shape A k J) u v) : region A D hk z t ω v⊆region A D hk z t ω u := by
  intro p hp
  simp only [region,TreePosteriorRegions.region,mem_filter,mem_univ,true_and] at hp ⊢
  exact huv.trans hp

theorem region_prefix (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) (p : X)
    (hp : p∈region A D hk z t ω v) :
    v=PrefixTree.atLevel (word A D hk z t ω p) (depth (shape A k J) v) (PrefixTree.depth_bound v) :=
  PrefixTree.desc_endpoint _ v (mem_filter.mp hp).2

theorem same_prefix (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω : Ω) (v : Vertex (size A k J)) (p q : X)
    (hp : p∈region A D hk z t ω v) (hq : q∈region A D hk z t ω v)
    (j : Fin J) (hj : j.val<depth (shape A k J) v) :
    word A D hk z t ω p j=word A D hk z t ω q j := by
  have he := (region_prefix A D hk z t ω v p hp).symm.trans (region_prefix A D hk z t ω v q hq)
  have hw := congrArg (PrefixTree.chart (Label X A.C k) J) he
  simp only [PrefixTree.atLevel,Equiv.apply_symm_apply] at hw
  have hb : depth (shape A k J) v≤J := PrefixTree.depth_bound v
  have hf : (fun i : Fin (depth (shape A k J) v) => word A D hk z t ω p ⟨i.val,by have := i.isLt; omega⟩)=
      (fun i : Fin (depth (shape A k J) v) => word A D hk z t ω q ⟨i.val,by have := i.isLt; omega⟩) :=
    eq_of_heq (Sigma.mk.inj_iff.mp hw).2
  exact congrFun hf ⟨j.val,hj⟩

end UniformKServer.PartitionTree

end


end

end OAI
