import Mathlib
import OAI.Combinatorics.UniformKServer.PartitionTransport
import OAI.Combinatorics.UniformKServer.CommonAnchorTravel
import OAI.Combinatorics.UniformKServer.PilotFamily

namespace OAI

noncomputable section

/-! Adapted rounded joint laws for the literal partition/allocation process,
with the exact financed movement bound. -/
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry FiniteProbability
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem allocation_causal (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω v : Ω) (he : (D.filtration t).r ω v) :
    actualAllocation A D hk z t ω=actualAllocation A D hk z t v := by
  have heq : (actualAllocation A D hk z t ω).amount=(actualAllocation A D hk z t v).amount := by
    funext u
    exact TreeAllocator.measurable (TreeCountData.data D (map A D hk z)) (by omega) t he u
  cases h₁ : actualAllocation A D hk z t ω
  cases h₂ : actualAllocation A D hk z t v
  simp only [h₁,h₂] at heq
  cases heq
  rfl

theorem anchors_causal (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (t : ℕ) (ω v : Ω) (he : (D.filtration t).r ω v) :
    anchor A D hk z t ω=anchor A D hk z t v := by
  funext u
  unfold anchor
  split_ifs
  · rfl
  · exact A.anchor_measurable D hk ω v t _ he _ _

def roundingChain (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) : ChainInput (shape A k J) k X Ω where
  allocation := actualAllocation A D hk z
  anchors := anchor A D hk z
  filtration := D.filtration
  refines := D.refines
  allocation_causal := allocation_causal A D hk z
  anchors_causal := anchors_causal A D hk z
  weight := weight A
  weight_nonneg := fun v=>radius_nonneg A _
  weight_separated := weight_separated A
  factor := 120
  factor_nonneg := by norm_num
  geometry t ω u v hu hv hne := distinct_anchor_cost A D hk z t ω u v hne
    (park_witness A D hk z t ω u hu) (park_witness A D hk z (t+1) ω v hv) hdiam

theorem roundingChain_cost (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (t : ℕ) (ω : Ω) :
    ((roundingChain A D hk z hdiam).joint t ω).expect
      (fun st=>stateDistance (anchor A D hk z t ω) (anchor A D hk z (t+1) ω) st.1 st.2)≤
      15840*variation (weight A) (actualAllocation A D hk z t ω) (actualAllocation A D hk z (t+1) ω)+
        anchorTravel A D hk z t ω := by
  have h := (roundingChain A D hk z hdiam).cost_bound t ω
  have hc := common_travel_le A D hk z t ω
  change _ ≤ 120*132*variation _ _ _+_ at h
  norm_num only [show (120:ℝ)*132=15840 by norm_num] at h
  exact h.trans (add_le_add (le_refl _) hc)

end UniformKServer.PartitionTree

end

end OAI
