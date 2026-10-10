import Mathlib
import OAI.Combinatorics.UniformKServer.ActualRoundedStep
import OAI.Combinatorics.UniformKServer.ActualRoundingChain
import OAI.Combinatorics.UniformKServer.PublicFlow

namespace OAI

noncomputable section

/-! Law-dependent but genuinely online configuration/action flows for the
actual pilot, partition, allocation, anchor, and rounding construction. -/
namespace UniformKServer.HiddenFlow.Data
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype Ω] {k : ℕ}

def transcript (D : Data X Ω k) (t : ℕ) (ω : Ω) : List X :=
  List.ofFn (fun i : Fin t=>D.request i.val ω)

theorem transcript_zero (D : Data X Ω k) (ω : Ω) : D.transcript 0 ω=[] := rfl

theorem transcript_snoc (D : Data X Ω k) (t : ℕ) (ω : Ω) :
    D.transcript (t+1) ω=D.transcript t ω++[D.request t ω] := by
  simp only [transcript,List.ofFn_succ',List.concat_eq_append,Fin.val_castSucc,Fin.val_last]

theorem transcript_length (D : Data X Ω k) (t : ℕ) (ω : Ω) :
    (D.transcript t ω).length=t := by simp only [transcript,List.length_ofFn]

def Public (D : Data X Ω k) : Prop :=
  ∀ t ω v,D.transcript t ω=D.transcript t v → (D.filtration t).r ω v

end UniformKServer.HiddenFlow.Data

namespace UniformKServer.PartitionTree
open Finset FiniteProbability TreeRounding TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}
local instance configEq : DecidableEq (Fin k→X) := fun a b=>Classical.propDecidable (a=b)

def publicInput (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public) :
    PublicInput (roundingChain A D hk z hdiam) where
  default := ω₀
  request := D.request
  trace := D.transcript
  trace_zero := D.transcript_zero
  trace_snoc := D.transcript_snoc
  trace_length := D.transcript_length
  reflects := hpublic

def componentFlow (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) : RealFlow.Data X (Fin k→X) (Fin k) :=
  (publicInput A D hk z hdiam ω₀ hpublic).flow (by omega) s

theorem component_valid (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) : RealFlow.Valid (componentFlow A D hk z hdiam ω₀ hpublic s)
      (fun c r j=>Function.update c j r) PublicInput.allowed s N :=
  (publicInput A D hk z hdiam ω₀ hpublic).flow_valid (by omega) s N

theorem component_bound (A : ActualPartitions.Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (z : Tape A k N J) (hdiam : ∀ p q : X,dist p q≤40*A.R) (ω₀ : Ω) (hpublic : D.Public)
    (s : Fin k→X) (hJ : 0<J) (hsmall : ∀ p q : X,p≠q → 20*radius A J<dist p q) (ω : Ω) :
    RealFlow.flowCost (componentFlow A D hk z hdiam ω₀ hpublic s) (fun c r j=>dist (c j) r)
      [] (D.transcript N ω)≤
      15840*(∑ t∈range N,variation (weight A) (actualAllocation A D hk z t ω)
        (actualAllocation A D hk z (t+1) ω))+
      (∑ t∈range N,anchorTravel A D hk z t ω)+k*(40*A.R) := by
  have h := (publicInput A D hk z hdiam ω₀ hpublic).flow_bound (by omega) s N ω (40*A.R) hdiam
    (fun t _ v hv=>rounded_serves A D hk z t ω hJ hsmall v hv)
  have hsum := sum_le_sum (s:=range N) (fun t _=>roundingChain_cost A D hk z hdiam t ω)
  simp only [sum_add_distrib,←mul_sum] at hsum
  change _≤(∑ t∈range N,((roundingChain A D hk z hdiam).joint t ω).expect
    (fun st=>stateDistance (anchor A D hk z t ω) (anchor A D hk z (t+1) ω) st.1 st.2))+_ at h
  change RealFlow.flowCost (componentFlow A D hk z hdiam ω₀ hpublic s) (fun c r j=>dist (c j) r) []
    (D.transcript N ω)≤_ at h
  linarith only [h,hsum]

end UniformKServer.PartitionTree

end

end OAI
