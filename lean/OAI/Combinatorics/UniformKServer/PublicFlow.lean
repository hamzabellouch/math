import Mathlib
import OAI.Combinatorics.UniformKServer.PublicRounding
import OAI.Combinatorics.UniformKServer.RealFlowMixture

namespace OAI

noncomputable section

/-! A rounded private process gives a literal nonnegative configuration/action
flow with legal zero-marginal rows and the same expected movement. -/
namespace UniformKServer.TreeRounding.PublicInput
open Finset FiniteProbability
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X Ω : Type} [Fintype X] [MetricSpace X]
local instance configEq : DecidableEq (Fin k→X) := fun a b=>Classical.propDecidable (a=b)
variable {D : ChainInput S k X Ω} (O : PublicInput D)

def allowed (c : Fin k→X) (r : X) (j : Fin k) : Prop := (∃ i,c i=r) → c j=r

def flow (hk : 0<k) (s : Fin k→X) : RealFlow.Data X (Fin k→X) (Fin k) :=
  (O.input.model hk).flow (O.initial s)

theorem flow_valid (hk : 0<k) (s : Fin k→X) (H : ℕ) :
    RealFlow.Valid (O.flow hk s) (fun c r j=>Function.update c j r) allowed s H := by
  apply MarkovFlow.Model.valid
  · exact LazyMarkov.Input.initial_marginal _ s
  · intro w r c v
    exact O.input.legal hk w r c v

theorem flow_trace (hk : 0<k) (s : Fin k→X) (t : ℕ) (ω : Ω) :
    RealFlow.flowCost (O.flow hk s) (fun c r j=>dist (c j) r) [] (O.trace t ω)=
      ∑ u∈range t,O.charge hk s u ω := by
  induction t with
  | zero => simp only [O.trace_zero,RealFlow.flowCost,sum_range_zero]
  | succ t ih =>
    rw [O.trace_snoc,RealFlow.flowCost_append,ih,sum_range_succ]
    congr 1
    simp only [RealFlow.flowCost,List.nil_append,add_zero]
    rfl

theorem flow_bound (hk : 0<k) (s : Fin k→X) (N : ℕ) (ω : Ω) (Δ : ℝ)
    (hdiam : ∀ x y : X,dist x y≤Δ)
    (hcover : ∀ t<N,∀ v : State S k,Rounded (D.allocation (t+1) ω) v.value →
      ∃ i,D.anchors (t+1) ω (v.realization.tuple i)=O.request t ω) :
    RealFlow.flowCost (O.flow hk s) (fun c r j=>dist (c j) r) [] (O.trace N ω)≤
      (∑ t∈range N,O.transport t ω)+k*Δ := by
  rw [O.flow_trace]
  exact O.total_charge hk s N ω Δ hdiam hcover

end UniformKServer.TreeRounding.PublicInput

end

end OAI
