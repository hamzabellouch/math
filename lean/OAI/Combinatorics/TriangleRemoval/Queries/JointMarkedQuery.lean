import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.TracedGridQueryAddress
import OAI.Combinatorics.TriangleRemoval.Spectral.CheckMarkedTrace

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section MarkedTrace
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def jointMarkedQuery (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) :
    ℕ → ℕ → QueryCall ι τ → ExposureTree τ (Fin N) (Bool × Bool × List (QueryCall ι τ))
  | 0, _, c => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H c.focus c.parent).toList)
      (fun _ => .done (true,true,[c]))
  | d+1, k, c => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H c.focus c.parent).toList)
      (fun values => ExposureTree.mapOutput (fun z => (z.1,z.2.1,c :: z.2.2))
        (ExposureTree.checkMarkedTrace
          ((values.mergeSort (fun a b => a.2.val ≤ b.2.val)).map
            (fun p => (required (p.1 :: c.address), if p.2.val < k then
              jointMarkedQuery H N required d p.2.val
                ⟨p.1 :: c.address,(H p.1.2).erase p.1.1,some p.1.2⟩
              else .done (false,false,[]))))))

theorem jointMarkedQuery_marked (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) (d k : ℕ) (c : QueryCall ι τ) :
    ExposureTree.mapOutput (fun z => (z.1,z.2.1)) (jointMarkedQuery H N required d k c) =
      markedGridQueryDepth H N required d k c.address c.focus c.parent := by
  induction d generalizing k c with
  | zero => simp only [jointMarkedQuery,markedGridQueryDepth,
      ExposureTree.mapOutput_bind,ExposureTree.mapOutput_done]
  | succ d ih =>
    simp only [jointMarkedQuery,markedGridQueryDepth,ExposureTree.mapOutput_bind,
      ExposureTree.mapOutput_comp]
    congr 1
    funext values
    rw [show (fun x : Bool × Bool × List (QueryCall ι τ) => (x.1,x.2.1)) ∘
        (fun z : Bool × Bool × List (QueryCall ι τ) => (z.1,z.2.1,c :: z.2.2)) =
        (fun z : Bool × Bool × List (QueryCall ι τ) => (z.1,z.2.1)) from rfl,
      ExposureTree.checkMarkedTrace_marked,List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    dsimp only [Function.comp_def]
    congr 1
    split
    · exact ih _ _
    · rfl

theorem jointMarkedQuery_trace (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) (d k : ℕ) (c : QueryCall ι τ) :
    ExposureTree.mapOutput (fun z => (z.1,z.2.2)) (jointMarkedQuery H N required d k c) =
      tracedGridQuery H N d k c := by
  induction d generalizing k c with
  | zero => simp only [jointMarkedQuery,tracedGridQuery,
      ExposureTree.mapOutput_bind,ExposureTree.mapOutput_done]
  | succ d ih =>
    simp only [jointMarkedQuery,tracedGridQuery,ExposureTree.mapOutput_bind,
      ExposureTree.mapOutput_comp]
    congr 1
    funext values
    rw [show (fun x : Bool × Bool × List (QueryCall ι τ) => (x.1,x.2.2)) ∘
        (fun z : Bool × Bool × List (QueryCall ι τ) => (z.1,z.2.1,c :: z.2.2)) =
        (fun z : Bool × List (QueryCall ι τ) => (z.1,c :: z.2)) ∘
          (fun z : Bool × Bool × List (QueryCall ι τ) => (z.1,z.2.2)) from rfl,
      ← ExposureTree.mapOutput_comp,ExposureTree.checkMarkedTrace_trace,List.map_map]
    congr 2
    apply List.map_congr_left
    intro p _
    dsimp only [Function.comp_def]
    split
    · exact ih _ _
    · rfl

theorem jointMarkedQuery_address (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) (d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : Bool × Bool × List (QueryCall ι τ)}
    (hz : z ∈ (ExposureTree.fresh ν (jointMarkedQuery H N required d k c)).support) :
    ∀ a ∈ z.2.2, c.address <:+ a.address := by
  have ht : (z.1,z.2.2) ∈ (ExposureTree.fresh ν (tracedGridQuery H N d k c)).support := by
    rw [← jointMarkedQuery_trace H N required d k c,ExposureTree.fresh_mapOutput]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨z,hz,rfl⟩
  rw [← ExposureTree.freshLog_outcome] at ht
  obtain ⟨x,hx,hxe⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
  have hh := tracedGridQuery_address H N d k c ν hx
  rw [hxe] at hh
  exact hh

end MarkedTrace
end SharpTerminalLeave

end

end OAI
