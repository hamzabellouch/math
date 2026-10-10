import Mathlib
import OAI.Combinatorics.KMedian.Process.BatchProposalProgram
import OAI.Combinatorics.KMedian.Process.CopyNextProgram

namespace OAI


                                                  
section
namespace MetricKMedian.RationalPhysicalKernel.UpdateProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList
local instance {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A

structure Context extends CopyGraphProgram.Input where
  β : ℚ
  p : ℚ
  φ : ℚ
  hp : 0≤p
  hφ : 0≤φ
  hupper : (1+φ)*p≤1

structure Input where
  ctx : Context
  G : ctx.A → Finset ctx.A

abbrev Input.proposal (x : Input) : RationalBatchData.ProposalProgram.Input (fun c : Context => ↥c.A) where
  ctx := x.ctx
  n := x.ctx.A.card
  enum := ordinal x.ctx.A
  G := x.G
  Δ := x.ctx.Δ
  g := x.ctx.g
  b := x.ctx.β
  p := x.ctx.p
  φ := x.ctx.φ
  hp := x.ctx.hp
  hφ := x.ctx.hφ
  hupper := x.ctx.hupper

abbrev Raw := (ℕ × Row) × RationalBatchData.GraphData.Raw
def Input.raw (x : Input) : Raw := ((x.ctx.Δ,CopyList.view x.ctx.A),x.proposal.raw)
abbrev Input.encode (x : Input) := enc x.raw

def finish (x : Raw × Data Row) : Data Row :=
  (x.2.1,x.2.2.map (fun Z => CopyNext.transition (x.1.1,((RationalBatchData.GraphData.prepare x.1.2).2,Z))))
@[fun_prop] theorem finish_poly : Poly finish := by
  unfold finish
  apply pair
  · fun_prop
  · apply list_map <;> fun_prop

abbrev Input.update (x : Input) (Z) := RationalBatchData.transition x.ctx.A x.G
  (RationalBatchData.heavySet (RationalBatchData.graphMass x.G x.ctx.g) x.ctx.β) Z

def Input.law (x : Input) := x.proposal.law.map x.update

def Input.result (x : Input) : Data Row :=
  ((x.law.law.denominator,List.ofFn x.law.law.numerator),x.law.states.toList.map CopyList.view)

 theorem result_map (x : Input) : x.result=(x.proposal.result.1,
    x.proposal.law.states.toList.map (fun Z => CopyList.view (x.update Z))) := by
  unfold Input.result Input.law
  change (x.proposal.result.1,(Vector.map x.update x.proposal.law.states).toList.map CopyList.view)=_
  erw [Vector.toList_map,List.map_map]
  rfl

 theorem finish_input (x : Input) : finish (x.raw,x.proposal.result)=x.result := by
  rw [result_map]
  apply Prod.ext
  · rfl
  · change (x.proposal.law.states.toList.map (fun Z => setView (Z.map x.proposal.enumActions.symm.toEmbedding))).map
      (fun Z => CopyNext.transition (x.raw.1,((RationalBatchData.GraphData.prepare x.raw.2).2,Z))) = _
    rw [List.map_map]
    apply List.map_congr_left
    intro Z _
    change CopyNext.transition ((x.ctx.Δ,view x.ctx.A),
      ((RationalBatchData.GraphData.prepare (((x.ctx.g,x.ctx.β),(x.ctx.Δ,(x.ctx.p,x.ctx.φ))),
        RationalBatchData.Ordinal.graphView (ordinal x.ctx.A) x.G)).2,
        setView (Z.map x.proposal.enumActions.symm.toEmbedding)))=_
    rw [RationalBatchData.Ordinal.prepare_graph]
    exact CopyNext.transition_view x.ctx.A x.G _ Z

noncomputable def proposalProgram : PolyProgram Input.encode
    RationalBatchData.ProposalProgram.Input.encode Input.proposal :=
  (snd enc enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)

noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.er) Input.result := by
  let ctx : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (ctx.fanout (proposalProgram.comp RationalBatchData.ProposalProgram.program) |>.comp finish_poly.program).congr _ finish_input
end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
