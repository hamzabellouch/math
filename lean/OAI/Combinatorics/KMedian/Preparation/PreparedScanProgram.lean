import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListExtras
import OAI.Combinatorics.KMedian.Preparation.RationalPreparedScan
import OAI.Combinatorics.KMedian.Programs.OriginalMaskProgram
import OAI.Combinatorics.KMedian.Process.RoundCountsProgram

namespace OAI


                                           
section
namespace MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
variable {τ : ℝ} (q : RationalParameters τ)
structure Input where
  f : ℕ
  h : ℕ
  j : ℕ
  df : Fin h → Fin h → ℚ
  dc : Fin j → Fin h → ℚ
  orig : Fin f → Fin h
  ns : List (Fin f → ℕ)
  budget : ℚ
abbrev Raw := (List Unit × List ℕ) × ((List (List ℚ) × List (List ℚ)) × (List (List ℕ) × ℚ))
def Input.raw (x : Input) : Raw := ((List.replicate x.h (),List.ofFn (fun i => (x.orig i).val)),
  ((List.ofFn (fun i => List.ofFn (x.df i)),List.ofFn (fun c => List.ofFn (x.dc c))),
  (x.ns.map List.ofFn,x.budget)))
abbrev Input.encode (x : Input) := enc x.raw

def Input.item (x : Input) (n : Fin x.f → ℕ) : RoundCountsProgram.Input :=
  ⟨x.f,x.j,(fun a b => x.df (x.orig a) (x.orig b)),(fun c a => x.dc c (x.orig a)),n⟩
def Input.items (x : Input) := x.ns.map x.item

def prepare (x : Raw) : List RoundCountsProgram.Raw := x.2.2.1.map (fun ns =>
  (x.1.2.map (fun _ => ()),((MaskProgram.pullbackMatrix (x.2.1.1,x.1.2),
    x.2.1.2.map (fun ds => MaskProgram.pullback (ds,x.1.2))),ns)))
@[fun_prop] theorem prepare_poly : Poly prepare := by
  unfold prepare
  apply list_map
  · have hd : Poly (fun x : Raw × List ℕ => x.1.2.1.2.map (fun ds => MaskProgram.pullback (ds,x.1.1.2))) := by
      apply list_map <;> fun_prop
    have hu : Poly (fun x : Raw × List ℕ => x.1.1.2.map (fun _ => ())) := by apply list_map <;> fun_prop
    fun_prop
  · fun_prop
 theorem prepare_input (x : Input) : prepare x.raw=x.items.map RoundCountsProgram.Input.raw := by
  simp only [prepare,Input.raw,List.map_ofFn,Function.comp_def,MaskProgram.pullbackMatrix_view,
    MaskProgram.pullback_view,List.map_map,Input.items]
  apply List.map_congr_left
  intro n _
  simp only [Input.item,RoundCountsProgram.Input.raw]
  congr 1
  simp

def dummy : RoundCountsProgram.Input := ⟨0,0,Fin.elim0,Fin.elim0,Fin.elim0⟩
noncomputable def itemsProgram : PolyProgram Input.encode (encodeList RoundCountsProgram.Input.encode) Input.items :=
  prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    change encodeList enc (prepare x.raw)=_
    rw [prepare_input,encodeList_map]
    rfl)

def Input.candidates (x : Input) := q.countCandidates x.df x.dc x.orig x.ns

def images (x : Raw × List Table) : Table := x.2.flatten.map (fun O => MaskProgram.imageRaw (x.1.1,O))
@[fun_prop] theorem images_poly : Poly images := by
  unfold images
  apply list_map
  · fun_prop
  · exact comp (⟨listFlatten (enc : Row → List Bool) []⟩ : Poly (List.flatten : List Table → Table)) (by fun_prop)
 theorem images_input (x : Input) : images (x.raw,x.items.map (RoundCountsProgram.Input.result q))=
    (x.candidates q).map setView := by
  simp only [images,Input.items,List.map_map,Function.comp_def,RoundCountsProgram.Input.result,
    Input.item,Input.raw]
  rw [List.map_flatten]
  simp only [List.map_map,Function.comp_def,← Option.toList_map,Option.map_map]
  change (x.ns.map (fun n => (((q.roundCounts (fun a b => x.df (x.orig a) (x.orig b))
    (fun c a => x.dc c (x.orig a)) n).map (fun O => MaskProgram.imageRaw
      ((List.replicate x.h (),List.ofFn (fun i => (x.orig i).val)),setView O))).toList))).flatten=_
  simp only [MaskProgram.imageRaw_view]
  simp only [Input.candidates,RationalParameters.countCandidates,
    List.flatMap_def,List.map_flatten,List.map_map]
  simp only [← Option.toList_map,Option.map_map,Function.comp_def]

noncomputable def candidatesProgram : PolyProgram Input.encode SparseGraph.ListOperation.et
    (fun x => (x.candidates q).map setView) := by
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let p := itemsProgram.comp ((RoundCountsProgram.program q).listMap dummy)
  exact (r.fanout p |>.comp images_poly.program).congr _ (images_input q)

def metadata (x : Raw) : ℚ × List (List ℚ) := (x.2.2.2,x.2.1.2)
@[fun_prop] theorem metadata_poly : Poly metadata := by unfold metadata; fun_prop

def Input.result (x : Input) : Table := ((q.roundList x.df x.dc x.orig x.ns x.budget).map setView).toList
noncomputable def program : PolyProgram Input.encode SparseGraph.ListOperation.et (Input.result q) := by
  let m := metadata_poly.program.recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (m.fanout (candidatesProgram q) |>.comp Completion.Rational.BestProgram.raw_poly.program).congr _ (fun x => by
    change Completion.Rational.BestProgram.raw ((x.budget,List.ofFn (fun c => List.ofFn (x.dc c))),
      (x.candidates q).map setView)=x.result q
    rw [Completion.Rational.BestProgram.raw_best]
    rfl)
end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
