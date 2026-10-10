import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalRoundProgram
import OAI.Combinatorics.KMedian.Sparse.SparseTable

namespace OAI


                                                
section
namespace MetricKMedian.RationalPhysicalKernel.HistoryProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table)
open CopyList UpdateProgram
local instance {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A

abbrev Hist (x : Context) := SparseHistories.History (State (Fin x.f) x.Δ x.g x.β)
def law (P : ℕ → ℚ) (T : ℕ) (x : Context) := histories x.d x.g x.β x.p x.φ P x.hp x.hφ x.hupper x.A T
abbrev view (x : Context) (z : Hist x) := CopyList.view z.1.1
def result (P : ℕ → ℚ) (T : ℕ) (x : Context) : Data Row := table (law P T x) (view x)

def nextCtx (x : Context) (P : ℚ) (hP : 0<P) (A : Finset (CopyState.Copy (F:=Fin x.f) x.Δ)) : Context :=
  {x with toInput := {x.toInput with P:=P,positive:=hP,A:=A}}

def nextRaw (P : ℚ) (x : RoundProgram.Raw × Row) : RoundProgram.Raw :=
  (((((x.1.1.1.1.1.1,P),x.1.1.1.1.2),x.1.1.1.2),x.2),x.1.2)
@[fun_prop] theorem nextRaw_poly (P : ℚ) : Poly (nextRaw P) := by unfold nextRaw; fun_prop
 theorem nextCtx_raw (x : Context) (P : ℚ) (hP : 0<P) (A) :
    nextRaw P (RoundProgram.ctxRaw x,CopyList.view A)=RoundProgram.ctxRaw (nextCtx x P hP A) := rfl

def attach (P : ℚ) (x : RoundProgram.Raw × Data Row) : LawData × List RoundProgram.Raw :=
  (x.2.1,x.2.2.map (fun A => nextRaw P (x.1,A)))
@[fun_prop] theorem attach_poly (P : ℚ) : Poly (attach P) := by
  unfold attach
  apply pair
  · fun_prop
  · apply list_map <;> fun_prop

def inputs (P : ℕ → ℚ) (T : ℕ) (hP : 0<P T) (x : Context) : List Context :=
  (law P T x).states.toList.map (fun z => nextCtx x (P T) hP z.1.1)
 theorem attach_result (P : ℕ → ℚ) (T : ℕ) (hP : 0<P T) (x : Context) :
    attach (P T) (RoundProgram.ctxRaw x,result P T x)=
      ((result P T x).1,(inputs P T hP x).map RoundProgram.ctxRaw) := by
  simp only [attach,result,table,inputs,List.map_map,Function.comp_def]
  rfl

 theorem conditional (P : ℕ → ℚ) (T : ℕ) (hP : 0<P T) (x : Context) (z : Hist x) :
    RoundProgram.ctxResult (nextCtx x (P T) hP z.1.1)=
      table (SparseHistories.branch (step x.d x.g x.β x.p x.φ (P T) x.hp x.hφ x.hupper) z) (view x) := by
  change table (RoundProgram.ctxLaw (nextCtx x (P T) hP z.1.1)) CopyList.view=_
  have hs := RoundProgram.law_step (nextCtx x (P T) hP z.1.1) z.1 rfl
  rw [hs,table_map]
  unfold SparseHistories.branch
  rw [table_map]
  rfl

noncomputable def program (P : ℕ → ℚ) (T : ℕ) (hP : ∀ t<T,0<P t) :
    PolyProgram RoundProgram.ctxEncode (ed SparseGraph.ListOperation.er) (result P T) := by
  induction T with
  | zero =>
    let q : Poly (fun x : RoundProgram.Raw => (((1:ℤ),[(1:ℤ)]),[x.1.2])) := by
      apply pair
      · fun_prop
      · fun_prop
    exact q.program.recode RoundProgram.ctxRaw (fun _ => rfl) (fun _ => rfl)
  | succ T ih =>
    let prev := ih (fun t ht => hP t (by omega))
    let ctx : PolyProgram RoundProgram.ctxEncode enc RoundProgram.ctxRaw :=
      (identity enc).recode RoundProgram.ctxRaw (fun _ => rfl) (fun _ => rfl)
    let attached : PolyProgram RoundProgram.ctxEncode
        (encodePair enc (encodeList RoundProgram.ctxEncode))
        (fun x => ((result P T x).1,inputs P T (hP T (by omega)) x)) :=
      (ctx.fanout prev |>.comp (attach_poly (P T)).program).recode id (fun _ => rfl) (fun x => by
        dsimp only [Function.comp_def,id_eq]
        rw [attach_result P T (hP T (by omega))]
        change encodePair enc (encodeList enc) _=encodePair enc (encodeList RoundProgram.ctxEncode) _
        simp only [encodePair,encodeList_map]
        rfl)
    let getLaw := fst (α:=LawData) (β:=List Context) enc (encodeList RoundProgram.ctxEncode)
    let getInputs := snd (α:=LawData) (β:=List Context) enc (encodeList RoundProgram.ctxEncode)
    let cond := getLaw.fanout (getInputs.comp (RoundProgram.program.listMap RoundProgram.dummy.ctx))
    exact (attached.comp cond |>.comp bindData_poly.program).congr _ (fun x => by
      change bindData ((result P T x).1,(inputs P T (hP T (by omega)) x).map RoundProgram.ctxResult)=result P (T+1) x
      unfold result law histories
      rw [SparseHistories.tree,table_bind]
      apply congrArg bindData
      apply Prod.ext
      · rfl
      · simp only [inputs,Function.comp_def,states_list,List.map_ofFn]
        apply congrArg List.ofFn
        funext i
        exact conditional P T (hP T (by omega)) x _)
end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
