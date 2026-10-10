import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalBatchUpdateProgram
import OAI.Combinatorics.KMedian.Sparse.SparseMapBind

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel.RoundProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table)
open CopyList UpdateProgram
local instance {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A

abbrev Raw := CopyGraphProgram.Raw × (ℚ × (ℚ × ℚ))
def ctxRaw (x : Context) : Raw := (x.toInput.raw,(x.β,(x.p,x.φ)))
abbrev ctxEncode (x : Context) := enc (ctxRaw x)

def ctxInputs (x : Context) : List UpdateProgram.Input := x.toInput.law.states.toList.map (fun G => ⟨x,G⟩)

def attach (x : Raw × Data Table) : LawData × List UpdateProgram.Raw :=
  (x.2.1,x.2.2.map fun G => ((x.1.1.1.1.2,x.1.1.2),
    (((x.1.1.1.1.1.1,x.1.2.1),(x.1.1.1.1.2,x.1.2.2)),G)))
@[fun_prop] theorem attach_poly : Poly attach := by
  unfold attach
  apply pair
  · fun_prop
  · apply list_map <;> fun_prop

 theorem attach_input (x : Context) : attach ((ctxRaw x),x.toInput.result)=
    (x.toInput.result.1, (ctxInputs x).map UpdateProgram.Input.raw) := by
  simp only [attach,ctxRaw,CopyGraphProgram.Input.result,ctxInputs,
    List.map_map,Function.comp_def]
  rfl

noncomputable def graphProgram : PolyProgram ctxEncode (ed SparseGraph.ListOperation.et)
    (fun x => x.toInput.result) :=
  (show PolyProgram ctxEncode CopyGraphProgram.Input.encode (fun x : Context => x.toInput) from
    (fst enc enc).recode ctxRaw (fun _ => rfl) (fun _ => rfl)).comp CopyGraphProgram.program

noncomputable def inputsProgram : PolyProgram ctxEncode
    (encodePair enc (encodeList UpdateProgram.Input.encode)) (fun x => (x.toInput.result.1,(ctxInputs x))) := by
  let ctx : PolyProgram ctxEncode enc ctxRaw := (identity enc).recode ctxRaw (fun _ => rfl) (fun _ => rfl)
  exact (ctx.fanout graphProgram |>.comp attach_poly.program).recode id (fun _ => rfl) (fun x => by
    dsimp only [Function.comp_def,id_eq]
    rw [attach_input]
    change encodePair enc (encodeList enc) _=encodePair enc (encodeList UpdateProgram.Input.encode) _
    apply congrArg (fun w => quote (enc x.toInput.result.1)++w)
    induction ctxInputs x with
    | nil => rfl
    | cons a as ih => simpa only [List.map_cons,encodeList,UpdateProgram.Input.encode] using congrArg (fun w => quote (enc a.raw)++w) ih)

def dummy : UpdateProgram.Input where
  ctx := {
    f := 0
    Δ := 0
    d := fun i => Fin.elim0 i
    g := 0
    P := 1
    positive := by norm_num
    A := ∅
    β := 0
    p := 0
    φ := 0
    hp := le_rfl
    hφ := le_rfl
    hupper := by norm_num }
  G := fun _ => ∅

def ctxLaw (x : Context) : SparseIntegerLaw (Finset (CopyState.Copy (F:=Fin x.f) x.Δ)) := x.toInput.law.bindIndexed
  (fun i => (UpdateProgram.Input.mk x x.toInput.law.states[i.val]).law)
def ctxResult (x : Context) : Data Row :=
  (((ctxLaw x).law.denominator,List.ofFn (ctxLaw x).law.numerator),(ctxLaw x).states.toList.map CopyList.view)

noncomputable def program : PolyProgram ctxEncode (ed SparseGraph.ListOperation.er) ctxResult := by
  let getLaw := fst (α:=LawData) (β:=List UpdateProgram.Input) enc (encodeList UpdateProgram.Input.encode)
  let getInputs := snd (α:=LawData) (β:=List UpdateProgram.Input) enc (encodeList UpdateProgram.Input.encode)
  let cond := getLaw.fanout (getInputs.comp (UpdateProgram.program.listMap dummy))
  exact (inputsProgram.comp cond |>.comp bindData_poly.program).congr _ (fun x => by
    change bindData (x.toInput.result.1,(ctxInputs x).map UpdateProgram.Input.result)=(ctxResult x)
    have hh : (ctxInputs x).map UpdateProgram.Input.result=List.ofFn (fun i =>
      ((raw ((UpdateProgram.Input.mk x x.toInput.law.states[i.val]).law)).1,
        (UpdateProgram.Input.mk x x.toInput.law.states[i.val]).law.states.toList.map CopyList.view)) := by
      simp only [ctxInputs,states_list,List.map_ofFn,Function.comp_def,UpdateProgram.Input.result,raw]
    rw [hh]
    have h := bindData_raw (β:=Finset (CopyState.Copy (F:=Fin x.f) x.Δ)) x.toInput.law
      (fun i => (UpdateProgram.Input.mk x x.toInput.law.states[i.val]).law) CopyList.view
    exact h)

 theorem law_step (x : Context) (s : State (Fin x.f) x.Δ x.g x.β) (hs : s.1=x.A) :
    (ctxLaw x)=(step x.d x.g x.β x.p x.φ x.P x.hp x.hφ x.hupper s).map Prod.fst := by
  unfold step
  erw [SparseIntegerLaw.map_map]
  unfold RationalBatchData.events
  erw [SparseIntegerLaw.map_bindIndexed]
  cases s with
  | mk A payload =>
    dsimp only at hs
    subst A
    unfold ctxLaw
    congr 1
    funext i
    erw [SparseIntegerLaw.map_map]
    rfl
end MetricKMedian.RationalPhysicalKernel.RoundProgram
end

end OAI
