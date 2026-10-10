import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanEncoding

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace Thread
variable (M : Machine)
abbrev Key := M.K ⊕ Bool
abbrev Label := M.Label ⊕ Fin 4
abbrev State := M.State × Option Bool
abbrev source : Key M := .inr false
abbrev buffer : Key M := .inr true
abbrev reading : Label M := .inr 0
abbrev loading : Label M := .inr 1
abbrev emitting : Label M := .inr 2
abbrev draining : Label M := .inr 3

def store (s : M.K → List Bool) (xs ys : List Bool) : Key M → List Bool :=
  fun k => match k with
  | .inl k => s k
  | .inr false => xs
  | .inr true => ys

@[simp] theorem store_local (s : M.K → List Bool) (xs ys : List Bool) (k : M.K) :
    store M s xs ys (.inl k)=s k := rfl
@[simp] theorem store_source (s : M.K → List Bool) (xs ys : List Bool) :
    store M s xs ys (source M)=xs := rfl
@[simp] theorem store_buffer (s : M.K → List Bool) (xs ys : List Bool) :
    store M s xs ys (buffer M)=ys := rfl

def slot (k : M.K) (xs : List Bool) : M.K → List Bool := fun j => if j=k then xs else []

 theorem slot_nil (k : M.K) : slot M k []=fun _ => [] := by funext j; simp [slot]
 theorem slot_self (k : M.K) (xs : List Bool) : slot M k xs k=xs := by simp [slot]
 theorem slot_update (k : M.K) (xs ys : List Bool) : update (slot M k xs) k ys=slot M k ys := by
  funext j
  by_cases h : j=k <;> simp [slot,h]

 theorem store_update_local (s : M.K → List Bool) (xs ys : List Bool) (k : M.K) (w : List Bool) :
    update (store M s xs ys) (.inl k) w=store M (update s k w) xs ys := by
  funext j
  rcases j with j | j
  · simp [store,update_apply]
  · cases j <;> simp [store]
 theorem store_update_source (s : M.K → List Bool) (xs ys w : List Bool) :
    update (store M s xs ys) (source M) w=store M s w ys := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]
 theorem store_update_buffer (s : M.K → List Bool) (xs ys w : List Bool) :
    update (store M s xs ys) (buffer M) w=store M s xs w := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]

def body (tail : List Bool) : Embedding M.K M.Label M.State (Key M) (Label M) (State M) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := store M s tail []
  stack_key _ _ := rfl
  stack_update s k x := (store_update_local M s tail [] k x).symm
  label := Sum.inl
  halted := some (emitting M)
  stop := .goto (fun _ => emitting M)
  stop_spec _ _ := rfl

 theorem body_stmt (tail : List Bool) (s : TM2.Stmt (fun _ : M.K => Bool) M.Label M.State) :
    (body M tail).stmt s=(body M []).stmt s := by
  induction s <;> simp_all [Embedding.stmt,body]

def clean (v : State M) : State M := (v.1,none)

def readCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (source M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.getD false)
      (.pop (source M) (fun v b => (v.1,b))
        (.push (buffer M) (fun v => v.2.getD false)
          (.load (clean M) (.goto (fun _ => reading M)))))
      (.load (clean M) (.goto (fun _ => loading M))))

def loadCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (.inl M.input) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => loading M))))
      (.load (clean M) (.goto (fun _ => .inl M.main))))

def emitCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (.inl M.output) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (buffer M) (fun _ => true) (.push (buffer M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => emitting M)))))
      (.push (buffer M) (fun _ => false)
        (.load (clean M) (.goto (fun _ => draining M)))))

def drainCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (source M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => draining M))))
      (.load (clean M) .halt))

def code : Label M → TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M)
  | .inl l => (body M []).stmt (M.code l)
  | .inr i => if i=0 then readCode M else if i=1 then loadCode M else if i=2 then emitCode M else drainCode M

abbrev machine : Machine where
  K := Key M
  input := source M
  output := source M
  Label := Label M
  main := reading M
  State := State M
  initial := (M.initial,none)
  code := code M

 theorem code_body (tail : List Bool) (l : M.Label) :
    (machine M).code ((body M tail).label l)=(body M tail).stmt (M.code l) := (body_stmt M tail _).symm

def readCfg (xs tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (reading M),(M.initial,none),store M (fun _ => []) (quote xs++tail) buf⟩

def loadCfg (tail buf xs : List Bool) : (machine M).Cfg :=
  ⟨some (loading M),(M.initial,none),store M (slot M M.input xs) tail buf⟩

def emitCfg (tail xs buf : List Bool) : (machine M).Cfg :=
  ⟨some (emitting M),(M.initial,none),store M (slot M M.output xs) tail buf⟩

def drainCfg (tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (draining M),(M.initial,none),store M (fun _ => []) tail buf⟩

 theorem read_cons (b : Bool) (xs tail buf : List Bool) :
    (machine M).step (readCfg M (b::xs) tail buf)=some (readCfg M xs tail (b::buf)) := by
  simp [readCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,store_update_buffer]

 theorem read_nil (tail buf : List Bool) :
    (machine M).step (readCfg M [] tail buf)=some (loadCfg M tail buf []) := by
  simp [readCfg,loadCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,slot_nil]

 theorem read_run (xs tail buf : List Bool) :
    Trace (machine M).step (xs.length+1) (readCfg M xs tail buf) (loadCfg M tail (xs.reverse++buf) []) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (read_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (read_cons M b xs tail buf) (ih (b::buf))

 theorem load_cons (b : Bool) (tail buf xs : List Bool) :
    (machine M).step (loadCfg M tail (b::buf) xs)=some (loadCfg M tail buf (b::xs)) := by
  simp [loadCfg,TM2.step,code,loadCode,TM2.stepAux,clean,
    store_update_buffer,store_update_local,slot_update,slot_self]

 theorem load_nil (tail xs : List Bool) :
    (machine M).step (loadCfg M tail [] xs)=some ((body M tail).cfg (M.initialCfg xs)) := by
  simp [loadCfg,Embedding.cfg,body,Machine.initialCfg,TM2.step,code,loadCode,TM2.stepAux,
    clean,store_update_buffer,slot]
  rfl

 theorem load_run (tail buf xs : List Bool) :
    Trace (machine M).step (buf.length+1) (loadCfg M tail buf xs)
      ((body M tail).cfg (M.initialCfg (buf.reverse++xs))) := by
  induction buf generalizing xs with
  | nil => exact Trace.cons (load_nil M tail xs) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (load_cons M b tail bs xs) (ih (b::xs))

 theorem emit_cons (b : Bool) (tail xs buf : List Bool) :
    (machine M).step (emitCfg M tail (b::xs) buf)=some (emitCfg M tail xs (b::true::buf)) := by
  simp [emitCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_update,slot_self]

 theorem emit_nil (tail buf : List Bool) :
    (machine M).step (emitCfg M tail [] buf)=some (drainCfg M tail (false::buf)) := by
  simp [emitCfg,drainCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_nil]

 theorem emit_run (tail xs buf : List Bool) :
    Trace (machine M).step (xs.length+1) (emitCfg M tail xs buf)
      (drainCfg M tail ((quote xs).reverse++buf)) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (emit_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,quote,List.reverse_cons,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        Trace.cons (emit_cons M b tail xs buf) (ih (b::true::buf))

 theorem drain_cons (b : Bool) (tail buf : List Bool) :
    (machine M).step (drainCfg M tail (b::buf))=some (drainCfg M (b::tail) buf) := by
  simp [drainCfg,TM2.step,code,drainCode,TM2.stepAux,clean,
    store_update_source,store_update_buffer]

 theorem drain_nil (tail : List Bool) :
    (machine M).step (drainCfg M tail [])=some ((machine M).finalCfg tail) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.finalCfg,code,drainCode,TM2.stepAux,clean]

 theorem drain_run (tail buf : List Bool) :
    Trace (machine M).step (buf.length+1) (drainCfg M tail buf) ((machine M).finalCfg (buf.reverse++tail)) := by
  induction buf generalizing tail with
  | nil => exact Trace.cons (drain_nil M tail) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (drain_cons M b tail bs) (ih (b::tail))

 theorem body_final (tail xs : List Bool) : (body M tail).cfg (M.finalCfg xs)=emitCfg M tail xs [] := rfl

 theorem run {xs zs : List Bool} {n : ℕ} (tail : List Bool)
    (h : Trace M.step n (M.initialCfg xs) (M.finalCfg zs)) :
    Trace (machine M).step (2*xs.length+3*zs.length+5+n)
      ((machine M).initialCfg (quote xs++tail)) ((machine M).finalCfg (quote zs++tail)) := by
  have hi : (machine M).initialCfg (quote xs++tail)=readCfg M xs tail [] := by
    apply cfg_ext <;> try rfl
    funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.initialCfg,readCfg,store]
  rw [hi]
  have ha := read_run M xs tail []
  simp only [List.append_nil] at ha
  have hb := load_run M tail xs.reverse []
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hb
  have hc := (body M tail).trace M.code (machine M).code (code_body M tail) h
  rw [body_final] at hc
  have hd := emit_run M tail zs []
  simp only [List.append_nil] at hd
  have he := drain_run M tail (quote zs).reverse
  simp only [List.reverse_reverse,List.length_reverse,quote_length] at he
  have hx := (((ha.trans hb).trans hc).trans hd).trans he
  convert hx using 1
  omega

end Thread

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {f : α → β}

 noncomputable def thread (P : PolyProgram ea eb f) (ec : γ → List Bool) :
    PolyProgram (encodePair ea ec) (encodePair eb ec) (fun x => (f x.1,x.2)) where
  machine := Thread.machine P.machine
  time := 2*X+3*P.sizeBound+5+P.time
  outputs x := by
    have hp := P.outputs x.1
    have h := Thread.run P.machine (ec x.2) (Trace.of_iterate hp.evals_in_steps)
    refine ⟨⟨_,h.iterate_eq⟩,?_⟩
    have hn : (ea x.1).length≤(encodePair ea ec x).length := by simp only [encodePair_length]; omega
    have hl := (P.length_bound x.1).trans (polynomial_eval_mono P.sizeBound hn)
    have ht := hp.steps_le_m.trans (polynomial_eval_mono P.time hn)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega

end PolyProgram
end MetricKMedian.Binary
end

end OAI
