import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.ProgramAssembly

namespace OAI

section
universe u v w
namespace SourceBurnside.TwoInputBody
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
variable {f : (Fin 7 → ℕ) → ℕ} {Pre : ℕ → (Fin 7 → ℕ) → Prop}
abbrev K (R : Realizer f Pre) := Fin 7 ⊕ RawCompiled.K R
def codeSlot (R : Realizer f Pre) : K R := .inr (.inl (.inl (.inl 0)))
def requestSlot (R : Realizer f Pre) : K R := .inr (.inl (.inl (.inl 4)))
def source (R : Realizer f Pre) : K R := .inl 0
def start (R : Realizer f Pre) (x : List Bool) : Store (K R) := Function.update (fun _ => []) (source R) x.reverse
def transfer (R : Realizer f Pre) : Program (K R) := .seq (copy (.inl 6) (codeSlot R) (.inl 4))
  (copy (.inl 0) (requestSlot R) (.inl 4))
def program (R : Realizer f Pre) (W D : ℕ) : Program (K R) :=
  .seq (TwoInputQuote.program.relabel Sum.inl) (.seq (transfer R) ((RawCompiled.program R W D).relabel Sum.inr))
lemma start_eq (R : Realizer f Pre) (x : List Bool) :
    start R x=Sum.elim (TwoInputQuote.store x [] [] 0 []) (fun _ => []) := by
  funext j;cases j with
  | inl j => fin_cases j <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, start,source,TwoInputQuote.store]
  | inr j => simp [-Sum.update_elim_inr, -Sum.elim_update_right, start,source]
lemma update_ready (R : Realizer f Pre) (r : Fin 7 → List Bool) (code request : List Bool) :
    Function.update (Function.update (Sum.elim r (fun _ => [])) (codeSlot R) code.reverse)
      (requestSlot R) request.reverse=Sum.elim r (RawCompiled.before R code request) := by
  funext j;cases j with
  | inl j => simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot]
  | inr j => cases j with
    | inr j => simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot,RawCompiled.before]
    | inl j => cases j with
      | inr j => simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot,RawCompiled.before,RawAssembler.store]
      | inl j => cases j with
        | inr j => fin_cases j <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot,RawCompiled.before,RawAssembler.store,RawNumberPrep.store]
        | inl j => fin_cases j <;> simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot,RawCompiled.before,RawAssembler.store,RawNumberPrep.store,RawNumberPrep.before]
lemma transfer_run (R : Realizer f Pre) (v request : List Bool) :
    let q := TwoInputQuote.store request (InitialFormula.bin v.length) v 0 (WrappedInput.specialize v v).reverse
    Run (transfer R) (Sum.elim q (fun _ => []))
      (5*(WrappedInput.specialize v v).length+2+(5*request.length+2))
      (Sum.elim q (RawCompiled.before R (WrappedInput.specialize v v) request)) := by
  dsimp only
  let r := Sum.elim (TwoInputQuote.store request (InitialFormula.bin v.length) v 0 (WrappedInput.specialize v v).reverse)
    (fun _ : RawCompiled.K R => [])
  have H1 := copy_run (.inl 6 : K R) (codeSlot R) (.inl 4)
    (by simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot]) (by simp) (by simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot]) r rfl
  have H2 := copy_run (.inl 0 : K R) (requestSlot R) (.inl 4)
    (by simp [-Sum.update_elim_inr, -Sum.elim_update_right, requestSlot]) (by simp) (by simp [-Sum.update_elim_inr, -Sum.elim_update_right, requestSlot])
    (Function.update r (codeSlot R) (WrappedInput.specialize v v).reverse) (by simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,r,TwoInputQuote.store])
  change Run (copy (.inl 6 : K R) (codeSlot R) (.inl 4)) r
    (5*(WrappedInput.specialize v v).reverse.length+2)
    (Function.update r (codeSlot R) (WrappedInput.specialize v v).reverse) at H1
  rw [List.length_reverse] at H1
  have HC : codeSlot R≠requestSlot R := by simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,requestSlot]
  have hreq : (Function.update r (codeSlot R) (WrappedInput.specialize v v).reverse) (requestSlot R)=[] := by
    rw [Function.update_of_ne (Ne.symm HC)]
    rfl
  have hsrc : (Function.update r (codeSlot R) (WrappedInput.specialize v v).reverse) (.inl 0)=request.reverse := by
    simp [-Sum.update_elim_inr, -Sum.elim_update_right, codeSlot,r,TwoInputQuote.store]
  rw [hreq,hsrc,List.nil_append,List.length_reverse] at H2
  have H := Run.seq _ _ _ _ _ _ _ H1 H2
  rw [update_ready] at H
  exact H

theorem trace (e : Formula (Fin 7)) (D : ℕ)
    (hE : ∀code h l z data,e.Exponents (RawPreparedInputs.bound D h code data l)
      (RawPreparedInputs.semantic code h l z data)) :
    ∃R : Realizer e.totalize.eval (fun n v => e.totalize.Safe n v),
      ∀(v : List Bool) (h l : ℕ) (z : Bool) (data : List Bool),
        let code := WrappedInput.specialize v v
        let request := RawHeader.request h l z data
        let n := RawNumberPrep.width e.weight D h code data (InitialFormula.bin l)
        let q := TwoInputQuote.store request (InitialFormula.bin v.length) v 0 code.reverse
        ∃t y,t ≤ (7*v.length+47)*InitialFormula.binSize v.length+17*v.length+32+
            (5*code.length+2+(5*request.length+2))+
            (RawCompiled.setupBound e.weight D h l code data+R.coefficient*(n+1)^2) ∧
          y.length=n ∧ Add.value y.reverse=e.eval (RawPreparedInputs.semantic code h l z data) ∧
          Run (program R e.weight D) (start R (InitialFormula.enc v.length++v++request)) t
            (Sum.elim q (Function.update (RawCompiled.prepared R n code h l z data) (.inr R.out) y)) := by
  obtain ⟨R,hR⟩ := RawCompiled.generic_trace e D hE
  refine ⟨R,?_⟩
  intro v h l z data
  obtain ⟨tb,y,hb,hy,hyv,HB⟩ := hR (WrappedInput.specialize v v) h l z data
  obtain ⟨ta,ha,HA⟩ := TwoInputQuote.program_run v (RawHeader.request h l z data)
  have H0 := HA.extend_left (fun _ : RawCompiled.K R => [])
  rw [←start_eq] at H0
  have H1 := transfer_run R v (RawHeader.request h l z data)
  have H2 := HB.extend_right (TwoInputQuote.store (RawHeader.request h l z data)
    (InitialFormula.bin v.length) v 0 (WrappedInput.specialize v v).reverse)
  refine ⟨ta+((5*(WrappedInput.specialize v v).length+2+(5*(RawHeader.request h l z data).length+2))+tb),y,?_,hy,hyv,?_⟩
  · have H := Nat.add_le_add ha (Nat.add_le_add_left hb (5*(WrappedInput.specialize v v).length+2+(5*(RawHeader.request h l z data).length+2)))
    simpa only [Nat.add_assoc] using H
  · exact Run.seq _ _ _ _ _ _ _ H0 (Run.seq _ _ _ _ _ _ _ H1 H2)
end SourceBurnside.TwoInputBody

namespace SourceBurnside.CompactStacks
open StackMachine
variable {m : ℕ} {Q : Type}

inductive State (m : ℕ) (Q : Type)
  | start (q : Q)
  | seek (q : Q) (k : Fin (m+1))
  | saveTag (q : Q) (k : Fin (m+1)) (a : Option Bool)
  | readData (q : Q) (k : Fin (m+1))
  | saveData (q : Q) (k : Fin (m+1)) (a : Option Bool)
  | insertTag (q : Q)
  | popTag (q : Q) (a : Option Bool)
  | restore (q : Q)
  | putBack (q : Q) (b : Bool)
  deriving DecidableEq, Fintype

def pred (k : Fin (m+1)) : Fin (m+1) := ⟨k.val-1,by have := k.isLt;omega⟩
def operation (P : Q → Instr (Fin m) Bool Q) (q : Q) : Instr (Fin 2) Bool (State m Q) :=
  match P q with
  | .halt => .halt
  | .push _ b q' => .push 0 b (.insertTag q')
  | .pop _ _ => .pop 0 (fun b => .popTag q b)
def seeking (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin (m+1)) : Instr (Fin 2) Bool (State m Q) :=
  if k.val=0 then operation P q else .pop 0 (fun a => .saveTag q k a)
def machine (P : Q → Instr (Fin m) Bool Q) : State m Q → Instr (Fin 2) Bool (State m Q)
  | .start q => match P q with
    | .halt => .halt
    | .push k _ _ | .pop k _ => seeking P q k.castSucc
  | .seek q k => seeking P q k
  | .saveTag q k a => match a with
    | none => .halt
    | some true => .push 1 true (.readData q k)
    | some false => .push 1 false (.seek q (pred k))
  | .readData q k => .pop 0 (fun a => .saveData q k a)
  | .saveData q k a => match a with
    | none => .halt
    | some b => .push 1 b (.seek q k)
  | .insertTag q' => .push 0 true (.restore q')
  | .popTag q a => match P q,a with
    | .pop _ f,some true => .pop 0 (fun b => .restore (f b))
    | .pop _ f,some false => .push 0 false (.restore (f none))
    | _,_ => .halt
  | .restore q => .pop 1 (fun b => match b with | none => .start q | some b => .putBack q b)
  | .putBack q b => .push 0 b (.restore q)

def block (bs : List Bool) : List Bool := bs.flatMap (fun b => [true,b])++[false]
def words (ss : List (List Bool)) : List Bool := ss.flatMap block
@[simp] lemma block_length (bs : List Bool) : (block bs).length=2*bs.length+1 := by
  simp [block,Nat.mul_comm]
@[simp] lemma block_cons (b : Bool) (bs : List Bool) : block (b::bs)=true::b::block bs := by simp [block]
@[simp] lemma block_nil : block []=[false] := rfl
@[simp] lemma words_nil : words []=[] := rfl
@[simp] lemma words_cons (b : List Bool) (bs : List (List Bool)) : words (b::bs)=block b++words bs := by simp [words]

def config (s : State m Q) (front back : List Bool) : Config (Fin 2) Bool (State m Q) :=
  ⟨s,![front.reverse,back]⟩

lemma skip_bit (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin (m+1)) (hk : k.val≠0)
    (b : Bool) (xs acc : List Bool) :
    exec (machine P) (config (.seek q k) (true::b::xs) acc) 4 =
      config (.seek q k) xs (acc++[true,b]) := by
  simp [exec,next,machine,seeking,hk,config,List.reverse_cons,List.append_assoc]
  funext i;fin_cases i <;> simp
lemma skip_end (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin (m+1)) (hk : k.val≠0)
    (xs acc : List Bool) :
    exec (machine P) (config (.seek q k) (false::xs) acc) 2 =
      config (.seek q (pred k)) xs (acc++[false]) := by
  simp [exec,next,machine,seeking,hk,config,List.reverse_cons]
  funext i;fin_cases i <;> simp

lemma skip_block (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin (m+1)) (hk : k.val≠0)
    (bs xs acc : List Bool) :
    exec (machine P) (config (.seek q k) (block bs++xs) acc) (2*(block bs).length) =
      config (.seek q (pred k)) xs (acc++block bs) := by
  induction bs generalizing acc with
  | nil => simpa using skip_end P q k hk xs acc
  | cons a bs ih =>
    rw [block_cons,List.cons_append,List.cons_append]
    have he : 2*(true::a::block bs).length=4+2*(block bs).length := by simp;omega
    rw [he,UniversalStack.exec_from,skip_bit P q k hk a (block bs++xs) acc,ih]
    all_goals simp [List.append_assoc]

lemma skip_words (P : Q → Instr (Fin m) Bool Q) (q : Q)
    (ss : List (List Bool)) (k : Fin (m+1)) (hk : ss.length≤k.val) (xs acc : List Bool) :
    exec (machine P) (config (.seek q k) (words ss++xs) acc) (2*(words ss).length) =
      config (.seek q ⟨k.val-ss.length,by have := k.isLt;omega⟩) xs (acc++words ss) := by
  induction ss generalizing k acc with
  | nil => simp [exec]
  | cons b ss ih =>
    have hn : k.val≠0 := by simp only [List.length_cons] at hk;omega
    have ht : ss.length≤(pred k).val := by simp only [List.length_cons] at hk;dsimp [pred];omega
    rw [words_cons,List.append_assoc,show 2*(block b++words ss).length=2*(block b).length+2*(words ss).length by simp;omega]
    rw [UniversalStack.exec_from,skip_block P q k hn b (words ss++xs) acc,ih (pred k) ht]
    congr 1
    · congr 1;apply Fin.ext;dsimp [pred];omega
    · simp [List.append_assoc]

lemma restore (P : Q → Instr (Fin m) Bool Q) (q : Q) (xs acc : List Bool) :
    exec (machine P) (config (.restore q) xs acc) (2*acc.length+1)=config (.start q) (acc++xs) [] := by
  induction acc using List.reverseRecOn generalizing xs with
  | nil => simp [exec,next,machine,config]
  | append_singleton acc b ih =>
    have H : exec (machine P) (config (.restore q) xs (acc++[b])) 2=config (.restore q) (b::xs) acc := by
      simp [exec,next,machine,config,List.reverse_cons]
      funext i;fin_cases i <;> simp
    rw [show 2*(acc++[b]).length+1=2+(2*acc.length+1) by simp;omega,UniversalStack.exec_from,H,ih]
    all_goals simp [List.append_assoc]

lemma at_push (P : Q → Instr (Fin m) Bool Q) (q q' : Q) (k : Fin m) (b : Bool)
    (hp : P q=.push k b q') (bs xs acc : List Bool) :
    exec (machine P) (config (.seek q 0) (block bs++xs) acc) 2=
      config (.restore q') (block (b::bs)++xs) acc := by
  simp [exec,next,machine,seeking,operation,hp,config,List.reverse_cons,
    List.reverse_append,List.append_assoc]
  funext i;fin_cases i <;> simp

lemma at_pop_cons (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin m)
    (f : Option Bool → Q) (hp : P q=.pop k f) (b : Bool) (bs xs acc : List Bool) :
    exec (machine P) (config (.seek q 0) (block (b::bs)++xs) acc) 2=
      config (.restore (f (some b))) (block bs++xs) acc := by
  simp [exec,next,machine,seeking,operation,hp,config,List.reverse_cons,List.reverse_append]
  funext i;fin_cases i <;> simp

lemma at_pop_nil (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin m)
    (f : Option Bool → Q) (hp : P q=.pop k f) (xs acc : List Bool) :
    exec (machine P) (config (.seek q 0) (block []++xs) acc) 2=
      config (.restore (f none)) (block []++xs) acc := by
  simp [exec,next,machine,seeking,operation,hp,config,List.reverse_cons]

lemma start_push (P : Q → Instr (Fin m) Bool Q) (q q' : Q) (k : Fin m) (b : Bool)
    (hp : P q=.push k b q') (xs acc : List Bool) (n : ℕ) (hn : 0<n) :
    exec (machine P) (config (.start q) xs acc) n=
      exec (machine P) (config (.seek q k.castSucc) xs acc) n := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [UniversalStack.exec_start,UniversalStack.exec_start]
  congr 1
  by_cases hk : k.val=0 <;> simp [next,machine,hp,config,seeking,operation,hk]

lemma start_pop (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin m)
    (f : Option Bool → Q) (hp : P q=.pop k f) (xs acc : List Bool) (n : ℕ) (hn : 0<n) :
    exec (machine P) (config (.start q) xs acc) n=
      exec (machine P) (config (.seek q k.castSucc) xs acc) n := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [UniversalStack.exec_start,UniversalStack.exec_start]
  congr 1
  by_cases hk : k.val=0 <;> simp [next,machine,hp,config,seeking,operation,hk]

@[simp] lemma words_append (a b : List (List Bool)) : words (a++b)=words a++words b := by
  simp [words]

def registers (r : Fin m → List Bool) : List (List Bool) := List.ofFn (fun k => (r k).reverse)
@[simp] lemma registers_length (r : Fin m → List Bool) : (registers r).length=m := by simp [registers]
@[simp] lemma registers_getElem (r : Fin m → List Bool) (i : ℕ) (hi : i<(registers r).length) :
    (registers r)[i]=(r ⟨i,by simpa using hi⟩).reverse := by simp [registers]

lemma registers_update (r : Fin m → List Bool) (k : Fin m) (bs : List Bool) :
    registers (Function.update r k bs)=(registers r).set k.val bs.reverse := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [registers_length] at hi
  by_cases he : i=k.val
  · subst i;simp
  · have hn : (⟨i,hi⟩ : Fin m)≠k := by intro h;exact he (congrArg Fin.val h)
    simp [Ne.symm he,hn,registers]

lemma registers_split (r : Fin m → List Bool) (k : Fin m) :
    registers r=(registers r).take k.val ++ (r k).reverse::(registers r).drop (k.val+1) := by
  conv_lhs => rw [←List.take_append_drop k.val (registers r)]
  rw [List.drop_eq_getElem_cons (by simp)]
  simp

lemma full_push (P : Q → Instr (Fin m) Bool Q) (q q' : Q) (k : Fin m) (b : Bool)
    (hp : P q=.push k b q') (pre : List (List Bool)) (bs xs : List Bool) (hk : pre.length=k.val) :
    exec (machine P) (config (.start q) (words pre++block bs++xs) []) (4*(words pre).length+3)=
      config (.start q') (words pre++block (b::bs)++xs) [] := by
  rw [start_push P q q' k b hp _ _ _ (by omega)]
  rw [show 4*(words pre).length+3=2*(words pre).length+(2+(2*(words pre).length+1)) by omega,
    UniversalStack.exec_from _ _ (2*(words pre).length) (2+(2*(words pre).length+1)),List.append_assoc,
    skip_words P q pre k.castSucc (by simp [hk])]
  simp only [Fin.val_castSucc,hk,Nat.sub_self,List.nil_append,Fin.mk_zero]
  rw [UniversalStack.exec_from _ _ 2 _,at_push P q q' k b hp,restore]
  all_goals simp [List.append_assoc]

lemma full_pop_cons (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin m)
    (f : Option Bool → Q) (hp : P q=.pop k f) (pre : List (List Bool)) (b : Bool)
    (bs xs : List Bool) (hk : pre.length=k.val) :
    exec (machine P) (config (.start q) (words pre++block (b::bs)++xs) []) (4*(words pre).length+3)=
      config (.start (f (some b))) (words pre++block bs++xs) [] := by
  rw [start_pop P q k f hp _ _ _ (by omega)]
  rw [show 4*(words pre).length+3=2*(words pre).length+(2+(2*(words pre).length+1)) by omega,
    UniversalStack.exec_from _ _ (2*(words pre).length) (2+(2*(words pre).length+1)),List.append_assoc,
    skip_words P q pre k.castSucc (by simp [hk])]
  simp only [Fin.val_castSucc,hk,Nat.sub_self,List.nil_append,Fin.mk_zero]
  rw [UniversalStack.exec_from _ _ 2 _,at_pop_cons P q k f hp,restore]
  all_goals simp [List.append_assoc]

lemma full_pop_nil (P : Q → Instr (Fin m) Bool Q) (q : Q) (k : Fin m)
    (f : Option Bool → Q) (hp : P q=.pop k f) (pre : List (List Bool))
    (xs : List Bool) (hk : pre.length=k.val) :
    exec (machine P) (config (.start q) (words pre++block []++xs) []) (4*(words pre).length+3)=
      config (.start (f none)) (words pre++block []++xs) [] := by
  rw [start_pop P q k f hp _ _ _ (by omega)]
  rw [show 4*(words pre).length+3=2*(words pre).length+(2+(2*(words pre).length+1)) by omega,
    UniversalStack.exec_from _ _ (2*(words pre).length) (2+(2*(words pre).length+1)),List.append_assoc,
    skip_words P q pre k.castSucc (by simp [hk])]
  simp only [Fin.val_castSucc,hk,Nat.sub_self,List.nil_append,Fin.mk_zero]
  rw [UniversalStack.exec_from _ _ 2 _,at_pop_nil P q k f hp,restore]

def encode (C : Config (Fin m) Bool Q) : Config (Fin 2) Bool (State m Q) :=
  config (.start C.state) (words (registers C.store)) []

def ticks (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q) : ℕ :=
  match P C.state with
  | .halt => 0
  | .push k _ _ | .pop k _ => 4*(words ((registers C.store).take k.val)).length+3

lemma words_update (r : Fin m → List Bool) (k : Fin m) (bs : List Bool) :
    words (registers (Function.update r k bs))=
      words ((registers r).take k.val)++block bs.reverse++words ((registers r).drop (k.val+1)) := by
  rw [registers_update,List.set_eq_take_append_cons_drop,ite_eq_left (by simp)]
  simp [List.append_assoc]

lemma encode_push (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q)
    (k : Fin m) (b : Bool) (q' : Q) (h : P C.state=.push k b q') :
    exec (machine P) (encode C) (ticks P C)=encode (next P C) := by
  have H := full_push P C.state q' k b h ((registers C.store).take k.val)
    (C.store k).reverse (words ((registers C.store).drop (k.val+1))) (by simp)
  have hs : words (registers C.store)=words ((registers C.store).take k.val)++
    block (C.store k).reverse++words ((registers C.store).drop (k.val+1)) := by
    conv_lhs => rw [registers_split C.store k]
    simp [List.append_assoc]
  simpa [encode,ticks,next,h,hs,words_update,List.reverse_append,List.reverse_cons] using H

lemma encode_pop (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q)
    (k : Fin m) (f : Option Bool → Q) (h : P C.state=.pop k f) :
    exec (machine P) (encode C) (ticks P C)=encode (next P C) := by
  have hs : words (registers C.store)=words ((registers C.store).take k.val)++
    block (C.store k).reverse++words ((registers C.store).drop (k.val+1)) := by
    conv_lhs => rw [registers_split C.store k]
    simp [List.append_assoc]
  generalize hb : (C.store k).reverse=bs
  have hl : C.store k=bs.reverse := by rw [←hb,List.reverse_reverse]
  cases bs with
  | nil =>
    have H := full_pop_nil P C.state k f h ((registers C.store).take k.val)
      (words ((registers C.store).drop (k.val+1))) (by simp)
    rw [hb] at hs
    simpa [encode,ticks,next,h,hs,words_update,hl] using H
  | cons b bs =>
    have H := full_pop_cons P C.state k f h ((registers C.store).take k.val) b bs
      (words ((registers C.store).drop (k.val+1))) (by simp)
    rw [hb] at hs
    simpa [encode,ticks,next,h,hs,words_update,hl,List.dropLast_reverse] using H

theorem encode_next (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q) :
    exec (machine P) (encode C) (ticks P C)=encode (next P C) := by
  cases h : P C.state with
  | halt => simp [ticks,h,exec,next]
  | push k b q => exact encode_push P C k b q h
  | pop k f => exact encode_pop P C k f h

def clock (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q) : ℕ → ℕ
  | 0 => 0
  | n+1 => clock P C n+ticks P (exec P C n)

theorem encode_exec (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q) (n : ℕ) :
    exec (machine P) (encode C) (clock P C n)=encode (exec P C n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [clock,UniversalStack.exec_from,ih,encode_next]
    rfl

lemma words_length_le (ss : List (List Bool)) (B : ℕ) (h : ∀bs∈ss,bs.length≤B) :
    (words ss).length≤ ss.length*(2*B+1) := by
  induction ss with
  | nil => simp
  | cons bs ss ih =>
    have hb := h bs (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    simp only [words_cons,List.length_append,block_length,List.length_cons]
    nlinarith

lemma words_registers_length_le (r : Fin m → List Bool) (B : ℕ) (h : ∀k,(r k).length≤B) :
    (words (registers r)).length≤ m*(2*B+1) := by
  have H := words_length_le (registers r) B (by
    intro bs hb
    simp only [registers,List.mem_ofFn] at hb
    obtain ⟨k,rfl⟩ := hb
    simpa using h k)
  simpa using H

lemma words_take_length_le (ss : List (List Bool)) (k : ℕ) :
    (words (ss.take k)).length≤(words ss).length := by
  have h := congrArg (fun ts => (words ts).length) (List.take_append_drop k ss)
  simp only [words_append,List.length_append] at h
  omega

lemma ticks_bound (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q)
    (B : ℕ) (h : ∀k,(C.store k).length≤B) : ticks P C≤4*m*(2*B+1)+3 := by
  have H := words_registers_length_le C.store B h
  cases hp : P C.state with
  | halt => simp [ticks,hp]
  | push k b q =>
    have ht := words_take_length_le (registers C.store) k.val
    simp only [ticks,hp];nlinarith
  | pop k f =>
    have ht := words_take_length_le (registers C.store) k.val
    simp only [ticks,hp];nlinarith

theorem clock_bound (P : Q → Instr (Fin m) Bool Q) (C : Config (Fin m) Bool Q)
    (B : ℕ) (h : ∀k,(C.store k).length≤B) (n : ℕ) :
    clock P C n≤n*(4*m*(2*(B+n)+1)+3) := by
  induction n with
  | zero => simp [clock]
  | succ n ih =>
    have H := ticks_bound P (exec P C n) (B+n) (fun k =>
      (StackMachine.exec_length P C n k).trans (Nat.add_le_add_right (h k) n))
    rw [clock]
    have ht := Nat.add_le_add ih H
    nlinarith

end SourceBurnside.CompactStacks

namespace SourceBurnside.CompactInit
open Structured Structured.Program Structured.Binary
abbrev K := Fin 2
def store (todo acc : List Bool) : Store K := ![todo.reverse,acc]
def pairs (x : List Bool) : List Bool := x.flatMap (fun b => [true,b])
def packet : Program K := .loop 0 (fun b => .seq (.push 1 true) (.push 1 b))
lemma push_run (x acc : List Bool) (b : Bool) :
    Run (.push (1:K) b) (store x acc) 1 (store x (acc++[b])) := by
  convert Run.push (store x acc) (1:K) b using 1
  funext j;fin_cases j <;> simp [store]
lemma packet_run (x acc : List Bool) :
    Run packet (store x acc) (3*x.length+1) (store [] (acc++pairs x)) := by
  induction x generalizing acc with
  | nil => simpa [packet,pairs,List.append_nil] using Run.loop_nil (store [] acc) (0:K) (fun b => .seq (.push 1 true) (.push 1 b)) rfl
  | cons b xs ih =>
    have he : Function.update (store (b::xs) acc) (0:K) xs.reverse=store xs acc := by
      funext j;fin_cases j <;> simp [store]
    have hb := Run.seq _ _ _ _ _ _ _ (push_run xs acc true) (push_run xs (acc++[true]) b)
    rw [←he] at hb
    have H := Run.loop_cons (store (b::xs) acc) (0:K) (fun b => .seq (.push 1 true) (.push 1 b))
      xs.reverse b (store xs ((acc++[true])++[b])) _ 2 (3*xs.length+1) (by simp [store]) hb
      (ih ((acc++[true])++[b]))
    convert H using 1 <;> simp [packet,pairs,List.append_assoc]
    omega
lemma packet_length (x : List Bool) : (pairs x).length=2*x.length := by
  simp [pairs,Nat.mul_comm]
def program (m j : ℕ) : Program K :=
  .seq (pushes 1 j) (.seq packet (.seq (pushes 1 (m-j)) (move 1 0)))
def layout (m j : ℕ) (x : List Bool) : List Bool :=
  List.replicate j false++pairs x++List.replicate (m-j) false
lemma program_run (m j : ℕ) (x : List Bool) :
    Run (program m j) (store x [])
      ((j+1)+(3*x.length+1)+((m-j+1)+(2*(layout m j x).length+1)))
      (store (layout m j x) []) := by
  have h0 := pushes_run (1:K) j (store x [])
  have he0 : Function.update (store x []) (1:K) ([]++List.replicate j false)=store x (List.replicate j false) := by
    funext i;fin_cases i <;> simp [store]
  change Run (pushes (1:K) j) (store x []) (j+1) (Function.update (store x []) (1:K) ([]++List.replicate j false)) at h0
  rw [he0] at h0
  have h1 := packet_run x (List.replicate j false)
  have h2 := pushes_run (1:K) (m-j) (store [] (List.replicate j false++pairs x))
  have he2 : Function.update (store [] (List.replicate j false++pairs x)) (1:K)
      ((List.replicate j false++pairs x)++List.replicate (m-j) false)=store [] (layout m j x) := by
    funext i;fin_cases i <;> simp [store,layout]
  change Run _ _ _ (Function.update (store [] (List.replicate j false++pairs x)) (1:K)
      ((List.replicate j false++pairs x)++List.replicate (m-j) false)) at h2
  rw [he2] at h2
  have h3 := move_run (1:K) 0 (by decide) (store [] (layout m j x))
  have he3 : Function.update (Function.update (store [] (layout m j x)) (1:K) []) (0:K)
      ([]++(layout m j x).reverse)=store (layout m j x) [] := by
    funext i;fin_cases i <;> simp [store]
  change Run _ _ (2*(layout m j x).length+1) (Function.update (Function.update (store [] (layout m j x)) (1:K) []) (0:K)
      ([]++(layout m j x).reverse)) at h3
  rw [he3] at h3
  have H := Run.seq _ _ _ _ _ _ _ h0 (Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3))
  simpa only [program,Nat.add_assoc] using H
lemma layout_length {m j : ℕ} (hj : j ≤ m) (x : List Bool) : (layout m j x).length=m+2*x.length := by
  simp [layout,packet_length];omega
lemma program_time_le {m j : ℕ} (hj : j ≤ m) (x : List Bool) :
    (j+1)+(3*x.length+1)+((m-j+1)+(2*(layout m j x).length+1)) ≤ 3*m+7*x.length+4 := by
  rw [layout_length hj];omega
lemma words_empty (m : ℕ) : CompactStacks.words (List.replicate m [])=List.replicate m false := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ,ih]
lemma words_single (m : ℕ) (j : Fin m) (x : List Bool) :
    CompactStacks.words (List.ofFn (Function.update (fun _ : Fin m => []) j x))=
      List.replicate j.val false++CompactStacks.block x++List.replicate (m-j.val-1) false := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · have h0 : (Function.update (fun _ : Fin (m+1) => []) 0 x) 0=x := by simp
      have ht : (fun i : Fin m => (Function.update (fun _ : Fin (m+1) => []) 0 x) i.succ)=(fun _ => []) := by
        funext i;simp
      rw [List.ofFn_succ,h0,ht]
      simp only [Fin.val_zero,Nat.sub_zero,List.replicate_zero,List.nil_append,List.ofFn_const,CompactStacks.words_cons,words_empty,Nat.add_sub_cancel]
    · have h0 : (Function.update (fun _ : Fin (m+1) => []) k.succ x) 0=[] := by
        exact Function.update_of_ne (Fin.succ_ne_zero k).symm _ _
      have ht : (fun i : Fin m => (Function.update (fun _ : Fin (m+1) => []) k.succ x) i.succ)=
          Function.update (fun _ : Fin m => []) k x := by
        funext i;by_cases h : i=k <;> simp [h]
      rw [List.ofFn_succ,h0,ht,CompactStacks.words_cons,ih]
      simp only [CompactStacks.block_nil,Fin.val_succ,List.replicate_succ,List.cons_append]
      have he : m+1-(k.val+1)-1=m-k.val-1 := by omega
      rw [he,List.nil_append]
lemma layout_eq_words {m : ℕ} (j : Fin m) (x : List Bool) :
    layout m j.val x=CompactStacks.words (CompactStacks.registers (Function.update (fun _ : Fin m => []) j x.reverse)) := by
  have he : (fun k => (Function.update (fun _ : Fin m => []) j x.reverse k).reverse)=
      Function.update (fun _ : Fin m => []) j x := by
    funext k;by_cases h : k=j <;> simp [h]
  rw [CompactStacks.registers,he,words_single]
  have hj : m-j.val=(m-j.val-1)+1 := by have := j.isLt;omega
  unfold layout CompactStacks.block
  change List.replicate j.val false++pairs x++List.replicate (m-j.val) false =
    List.replicate j.val false++(pairs x++[false])++List.replicate (m-j.val-1) false
  conv_lhs => rw [hj,List.replicate_succ]
  simp only [List.append_assoc,List.singleton_append]
end SourceBurnside.CompactInit

namespace SourceBurnside.FixedArity
noncomputable section
open StackMachine Structured Structured.Program Structured.Binary
variable {A B Q Q' : Type*} [DecidableEq A] [DecidableEq B]
def renameInstr (e : A ≃ B) : Instr A Bool Q → Instr B Bool Q
  | .halt => .halt
  | .push k b q => .push (e k) b q
  | .pop k f => .pop (e k) f
def renameConfig (e : A ≃ B) (C : Config A Bool Q) : Config B Bool Q := ⟨C.state,C.store ∘ e.symm⟩
def rename (e : A ≃ B) (P : Q → Instr A Bool Q) : Q → Instr B Bool Q := fun q => renameInstr e (P q)
lemma update_comp (e : A ≃ B) (r : A → List Bool) (k : A) (v : List Bool) :
    (Function.update r k v) ∘ e.symm=Function.update (r ∘ e.symm) (e k) v := by
  funext j
  by_cases h : j=e k
  · subst j;simp
  · have h' : e.symm j≠k := by intro H;apply h;rw [←H,Equiv.apply_symm_apply]
    simp [h,h']
lemma rename_next (e : A ≃ B) (P : Q → Instr A Bool Q) (C : Config A Bool Q) :
    next (rename e P) (renameConfig e C)=renameConfig e (next P C) := by
  cases h : P C.state <;> simp [next,rename,renameConfig,renameInstr,h,update_comp]
lemma rename_exec (e : A ≃ B) (P : Q → Instr A Bool Q) (C : Config A Bool Q) (n : ℕ) :
    exec (rename e P) (renameConfig e C) n=renameConfig e (exec P C n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [exec,ih,rename_next]
def liftInstr (f : Q → Q') : Instr A Bool Q → Instr (Option A) Bool Q'
  | .halt => .halt
  | .push k b q => .push (some k) b (f q)
  | .pop k g => .pop (some k) (fun b => f (g b))
def liftConfig (f : Q → Q') (C : Config A Bool Q) : Config (Option A) Bool Q' := ⟨f C.state,extendStore C.store⟩
lemma lift_next (P : Q → Instr A Bool Q) (M : Q' → Instr (Option A) Bool Q') (f : Q → Q')
    (hf : ∀q,M (f q)=liftInstr f (P q)) (C : Config A Bool Q) :
    next M (liftConfig f C)=liftConfig f (next P C) := by
  cases h : P C.state <;> simp [next,liftConfig,hf,liftInstr,h,extendStore_update,extendStore]
lemma lift_exec (P : Q → Instr A Bool Q) (M : Q' → Instr (Option A) Bool Q') (f : Q → Q')
    (hf : ∀q,M (f q)=liftInstr f (P q)) (C : Config A Bool Q) (n : ℕ) :
    exec M (liftConfig f C) n=liftConfig f (exec P C n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [exec,ih,lift_next P M f hf];rfl
abbrev AnswerState (P : Program A) := Option P.Loc ⊕ Bool
def answerMachine (P : Program A) (out : A) : AnswerState P → Instr (Option A) Bool (AnswerState P)
  | .inl (some l) => mapInstr Sum.inl (P.operation l)
  | .inl none => .pop (some out) (fun b => .inr (b.getD false))
  | .inr _ => .halt
lemma answer_trace {P : Program A} {r s : Store A} {n : ℕ} (h : Run P r n s) (out : A) :
    exec (answerMachine P out) ⟨.inl (some P.start),extendStore r⟩ (n+1)=
      ⟨.inr ((s out).getLast?.getD false),Function.update (extendStore s) (some out) (s out).dropLast⟩ := by
  have H := compile_run h (answerMachine P out) Sum.inl (by intro l;rfl)
  rw [exec,H]
  rfl
lemma output_bit (y : List Bool) : Add.bit (y.getLast?.getD false)=Add.value y.reverse%2 := by
  rw [←List.head?_reverse]
  generalize y.reverse=z
  cases z with
  | nil => rfl
  | cons b z => cases b <;> simp [Add.value,Add.bit]
end
end SourceBurnside.FixedArity

namespace SourceBurnside.CompactProgram
noncomputable section
open StackMachine Structured Structured.Program FixedArity
variable {A : Type*} [DecidableEq A] {m : ℕ}
local instance (P : Program A) : DecidableEq (AnswerState P) := Classical.decEq _
def inputStore (j : A) (x : List Bool) : Store A := Function.update (fun _ => []) j x.reverse
def virtual (e : Option A ≃ Fin m) (P : Program A) (out : A) := rename e (answerMachine P out)
def initial (e : Option A ≃ Fin m) (P : Program A) (j : A) (x : List Bool) :=
  renameConfig e (⟨.inl (some P.start),extendStore (inputStore j x)⟩ : Config (Option A) Bool (AnswerState P))
def boot (e : Option A ≃ Fin m) (j : A) := CompactInit.program m (e (some j)).val
abbrev State (e : Option A ≃ Fin m) (P : Program A) (j : A) :=
  (boot e j).Loc ⊕ CompactStacks.State m (AnswerState P)
def enter (e : Option A ≃ Fin m) (P : Program A) (j : A) : Option (boot e j).Loc → State e P j
  | some l => .inl l
  | none => .inr (.start (.inl (some P.start)))
def machine (e : Option A ≃ Fin m) (P : Program A) (j out : A) :
    State e P j → Instr (Option (Fin 2)) Bool (State e P j)
  | .inl l => mapInstr (enter e P j) ((boot e j).operation l)
  | .inr q => liftInstr Sum.inr (CompactStacks.machine (virtual e P out) q)
def initialConfig (e : Option A ≃ Fin m) (P : Program A) (j : A) (x : List Bool) :
    Config (Option (Fin 2)) Bool (State e P j) :=
  ⟨.inl (boot e j).start,extendStore (CompactInit.store x [])⟩
def bootTime (e : Option A ≃ Fin m) (j : A) (x : List Bool) :=
  ((e (some j)).val+1)+(3*x.length+1)+((m-(e (some j)).val+1)+
    (2*(CompactInit.layout m (e (some j)).val x).length+1))
lemma initial_store (e : Option A ≃ Fin m) (P : Program A) (j : A) (x : List Bool) :
    (initial e P j x).store=Function.update (fun _ => []) (e (some j)) x.reverse := by
  change (extendStore (Function.update (fun _ => []) j x.reverse)) ∘ e.symm=_
  rw [extendStore_update,update_comp]
  congr 1
  funext a
  simp only [Function.comp_apply]
  cases e.symm a <;> simp [extendStore]
lemma boot_trace (e : Option A ≃ Fin m) (P : Program A) (j out : A) (x : List Bool) :
    exec (machine e P j out) (initialConfig e P j x) (bootTime e j x)=
      liftConfig Sum.inr (CompactStacks.encode (initial e P j x)) := by
  have H := compile_run (CompactInit.program_run m (e (some j)).val x)
    (machine e P j out) (enter e P j) (by intro l;rfl)
  change exec (machine e P j out) (initialConfig e P j x) (bootTime e j x)=_ at H
  rw [H]
  congr 1
  simp only [CompactStacks.encode,CompactStacks.config]
  rw [initial_store]
  change extendStore (CompactInit.store (CompactInit.layout m (e (some j)).val x) [])=
    extendStore ![(CompactStacks.words (CompactStacks.registers (Function.update (fun _ => []) (e (some j)) x.reverse))).reverse,[]]
  rw [CompactInit.layout_eq_words]
  rfl
lemma execution (e : Option A ≃ Fin m) (P : Program A) (j out : A) (x : List Bool) (n : ℕ) :
    exec (machine e P j out) (initialConfig e P j x)
      (bootTime e j x+CompactStacks.clock (virtual e P out) (initial e P j x) n)=
      liftConfig Sum.inr (CompactStacks.encode (exec (virtual e P out) (initial e P j x) n)) := by
  rw [UniversalStack.exec_from,boot_trace,
    lift_exec (CompactStacks.machine (virtual e P out)) (machine e P j out) Sum.inr (by intro q;rfl),
    CompactStacks.encode_exec]
lemma initial_length (e : Option A ≃ Fin m) (P : Program A) (j : A) (x : List Bool) (k : Fin m) :
    ((initial e P j x).store k).length ≤ x.length := by
  rw [initial_store]
  by_cases h : k=e (some j) <;> simp [h]
lemma time_bound (e : Option A ≃ Fin m) (P : Program A) (j out : A) (x : List Bool) (n : ℕ) :
    bootTime e j x+CompactStacks.clock (virtual e P out) (initial e P j x) n ≤
      3*m+7*x.length+4+n*(4*m*(2*(x.length+n)+1)+3) := by
  have hb := CompactInit.program_time_le (Nat.le_of_lt (e (some j)).isLt) x
  have hc := CompactStacks.clock_bound (virtual e P out) (initial e P j x) x.length (initial_length e P j x) n
  exact Nat.add_le_add hb hc
lemma answer_execution (e : Option A ≃ Fin m) {P : Program A} (j out : A) (x : List Bool)
    {n : ℕ} {s : Store A} (h : Run P (inputStore j x) n s) :
    (exec (machine e P j out) (initialConfig e P j x)
      (bootTime e j x+CompactStacks.clock (virtual e P out) (initial e P j x) (n+1))).state=
      .inr (.start (.inr ((s out).getLast?.getD false))) := by
  rw [execution]
  apply congrArg (fun q => Sum.inr (CompactStacks.State.start q))
  rw [show exec (virtual e P out) (initial e P j x) (n+1)=
    renameConfig e (exec (answerMachine P out) ⟨.inl (some P.start),extendStore (inputStore j x)⟩ (n+1)) from
      rename_exec e _ _ _,answer_trace h out]
  rfl
omit [DecidableEq A] in
lemma halted (e : Option A ≃ Fin m) (P : Program A) (j out : A) (b : Bool) :
    machine e P j out (.inr (.start (.inr b)))=.halt := rfl
end
end SourceBurnside.CompactProgram

end

end OAI
