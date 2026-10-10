import Mathlib
import OAI.GroupTheory.PeriodicGroups.Formulas.PredicateCompilation

namespace OAI

section
universe u v w
namespace SourceBurnside.LocalBody
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured Structured.Device Structured.Device.Formula

abbrev Registers := Fin 9
def code : Formula Registers := .read 0
def codeLength : Formula Registers := .read 1
def height : Formula Registers := .read 2
def arity : Formula Registers := .read 3
def zeroTask : Formula Registers := .read 4
def word (b : Bool) (i : Fin 2) : Formula Registers :=
  .read ⟨5+(if b then 2 else 0)+i.val,by have := i.isLt;split <;> omega⟩
def time : Formula Registers := .powTwo (.div height (.constant 5))
def width : Formula Registers := .mul (.constant 4) time
def origin : Formula Registers := .mul (.constant 2) time
def size (D : ℕ) : Formula Registers := .mul (.constant (10000*D)) height
def bound : Formula Registers := .powTwo height
def nextHeight (D : ℕ) : Formula Registers := .mul (.constant D) height
def table (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) : PredicateFormula.Table (ι:=Registers) :=
  PredicateFormula.physical β g c output blank initial accept encoding time width origin code codeLength (nextHeight D)
def body (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) : Formula Registers :=
  PredicateFormula.normalEntry (table β g D c output blank initial accept encoding) height (size D) bound arity zeroTask word

def exponentLimit (D h n : ℕ) : ℕ := 10000*(D+1)*(h+1)+n+32
lemma limit_height (D h n : ℕ) : 64*h+8≤exponentLimit D h n := by unfold exponentLimit;nlinarith
lemma limit_code (D h n : ℕ) : n≤exponentLimit D h n := by unfold exponentLimit;omega
lemma limit_next (D h n : ℕ) : D*h≤exponentLimit D h n := by unfold exponentLimit;nlinarith
lemma body_exponents (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Registers → ℕ) :
    (body β g D c output blank initial accept encoding).Exponents (exponentLimit D (v 2) (v 1)) v := by
  let M := exponentLimit D (v 2) (v 1)
  have hM : 64*v 2+8≤M := limit_height D (v 2) (v 1)
  have ht : time.Exponents M v := ⟨⟨trivial,trivial⟩,by change v 2 / 5≤M;exact (Nat.div_le_self _ _).trans (by omega)⟩
  apply PredicateFormula.normalEntry_exponents
  · apply PredicateFormula.physical_exponents β g c output blank initial accept encoding (by omega)
    · exact ht
    · exact ⟨trivial,ht⟩
    · exact ⟨trivial,ht⟩
    · trivial
    · trivial
    · exact ⟨trivial,trivial⟩
    · exact limit_code D (v 2) (v 1)
    · exact limit_next D (v 2) (v 1)
  · trivial
  · exact ⟨trivial,trivial⟩
  · exact ⟨trivial,by change v 2≤M;omega⟩
  · trivial
  · trivial
  · intro b i;trivial
  · exact hM

def inputs {h : ℕ} (a : List Bool) (l : Fin 3) (z : Bool) (data : Bool → Fin 2 → Raw h) : Registers → ℕ :=
  ![binaryValue a,a.length,h,l.val,boolean z,natCode (data false 0),natCode (data false 1),natCode (data true 0),natCode (data true 1)]
lemma inputs_bounded {h : ℕ} (D : ℕ) (a : List Bool) (l : Fin 3) (z : Bool) (data : Bool → Fin 2 → Raw h) :
    ∀i,inputs a l z data i<2^(exponentLimit D h a.length+1) := by
  have hM := limit_height D h a.length
  have hd : 10000*h≤exponentLimit D h a.length+1 := by unfold exponentLimit;nlinarith
  have hn : a.length≤exponentLimit D h a.length+1 := (limit_code D h a.length).trans (by omega)
  have hp : 2<2^(exponentLimit D h a.length+1) := by
    have h : 2≤exponentLimit D h a.length+1 := by unfold exponentLimit;omega
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by omega) h)
  intro i;fin_cases i
  · exact (binaryValue_lt a).trans_le (Nat.pow_le_pow_right (by omega) hn)
  · exact (limit_code D h a.length).trans_lt (lt_trans (Nat.lt_succ_self _) Nat.lt_two_pow_self)
  · exact (show h<exponentLimit D h a.length+1 by omega).trans Nat.lt_two_pow_self
  · exact l.isLt.trans_le (by omega)
  · change boolean z<_;cases z <;> simp only [boolean,Bool.false_eq_true,ite_false,ite_true] <;> omega
  all_goals exact (natCode_lt _).trans_le (Nat.pow_le_pow_right (by omega) hd)

theorem body_trace (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) :
    let e := body β g D c output blank initial accept encoding
    ∃R : Realizer e.totalize.eval (fun n v => e.totalize.Safe n v),
      ∀ {h : ℕ} (a : List Bool) (l : Fin 3) (z : Bool) (data : Bool → Fin 2 → Raw h),
        let M := exponentLimit D h a.length
        let n := e.weight*(M+1)
        let xs := packedInputs n (inputs a l z data)
        ∃t y,t≤R.coefficient*(n+1)^2 ∧ y.length=n ∧
          Binary.Add.value y.reverse=e.eval (inputs a l z data) ∧ Run R.program (input xs) t (result xs R.out y) := by
  dsimp only
  let e := body β g D c output blank initial accept encoding
  obtain ⟨R,hR⟩ := timed_total (0:Registers) e
  refine ⟨R,?_⟩
  intro h a l z data
  let M := exponentLimit D h a.length
  let n := e.weight*(M+1)
  have hn : M+1≤n := by have := e.weight_pos;dsimp [n];nlinarith
  have hv := inputs_bounded D a l z data
  have H := hR M (packedInputs n (inputs a l z data))
    (packedInputs_lengths _ _ (fun i => (hv i).trans_le (Nat.pow_le_pow_right (by omega) hn)))
    (by simpa only [packedInputs_values] using hv)
    (by rw [packedInputs_values];exact body_exponents β g D c output blank initial accept encoding (inputs a l z data))
  simpa only [packedInputs_values] using H
end SourceBurnside.LocalBody

namespace SourceBurnside.HeaderProgram
open Structured Structured.Program Structured.Binary
abbrev K := Fin 4

def store (todo : List Bool) (count : ℕ) (out ctl : List Bool) : Store K :=
  ![todo.reverse,List.replicate count true,out,ctl]
def step : Program K := .pop 0 (fun a =>
  if a=some true then .seq (.push 1 true) (.push 3 true) else .skip)
def scanPrefix : Program K := .loop 3 (fun _ => step)
def digit : Program K := .pop 0 (fun a => match a with
  | some b => .push 2 b | none => .skip)
def digits : Program K := .loop 1 (fun _ => digit)
def program : Program K := .seq (.push 3 true) (.seq scanPrefix digits)
lemma step_true (todo out : List Bool) (n : ℕ) :
    Run step (store (true::todo) n out []) 3 (store todo (n+1) out [true]) := by
  refine Run.pop _ _ _ 2 _ ?_
  have h : store (true::todo) n out [] 0=todo.reverse++[true] := by simp [store]
  have he : Function.update (store (true::todo) n out []) 0 todo.reverse=store todo n out [] := by
    funext i;fin_cases i <;> simp [store]
  simp only [h,List.getLast?_concat,List.dropLast_concat,he,ite_true]
  have H := Run.seq (.push (1:K) true) (.push 3 true) (store todo n out []) _ _ 1 1
    (Run.push _ _ _) (Run.push _ _ _)
  convert H using 1
  funext i;fin_cases i <;> simp [store,List.replicate_add]
lemma step_false (todo out : List Bool) (n : ℕ) :
    Run step (store (false::todo) n out []) 2 (store todo n out []) := by
  refine Run.pop _ _ _ 1 _ ?_
  have h : store (false::todo) n out [] 0=todo.reverse++[false] := by simp [store]
  have he : Function.update (store (false::todo) n out []) 0 todo.reverse=store todo n out [] := by
    funext i;fin_cases i <;> simp [store]
  simpa only [h,List.getLast?_concat,List.dropLast_concat,he,Bool.false_eq_true,
    Option.some.injEq,ite_false] using Run.skip (store todo n out [])
lemma prefix_run (k : ℕ) (todo out : List Bool) (n : ℕ) :
    Run scanPrefix (store (List.replicate k true++false::todo) n out [true]) (4*k+4)
      (store todo (n+k) out []) := by
  induction k generalizing n with
  | zero =>
    have he : Function.update (store (false::todo) n out [true]) 3 []=store (false::todo) n out [] := by
      funext i;fin_cases i <;> simp [store]
    have H := Run.loop_cons (store (false::todo) n out [true]) (3:K) (fun _ => step) [] true
      (store todo n out []) (store todo n out []) 2 1 rfl
      (by rw [he];exact step_false todo out n) (Run.loop_nil _ _ _ rfl)
    simpa [scanPrefix] using H
  | succ k ih =>
    let rest := List.replicate k true++false::todo
    have he : Function.update (store (true::rest) n out [true]) 3 []=store (true::rest) n out [] := by
      funext i;fin_cases i <;> simp [store]
    have H := Run.loop_cons (store (true::rest) n out [true]) (3:K) (fun _ => step) [] true
      (store rest (n+1) out [true]) (store todo (n+1+k) out []) 3 (4*k+4) rfl
      (by rw [he];exact step_true rest out n) (ih (n+1))
    convert H using 1 <;> try simp only [scanPrefix,List.replicate_succ,List.cons_append,rest]
    all_goals first | omega | (congr 1; omega)
lemma digit_run (b : Bool) (todo out : List Bool) (n : ℕ) :
    Run digit (store (b::todo) n out []) 2 (store todo n (out++[b]) []) := by
  refine Run.pop _ _ _ 1 _ ?_
  have h : store (b::todo) n out [] 0=todo.reverse++[b] := by simp [store]
  have he : Function.update (store (b::todo) n out []) 0 todo.reverse=store todo n out [] := by
    funext i;fin_cases i <;> simp [store]
  simp only [h,List.getLast?_concat,List.dropLast_concat,he]
  convert Run.push (store todo n out []) (2:K) b using 1
  funext i;fin_cases i <;> simp [store]
lemma digits_run (bits todo out : List Bool) :
    Run digits (store (bits++todo) bits.length out []) (3*bits.length+1) (store todo 0 (out++bits) []) := by
  induction bits generalizing out with
  | nil => simpa [digits] using Run.loop_nil (store todo 0 out []) (1:K) (fun _ => digit) rfl
  | cons b bits ih =>
    have he : Function.update (store (b::bits++todo) (bits.length+1) out []) 1
        (List.replicate bits.length true)=store (b::bits++todo) bits.length out [] := by
      funext i;fin_cases i <;> simp [store]
    have H := Run.loop_cons (store (b::bits++todo) (bits.length+1) out []) (1:K) (fun _ => digit)
      (List.replicate bits.length true) true (store (bits++todo) bits.length (out++[b]) [])
      (store todo 0 ((out++[b])++bits) []) 2 (3*bits.length+1)
      (by simp [store,List.replicate_add])
      (by rw [he];exact digit_run b (bits++todo) out bits.length) (ih (out++[b]))
    convert H using 1 <;> simp only [digits,List.length_cons,List.cons_append,List.append_assoc,List.nil_append]
    omega

theorem header_run (bits todo : List Bool) :
    Run program (store (UniversalInput.header bits++todo) 0 [] []) (7*bits.length+6)
      (store todo 0 bits []) := by
  let src := UniversalInput.header bits++todo
  have h1 := Run.push (store src 0 [] []) (3:K) true
  have he : Function.update (store src 0 [] []) 3 ((store src 0 [] [] 3)++[true])=store src 0 [] [true] := by
    funext i;fin_cases i <;> simp [store]
  rw [he] at h1
  have h2 : Run scanPrefix (store src 0 [] [true]) (4*bits.length+4) (store (bits++todo) bits.length [] []) := by
    simpa [src,UniversalInput.header,List.append_assoc] using prefix_run bits.length (bits++todo) [] 0
  have h3 : Run digits (store (bits++todo) bits.length [] []) (3*bits.length+1) (store todo 0 bits []) := by
    simpa only [List.nil_append] using digits_run bits todo []
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega
end SourceBurnside.HeaderProgram

namespace SourceBurnside.FiniteTable.Codec
open Structured.Binary
lemma binaryValue_eq (bs : List Bool) : binaryValue bs=Add.value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [binaryValue,BitVec.ofBoolListLE,BitVec.toNat_concat] at *
    cases b <;> simp [Add.value,Add.bit,ih] <;> omega
lemma binaryValue_append (as bs : List Bool) :
    binaryValue (as++bs)=binaryValue as+2^as.length*binaryValue bs := by
  simp only [binaryValue_eq,Add.value_append]
lemma binaryValue_prefix (as bs : List Bool) :
    binaryValue (as++bs)%2^as.length=binaryValue as := by
  rw [binaryValue_append,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (binaryValue_lt _)]
lemma binaryValue_suffix (as bs : List Bool) :
    binaryValue (as++bs)/2^as.length=binaryValue bs := by
  rw [binaryValue_append,Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt (binaryValue_lt _),Nat.zero_add]
lemma binaryValue_slice (as ds bs : List Bool) :
    binaryValue (as++ds++bs)/2^as.length%2^ds.length=binaryValue ds := by
  rw [List.append_assoc,binaryValue_suffix,binaryValue_prefix]
end SourceBurnside.FiniteTable.Codec

namespace SourceBurnside.InitialFormula
open FiniteTable.Codec Structured.Binary
lemma bin_value (n : ℕ) : Add.value (bin n).reverse=n := by
  rw [←binaryValue_eq]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [binaryValue_bit]
  by_cases hk : k<binSize n
  · have hr : k<(bin n).reverse.length := by simpa using hk
    rw [List.getD_eq_getElem _ _ hr,List.getElem_reverse]
    simp only [bin,List.length_ofFn,List.getElem_ofFn]
    congr 1
    omega
  · have hz : (bin n).reverse.getD k false=false := List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hk)
    rw [hz,eq_comm]
    apply Nat.testBit_eq_false_of_lt
    have hs : n<2^(binSize n) := by
      by_cases hn : n=0
      · simp [hn,binSize]
      · simpa [binSize,hn] using Nat.lt_size_self n
    exact hs.trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hk))
end SourceBurnside.InitialFormula

namespace SourceBurnside.RawHeader
open Structured Structured.Program Structured.Binary
abbrev K := Fin 6
def store (todo h l z : List Bool) : Store K := ![todo.reverse,[],h,[],l,z]
def heightSlots : Fin 4 → K := ![0,1,2,3]
def aritySlots : Fin 4 → K := ![0,1,4,3]
lemma heightSlots_injective : Function.Injective heightSlots := by decide
lemma aritySlots_injective : Function.Injective aritySlots := by decide
def readTask : Program K := .pop 0 (fun a => match a with | some b => .push 5 b | none => .skip)
def program : Program K := .seq (HeaderProgram.program.relabel heightSlots)
  (.seq (HeaderProgram.program.relabel aritySlots) readTask)
lemma height_run (bits todo l z : List Bool) :
    Run (HeaderProgram.program.relabel heightSlots) (store (UniversalInput.header bits++todo) [] l z)
      (7*bits.length+6) (store todo bits l z) := by
  refine (HeaderProgram.header_run bits todo).relabel_to heightSlots heightSlots_injective _ _ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 2 rfl)
    · exact False.elim (hi 3 rfl)
    · rfl
    · rfl
lemma arity_run (bits todo h z : List Bool) :
    Run (HeaderProgram.program.relabel aritySlots) (store (UniversalInput.header bits++todo) h [] z)
      (7*bits.length+6) (store todo h bits z) := by
  refine (HeaderProgram.header_run bits todo).relabel_to aritySlots aritySlots_injective _ _ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 1 rfl)
    · rfl
    · exact False.elim (hi 3 rfl)
    · exact False.elim (hi 2 rfl)
    · rfl
lemma task_run (z : Bool) (todo h l : List Bool) :
    Run readTask (store (z::todo) h l []) 2 (store todo h l [z]) := by
  refine Run.pop _ _ _ 1 _ ?_
  have he : Function.update (store (z::todo) h l []) 0 todo.reverse=store todo h l [] := by
    funext i;fin_cases i <;> simp [store]
  have hs : store (z::todo) h l [] 0=todo.reverse++[z] := by simp [store]
  simp only [hs,List.getLast?_concat,List.dropLast_concat,he]
  convert Run.push (store todo h l []) (5:K) z using 1
  funext i;fin_cases i <;> simp [store]

def request (h l : ℕ) (z : Bool) (data : List Bool) :=
  InitialFormula.enc h++InitialFormula.enc l++z::data
lemma program_run (h l : ℕ) (z : Bool) (data : List Bool) :
    Run program (store (request h l z data) [] [] [])
      (7*(InitialFormula.binSize h+InitialFormula.binSize l)+14)
      (store data (InitialFormula.bin h) (InitialFormula.bin l) [z]) := by
  have h1 := height_run (InitialFormula.bin h) (InitialFormula.enc l++z::data) [] []
  have h2 := arity_run (InitialFormula.bin l) (z::data) (InitialFormula.bin h) []
  have h3 := task_run z data (InitialFormula.bin h) (InitialFormula.bin l)
  have hh (n : ℕ) : UniversalInput.header (InitialFormula.bin n)=InitialFormula.enc n := by simp [UniversalInput.header,InitialFormula.enc]
  simp only [hh,InitialFormula.bin_length] at h1 h2
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | simp [request,List.append_assoc] | omega
lemma parsed_values (h l : ℕ) (z : Bool) (data : List Bool) :
    let r := store data (InitialFormula.bin h) (InitialFormula.bin l) [z]
    Binary.Add.value (r 0).reverse=FiniteTable.Codec.binaryValue data ∧
    Binary.Add.value (r 2).reverse=h ∧ Binary.Add.value (r 4).reverse=l ∧
      Binary.Add.value (r 5).reverse=CellRepr.boolean z := by
  dsimp [store]
  simp only [List.reverse_reverse,←FiniteTable.Codec.binaryValue_eq]
  rw [FiniteTable.Codec.binaryValue_eq (InitialFormula.bin h).reverse,
    FiniteTable.Codec.binaryValue_eq (InitialFormula.bin l).reverse]
  simp only [InitialFormula.bin_value,true_and]
  cases z <;> rfl
end SourceBurnside.RawHeader

namespace SourceBurnside.BinaryUnary
open Structured Structured.Program Structured.Binary
abbrev K := Fin 4
def store (bits : List Bool) (n : ℕ) : Store K := ![bits.reverse,List.replicate n false,[],[]]
def lastBit (b : Bool) : Program K := if b then .push 1 false else .skip
def step (b : Bool) : Program K := .seq (copy 1 2 3) (.seq (move 2 1) (lastBit b))
def program : Program K := .loop 0 step
lemma step_run (b : Bool) (bits : List Bool) (n : ℕ) :
    Run (step b) (store bits n) (7*n+4) (store bits (2*n+Add.bit b)) := by
  let r := store bits n
  let s := Function.update r (2:K) (List.replicate n false)
  have h1 : Run (copy (1:K) 2 3) r (5*n+2) s := by
    simpa [r,s,store] using copy_run (1:K) 2 3 (by decide) (by decide) (by decide) r (by rfl)
  have h2 := move_run (2:K) 1 (by decide) s
  have he : Function.update (Function.update s 2 []) 1 (s 1++(s 2).reverse)=store bits (2*n) := by
    funext i;fin_cases i <;> simp [s,r,store,two_mul]
  rw [he] at h2
  have hl : (s 2).length=n := by simp [s]
  rw [hl] at h2
  have h3 : Run (lastBit b) (store bits (2*n)) 1 (store bits (2*n+Add.bit b)) := by
    cases b
    · simpa [lastBit,Add.bit] using Run.skip (store bits (2*n))
    · convert Run.push (store bits (2*n)) (1:K) false using 1 <;> try rfl
      funext i;fin_cases i <;> simp [store,Add.bit,List.replicate_add]
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 h3)
  convert H using 1 <;> first | rfl | omega
lemma feed_ge (n : ℕ) (bits : List Bool) : n≤Divide.feed n bits := by
  rw [Divide.feed_value]
  have hp : 1≤2^bits.length := Nat.one_le_pow _ _ (by omega)
  nlinarith
lemma program_run (bits : List Bool) (n : ℕ) :
    ∃t,t≤(7*Divide.feed n bits+5)*bits.length+1 ∧
      Run program (store bits n) t (store [] (Divide.feed n bits)) := by
  induction bits generalizing n with
  | nil => exact ⟨1,by simp,Run.loop_nil _ _ _ rfl⟩
  | cons b bits ih =>
    obtain ⟨t,ht,hT⟩ := ih (2*n+Add.bit b)
    have he : Function.update (store (b::bits) n) 0 bits.reverse=store bits n := by
      funext i;fin_cases i <;> simp [store]
    have H := Run.loop_cons (store (b::bits) n) (0:K) step bits.reverse b
      (store bits (2*n+Add.bit b)) (store [] (Divide.feed (2*n+Add.bit b) bits)) (7*n+4) t
      (by simp [store]) (by rw [he];exact step_run b bits n) hT
    refine ⟨1+(7*n+4+t),?_,?_⟩
    · have hn : n≤Divide.feed (2*n+Add.bit b) bits :=
        (show n≤2*n+Add.bit b by omega).trans (feed_ge _ _)
      simp only [Divide.feed,List.length_cons]
      nlinarith
    · convert H using 1 <;> rfl

theorem numeral_run (n : ℕ) :
    ∃t,t≤(7*n+5)*InitialFormula.binSize n+1 ∧
      Run program (store (InitialFormula.bin n) 0) t (store [] n) := by
  have h : Divide.feed 0 (InitialFormula.bin n)=n := by
    simp [Divide.feed_value,InitialFormula.bin_value]
  simpa only [h,InitialFormula.bin_length] using program_run (InitialFormula.bin n) 0
end SourceBurnside.BinaryUnary

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]
def pushes (dst : K) : ℕ → Program K
  | 0 => .skip
  | n+1 => .seq (.push dst false) (pushes dst n)
lemma pushes_run (dst : K) (n : ℕ) (r : Store K) :
    Run (pushes dst n) r (n+1) (Function.update r dst (r dst++List.replicate n false)) := by
  induction n generalizing r with
  | zero => simpa [pushes] using Run.skip r
  | succ n ih =>
    let s := Function.update r dst (r dst++[false])
    have H := Run.seq (.push dst false) (pushes dst n) r s _ 1 (n+1)
      (Run.push _ _ _) (ih s)
    have he : Function.update s dst (s dst++List.replicate n false)=
        Function.update r dst (r dst++List.replicate (n+1) false) := by
      simp only [s,Function.update_self,Function.update_idem,List.replicate_succ,List.append_assoc,List.singleton_append]
    rw [he] at H
    convert H using 1 <;> first | rfl | omega

def inflate (src dst : K) (n : ℕ) : Program K := .loop src (fun _ => pushes dst n)
lemma inflate_run (src dst : K) (hne : src≠dst) (n : ℕ) (r : Store K) :
    Run (inflate src dst n) r ((n+2)*(r src).length+1)
      (Function.update (Function.update r src []) dst (r dst++List.replicate (n*(r src).length) false)) := by
  generalize hv : r src=v
  induction v using List.reverseRecOn generalizing r with
  | nil =>
    have he : Function.update (Function.update r src []) dst (r dst++List.replicate (n*0) false)=r := by
      simp [←hv]
    rw [List.length_nil,he]
    simpa [inflate] using Run.loop_nil r src (fun _ => pushes dst n) hv
  | append_singleton v b ih =>
    let s := Function.update r src v
    let t := Function.update s dst (s dst++List.replicate n false)
    have ht : t src=v := by simp [t,s,hne]
    have hh := ih t ht
    have H := Run.loop_cons r src (fun _ => pushes dst n) v b t _ (n+1) ((n+2)*v.length+1) hv
      (pushes_run dst n s) hh
    have he : Function.update (Function.update t src []) dst (t dst++List.replicate (n*v.length) false)=
        Function.update (Function.update r src []) dst (r dst++List.replicate (n*(v++[b]).length) false) := by
      funext k
      by_cases hd : k=dst
      · subst k
        simp [t,s,Ne.symm hne,List.append_assoc,Nat.mul_add,Nat.add_comm]
      · by_cases hs : k=src
        · subst k;simp [hd]
        · simp [t,s,hd,hs]
    rw [he] at H
    convert H using 1 <;> first | rfl | simp [List.length_append,Nat.mul_add];omega
end SourceBurnside.Structured.Binary

namespace SourceBurnside.DropPadding
open Structured Structured.Program Structured.Binary
abbrev K := Fin 2
def store (xs : List Bool) (n : ℕ) : Store K := ![xs,List.replicate n false]
def step : Program K := .pop 1 (fun _ => .skip)
def program : Program K := .loop 0 (fun _ => step)
lemma program_run (xs : List Bool) (n : ℕ) :
    Run program (store xs (xs.length+n)) (3*xs.length+1) (store [] n) := by
  induction xs using List.reverseRecOn with
  | nil => simpa [program] using Run.loop_nil (store [] n) (0:K) (fun _ => step) rfl
  | append_singleton xs b ih =>
    have he0 : Function.update (store (xs++[b]) ((xs++[b]).length+n)) 0 xs=store xs (xs.length+n+1) := by
      funext i;fin_cases i <;> simp [store,Nat.add_assoc,Nat.add_comm]
    have he1 : Function.update (store xs (xs.length+n+1)) 1 (List.replicate (xs.length+n) false)=store xs (xs.length+n) := by
      funext i;fin_cases i <;> simp [store]
    have hs : store xs (xs.length+n+1) 1=List.replicate (xs.length+n) false++[false] := by
      change List.replicate ((xs.length+n)+1) false=_
      rw [List.replicate_add];rfl
    have hb : Run step (store xs (xs.length+n+1)) 2 (store xs (xs.length+n)) := by
      refine Run.pop _ _ _ 1 _ ?_
      simp only [hs,List.dropLast_concat,he1]
      exact Run.skip _
    have H := Run.loop_cons (store (xs++[b]) ((xs++[b]).length+n)) (0:K) (fun _ => step) xs b
      (store xs (xs.length+n)) (store [] n) 2 (3*xs.length+1) rfl (by rw [he0];exact hb) ih
    convert H using 1 <;> first | rfl | simp;omega
end SourceBurnside.DropPadding

namespace SourceBurnside.PadRegister
open Structured Structured.Program Structured.Binary
abbrev K := Fin 5
def store (xs : List Bool) (n : ℕ) (out aux : List Bool) : Store K :=
  ![xs,List.replicate n false,out,[],aux]
def dropSlots : Fin 2 → K := ![4,2]
lemma dropSlots_injective : Function.Injective dropSlots := by decide
def program : Program K := .seq (copy 1 2 3) (.seq (copy 0 4 3)
  (.seq (DropPadding.program.relabel dropSlots) (copy 0 2 3)))
lemma program_run (xs : List Bool) (n : ℕ) (hn : xs.length≤n) :
    Run program (store xs n [] []) (5*n+13*xs.length+7)
      (store xs n (List.replicate (n-xs.length) false++xs) []) := by
  have h1 := copy_run (1:K) 2 3 (by decide) (by decide) (by decide) (store xs n [] []) (by rfl)
  have he1 : Function.update (store xs n [] []) 2 ((store xs n [] [] 2)++(store xs n [] [] 1))=
      store xs n (List.replicate n false) [] := by
    funext i;fin_cases i <;> simp [store]
  rw [he1] at h1
  have hl1 : (store xs n [] [] 1).length=n := by simp [store]
  rw [hl1] at h1
  have h2 := copy_run (0:K) 4 3 (by decide) (by decide) (by decide) (store xs n (List.replicate n false) []) (by rfl)
  have he2 : Function.update (store xs n (List.replicate n false) []) 4
      ((store xs n (List.replicate n false) [] 4)++(store xs n (List.replicate n false) [] 0))=
      store xs n (List.replicate n false) xs := by
    funext i;fin_cases i <;> simp [store]
  rw [he2] at h2
  have h3 : Run (DropPadding.program.relabel dropSlots) (store xs n (List.replicate n false) xs)
      (3*xs.length+1) (store xs n (List.replicate (n-xs.length) false) []) := by
    refine (DropPadding.program_run xs (n-xs.length)).relabel_to dropSlots dropSlots_injective _ _ ?_ ?_ ?_
    · intro i;fin_cases i
      · rfl
      · simp [DropPadding.store,dropSlots,store,Nat.add_sub_of_le hn]
    · intro i;fin_cases i <;> rfl
    · intro i hi;fin_cases i
      · rfl
      · rfl
      · exact False.elim (hi 1 rfl)
      · rfl
      · exact False.elim (hi 0 rfl)
  have h4 := copy_run (0:K) 2 3 (by decide) (by decide) (by decide)
    (store xs n (List.replicate (n-xs.length) false) []) (by rfl)
  have he4 : Function.update (store xs n (List.replicate (n-xs.length) false) []) 2
      ((store xs n (List.replicate (n-xs.length) false) [] 2)++(store xs n (List.replicate (n-xs.length) false) [] 0))=
      store xs n (List.replicate (n-xs.length) false++xs) [] := by
    funext i;fin_cases i <;> simp [store]
  rw [he4] at h4
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2 (Run.seq _ _ _ _ _ _ _ h3 h4))
  convert H using 1 <;> first | rfl | simp only [store,Matrix.cons_val_zero];omega
lemma result_length (xs : List Bool) (n : ℕ) (hn : xs.length≤n) :
    (List.replicate (n-xs.length) false++xs).length=n := by simp;omega
lemma result_value (xs : List Bool) (n : ℕ) :
    Add.value (List.replicate (n-xs.length) false++xs).reverse=Add.value xs.reverse := by
  simp [List.reverse_append,Add.value_append,Device.Constant.value_false]
end SourceBurnside.PadRegister

namespace SourceBurnside.WrappedInput
open StackMachine UniversalStack
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K]

def plain (P : List (UniversalStack.Token K)) : List Bool := false::UniversalInput.binaryCode P
def specialize (t v : List Bool) : List Bool :=
  true::(InitialFormula.enc t.length++t++InitialFormula.enc v.length++v)
inductive State (K : Type*) [Fintype K]
  | reverse | reversePut (b : Bool) | header | headerTick | skipPick | skipRead | marker
  | inner (s : UniversalInput.State K)
  deriving Fintype

def machine (src dst : K) : State K → Instr (UniversalStack.Stack K) (UniversalStack.Token K) (State K)
  | .reverse => .pop (.reg src) (fun a => match a with
      | none => .header | some (.bit b) => .reversePut b | _ => .inner (.universal (.stopped false)))
  | .reversePut b => .push (.reg dst) (.bit b) .reverse
  | .header => .pop (.reg dst) (fun a => match a with
      | some (.bit true) => .headerTick | some (.bit false) => .skipPick
      | _ => .inner (.universal (.stopped false)))
  | .headerTick => .push .pc .tick .header
  | .skipPick => .pop .pc (fun a => if a.isSome then .skipRead else .marker)
  | .skipRead => .pop (.reg dst) (fun _ => .skipPick)
  | .marker => .pop (.reg dst) (fun a => match a with
      | some (.bit true) => .header | some (.bit false) => .inner UniversalInput.first
      | _ => .inner (.universal (.stopped false)))
  | .inner s => match UniversalInput.machine src dst s with
      | .halt => .halt
      | .push k a q => .push k a (.inner q)
      | .pop k f => .pop k (fun a => .inner (f a))

def config (src dst : K) (s : State K) (u todo : List Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    Config (UniversalStack.Stack K) (UniversalStack.Token K) (State K) :=
  ⟨s,(UniversalStack.config .pick (UniversalInput.inputRegs src dst u todo) f b pc).store⟩
lemma exec_one (P : State K → Instr (UniversalStack.Stack K) (UniversalStack.Token K) (State K))
    (C : Config (UniversalStack.Stack K) (UniversalStack.Token K) (State K)) : exec P C 1=next P C := rfl
variable (src dst : K) (hne : src≠dst)
include hne
lemma reverse_token (u todo : List Bool) (a : Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .reverse (u++[a]) todo f b pc) 2=
      config src dst .reverse u (a::todo) f b pc := by
  apply config_ext
  · simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
  · funext k
    cases k with
    | reg k =>
      by_cases h1 : k=src
      · subst k; simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,hne]
      · by_cases h2 : k=dst
        · subst k
          simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne,List.reverse_cons]
        · simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,h1,h2]
    | front => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
    | back => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
    | pc => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]

omit hne in
lemma reverse_empty (todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .reverse [] todo f b pc)=
      config src dst .header [] todo f b pc := by
  apply config_ext
  · simp [next,machine,config,UniversalStack.config,UniversalInput.inputRegs]
  · funext k
    cases k with
    | reg k => by_cases h : k=src <;> simp [next,machine,config,UniversalStack.config,UniversalInput.inputRegs,h]
    | front => simp [next,machine,config,UniversalStack.config,UniversalInput.inputRegs]
    | back => simp [next,machine,config,UniversalStack.config,UniversalInput.inputRegs]
    | pc => simp [next,machine,config,UniversalStack.config,UniversalInput.inputRegs]

lemma reverse_all (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .reverse u todo f b pc) (2*u.length+1)=
      config src dst .header [] (u++todo) f b pc := by
  induction u using List.reverseRecOn generalizing todo with
  | nil => simpa [exec] using reverse_empty src dst todo f b pc
  | append_singleton u a ih =>
    rw [List.length_append,List.length_singleton,show 2*(u.length+1)+1=2+(2*u.length+1) by omega,
      exec_from,reverse_token src dst hne,ih]
    simp

lemma header_true (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .header u (true::todo) f b pc) 2=
      config src dst .header u todo f b (pc+1) := by
  apply config_ext
  · simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne,List.getLast?_reverse]
  · funext k
    cases k with
    | reg k =>
      by_cases h1 : k=src
      · subst k; simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,hne,Ne.symm hne]
      · by_cases h2 : k=dst
        · subst k; simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
        · simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,h1,h2,Ne.symm hne]
    | front => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
    | back => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
    | pc => simp [exec,next,machine,config,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne,List.replicate_succ']

lemma config_pop_dst (P : State K → StackMachine.Instr (UniversalStack.Stack K)
    (UniversalStack.Token K) (State K)) (s : State K) (g : Option (UniversalStack.Token K) → State K)
    (he : P s=.pop (.reg dst) g) (u todo : List Bool) (a : Bool)
    (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next P (config src dst s u (a::todo) f b pc)=
      config src dst (g (some (.bit a))) u todo f b pc := by
  apply config_ext
  · simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne,List.getLast?_reverse]
  · funext k
    cases k with
    | reg k =>
      by_cases h1 : k=src
      · subst k; simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs,hne,Ne.symm hne]
      · by_cases h2 : k=dst
        · subst k; simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs,Ne.symm hne]
        · simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs,h1,h2,Ne.symm hne]
    | front => simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs]
    | back => simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs]
    | pc => simp [next,config,he,UniversalStack.config,UniversalInput.inputRegs]

lemma header_false (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .header u (false::todo) f b pc)=
      config src dst .skipPick u todo f b pc := by
  exact config_pop_dst src dst hne (machine src dst) .header _ rfl u todo false f b pc

omit hne in
lemma skip_pick_zero (u todo : List Bool) (f b : List (UniversalStack.Token K)) :
    next (machine src dst) (config src dst .skipPick u todo f b 0)=
      config src dst .marker u todo f b 0 := by
  apply config_ext
  · rfl
  · funext k
    cases k <;> simp [next,machine,config,UniversalStack.config]

omit hne in
lemma skip_pick_succ (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .skipPick u todo f b (pc+1))=
      config src dst .skipRead u todo f b pc := by
  apply config_ext
  · simp [next,machine,config,UniversalStack.config,List.replicate_succ]
  · funext k
    cases k <;> simp [next,machine,config,UniversalStack.config,List.replicate_succ]

lemma skip_read (u todo : List Bool) (a : Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .skipRead u (a::todo) f b pc)=
      config src dst .skipPick u todo f b pc := by
  exact config_pop_dst src dst hne (machine src dst) .skipRead _ rfl u todo a f b pc

lemma header_ones (n : ℕ) (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    exec (machine src dst) (config src dst .header u (List.replicate n true++todo) f b pc) (2*n)=
      config src dst .header u todo f b (pc+n) := by
  induction n generalizing pc with
  | zero => simp [exec]
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,List.replicate_succ,List.cons_append,
      exec_from,header_true src dst hne,ih]
    simp [Nat.add_comm,Nat.add_left_comm]

lemma skip_bits (bits u todo : List Bool) (f b : List (UniversalStack.Token K)) :
    exec (machine src dst) (config src dst .skipPick u (bits++todo) f b bits.length)
      (2*bits.length+1)=config src dst .marker u todo f b 0 := by
  induction bits with
  | nil => simpa [exec] using skip_pick_zero src dst u todo f b
  | cons a bits ih =>
    rw [List.length_cons,List.cons_append,
      show 2*(bits.length+1)+1=1+(1+(2*bits.length+1)) by omega,exec_from]
    rw [exec_one]
    rw [skip_pick_succ src dst,exec_from]
    rw [exec_one]
    rw [skip_read src dst hne,ih]

lemma header_all (bits u todo : List Bool) (f b : List (UniversalStack.Token K)) :
    exec (machine src dst) (config src dst .header u (UniversalInput.header bits++todo) f b 0)
      (4*bits.length+2)=config src dst .marker u todo f b 0 := by
  rw [show 4*bits.length+2=2*bits.length+(1+(2*bits.length+1)) by omega]
  simp only [UniversalInput.header,List.append_assoc,List.cons_append]
  rw [exec_from,header_ones src dst hne,Nat.zero_add,exec_from]
  rw [exec_one]
  rw [header_false src dst hne,skip_bits src dst hne]

lemma marker_true (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .marker u (true::todo) f b pc)=
      config src dst .header u todo f b pc :=
  config_pop_dst src dst hne (machine src dst) .marker _ rfl u todo true f b pc
lemma marker_false (u todo : List Bool) (f b : List (UniversalStack.Token K)) (pc : ℕ) :
    next (machine src dst) (config src dst .marker u (false::todo) f b pc)=
      config src dst (.inner UniversalInput.first) u todo f b pc :=
  config_pop_dst src dst hne (machine src dst) .marker _ rfl u todo false f b pc

omit hne in
def liftConfig (C : Config (UniversalStack.Stack K) (UniversalStack.Token K) (UniversalInput.State K)) :
    Config (UniversalStack.Stack K) (UniversalStack.Token K) (State K) := ⟨.inner C.state,C.store⟩
omit hne in
lemma lift_next (C : Config (UniversalStack.Stack K) (UniversalStack.Token K) (UniversalInput.State K)) :
    next (machine src dst) (liftConfig C)=liftConfig (next (UniversalInput.machine src dst) C) := by
  rcases C with ⟨s,r⟩
  cases he : UniversalInput.machine src dst s <;> simp [next,machine,liftConfig,he]
omit hne in
lemma lift_exec (C : Config (UniversalStack.Stack K) (UniversalStack.Token K) (UniversalInput.State K)) (n : ℕ) :
    exec (machine src dst) (liftConfig C) n=liftConfig (exec (UniversalInput.machine src dst) C n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [exec,ih,lift_next]

def envelope (a x : List Bool) : List Bool := InitialFormula.enc a.length++a++x
omit hne in
lemma enc_header (n : ℕ) : InitialFormula.enc n=UniversalInput.header (InitialFormula.bin n) := by
  simp [InitialFormula.enc,UniversalInput.header]

theorem specialize_trace (t v x : List Bool) :
    exec (machine src dst) (config src dst .header [] (envelope (specialize t v) x) [] [] 0)
      (4*InitialFormula.binSize (specialize t v).length+3)=
      config src dst .header [] (envelope t (InitialFormula.enc v.length++v++x)) [] [] 0 := by
  rw [show 4*InitialFormula.binSize (specialize t v).length+3=
    (4*(InitialFormula.bin (specialize t v).length).length+2)+1 by rw [InitialFormula.bin_length],
    exec_from]
  unfold envelope
  rw [enc_header,List.append_assoc,header_all src dst hne,exec_one]
  simp only [specialize,List.cons_append]
  rw [marker_true src dst hne]
  simp only [List.append_assoc]

lemma plain_trace (P : List (UniversalStack.Token K)) (x : List Bool) :
    exec (machine src dst) (config src dst .header [] (envelope (plain P) x) [] [] 0)
      ((4*InitialFormula.binSize (plain P).length+3)+((UniversalInput.width K+1)*P.length+
        UniversalInput.width K)+(2*P.length+1))=
      config src dst (.inner (.universal .pick)) [] x P [] 0 := by
  rw [exec_from (machine src dst) _ _ (2*P.length+1),
    exec_from (machine src dst) _ _ ((UniversalInput.width K+1)*P.length+UniversalInput.width K),
    show 4*InitialFormula.binSize (plain P).length+3=(4*(InitialFormula.bin (plain P).length).length+2)+1 by
      rw [InitialFormula.bin_length],
    exec_from (machine src dst) _ (4*(InitialFormula.bin (plain P).length).length+2) 1]
  unfold envelope
  rw [enc_header,List.append_assoc,header_all src dst hne,exec_one]
  simp only [plain,List.cons_append]
  rw [marker_false src dst hne]
  change exec (machine src dst) (exec (machine src dst)
    (liftConfig (UniversalInput.config src dst UniversalInput.first [] (UniversalInput.binaryCode P++x) [] [] 0)) _) _=_
  rw [lift_exec,UniversalInput.parse_code src dst hne,List.nil_append,lift_exec,
    UniversalInput.reset_code src dst]
  rfl

theorem raw_specialize_trace (t v x : List Bool) :
    exec (machine src dst) (config src dst .reverse (envelope (specialize t v) x) [] [] [] 0)
      ((2*(envelope (specialize t v) x).length+1)+(4*InitialFormula.binSize (specialize t v).length+3))=
      config src dst .header [] (envelope t (InitialFormula.enc v.length++v++x)) [] [] 0 := by
  rw [exec_from,reverse_all src dst hne,List.append_nil,specialize_trace src dst hne]

end
end SourceBurnside.WrappedInput

end

end OAI
