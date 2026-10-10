import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.Compilation

namespace OAI

section
universe u v w
namespace SourceBurnside.Structured.Device.Formula
variable {ι : Type}
lemma exponents_mono {e : Formula ι} {m n : ℕ} {v : ι → ℕ} (hmn : m≤n) (he : e.Exponents m v) :
    e.Exponents n v := by
  induction e with
  | read i | constant a => trivial
  | add x y hx hy | sub x y hx hy | mul x y hx hy | div x y hx hy | mod x y hx hy | le x y hx hy =>
    exact ⟨hx he.1,hy he.2⟩
  | powTwo x hx => exact ⟨hx he.1,he.2.trans hmn⟩
  | bitLength x hx => exact hx he
  | branch c a b hc ha hb =>
    refine ⟨hc he.1,?_⟩
    split <;> rename_i h
    · exact hb (by simpa only [ite_eq_left h] using he.2)
    · exact ha (by simpa only [ite_eq_right h] using he.2)
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.RawLocalBody
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured Structured.Device Structured.Device.Formula

abbrev Registers := Fin 7
def height : Formula Registers := .read 2
def length : Formula Registers := .mul (.constant 10000) height
def sideStart : Formula Registers := .branch (equal (.read 3) (.constant 1)) (.constant 1) (.constant 2)
def offset (b : Bool) (i : Fin 2) : Formula Registers :=
  .mul (.add (if b then sideStart else .constant 0) (.constant i.val)) length
def piece (b : Bool) (i : Fin 2) : Formula Registers := field (.read 5) (offset b i) length
def substitution : LocalBody.Registers → Formula Registers :=
  ![.read 0,.read 1,.read 2,.read 3,.read 4,piece false 0,piece false 1,piece true 0,piece true 1]
def body (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) : Formula Registers :=
  (LocalBody.body β g D c output blank initial accept encoding).bind substitution

def lengthOK : Formula Registers := and (less (.read 4) (.constant 2))
  (equal (.read 6) (.mul (.branch (.read 4) (.constant 1) (.constant 2)) (.mul (.read 3) length)))
def checkedBody (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) : Formula Registers :=
  and lengthOK (body β g D c output blank initial accept encoding)
def limit (D h n : ℕ) := 10000*(D+20)*(h+1)+n+32
lemma offset_eval_bound (b : Bool) (i : Fin 2) (v : Registers → ℕ) : (offset b i).eval v≤30000*v 2 := by
  have hi : i.val≤1 := by omega
  have he : sideStart.eval v≤2 := by
    by_cases hc : v 3=1 <;> simp [sideStart,eval,equal_eval,hc]
  cases b
  · change (0+i.val)*(10000*v 2)≤_;nlinarith
  · change (sideStart.eval v+i.val)*(10000*v 2)≤_;nlinarith
lemma pieces_exponents (D : ℕ) (v : Registers → ℕ) (b : Bool) (i : Fin 2) :
    (piece b i).Exponents (limit D (v 2) (v 1)) v := by
  apply exponents_field
  · trivial
  · exact ⟨⟨by cases b <;> first | trivial | exact exponents_branch (exponents_equal trivial trivial) trivial trivial,trivial⟩,trivial,trivial⟩
  · exact ⟨trivial,trivial⟩
  · apply le_trans (offset_eval_bound b i v);unfold limit;nlinarith
  · change 10000*v 2≤limit D (v 2) (v 1);unfold limit;nlinarith
lemma body_exponents (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Registers → ℕ) :
    (body β g D c output blank initial accept encoding).Exponents (limit D (v 2) (v 1)) v := by
  apply exponents_bind
  · intro i;fin_cases i
    all_goals first | trivial | exact pieces_exponents D v _ _
  · have H := LocalBody.body_exponents β g D c output blank initial accept encoding (fun i => (substitution i).eval v)
    apply exponents_mono _ H
    change LocalBody.exponentLimit D (v 2) (v 1)≤limit D (v 2) (v 1)
    unfold LocalBody.exponentLimit limit;nlinarith
lemma lengthOK_exponents (M : ℕ) (v : Registers → ℕ) : lengthOK.Exponents M v := by
  apply exponents_and
  · apply exponents_less <;> trivial
  · apply exponents_equal
    · trivial
    · exact ⟨exponents_branch trivial trivial trivial,⟨trivial,⟨trivial,trivial⟩⟩⟩
lemma checkedBody_exponents (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Registers → ℕ) :
    (checkedBody β g D c output blank initial accept encoding).Exponents (limit D (v 2) (v 1)) v :=
  exponents_and (lengthOK_exponents _ _) (body_exponents β g D c output blank initial accept encoding v)
end SourceBurnside.RawLocalBody

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]
def appendMap (f : Bool → Bool) (src dst tmp aux : K) : Program K :=
  .seq (copy src tmp aux) (mapMove f tmp dst)
lemma appendMap_run (f : Bool → Bool) (src dst tmp aux : K)
    (hst : src≠tmp) (hsa : src≠aux) (hta : tmp≠aux) (htd : tmp≠dst)
    (r : Store K) (ht : r tmp=[]) (ha : r aux=[]) :
    Run (appendMap f src dst tmp aux) r (7*(r src).length+3)
      (Function.update r dst (r dst++((r src).reverse.map f))) := by
  have h1 := copy_run src tmp aux hst hsa hta r ha
  simp only [ht,List.nil_append] at h1
  have h2 := mapMove_run f tmp dst htd (Function.update r tmp (r src))
  have he : Function.update (Function.update (Function.update r tmp (r src)) tmp []) dst
      ((Function.update r tmp (r src)) dst++((Function.update r tmp (r src)) tmp).reverse.map f)=
      Function.update r dst (r dst++(r src).reverse.map f) := by
    funext i
    by_cases hd : i=dst
    · subst i;simp [Ne.symm htd]
    · by_cases hj : i=tmp
      · subst i;simp [htd,ht]
      · simp [hd,hj]
  rw [he] at h2
  simp only [Function.update_self] at h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | omega
lemma appendReverse_run (src dst tmp aux : K)
    (hst : src≠tmp) (hsa : src≠aux) (hta : tmp≠aux) (htd : tmp≠dst)
    (r : Store K) (ht : r tmp=[]) (ha : r aux=[]) :
    Run (appendMap id src dst tmp aux) r (7*(r src).length+3)
      (Function.update r dst (r dst++(r src).reverse)) := by
  simpa only [List.map_id_fun,id_eq] using appendMap_run id src dst tmp aux hst hsa hta htd r ht ha
lemma appendOnes_run (src dst tmp aux : K)
    (hst : src≠tmp) (hsa : src≠aux) (hta : tmp≠aux) (htd : tmp≠dst)
    (r : Store K) (ht : r tmp=[]) (ha : r aux=[]) :
    Run (appendMap (fun _ => true) src dst tmp aux) r (7*(r src).length+3)
      (Function.update r dst (r dst++List.replicate (r src).length true)) := by
  simpa [List.map_const] using
    appendMap_run (fun _ => true) src dst tmp aux hst hsa hta htd r ht ha
end SourceBurnside.Structured.Binary

namespace SourceBurnside.QuoteCode
open Structured Structured.Program Structured.Binary
abbrev K := Fin 5

def store (v bits out : List Bool) : Store K := ![v,bits,out,[],[]]
def copyCode : Program K := appendMap id 0 2 3 4
def copyBin : Program K := appendMap id 1 2 3 4
def ones : Program K := appendMap (fun _ => true) 1 2 3 4
def reverseHeader : Program K := .seq copyBin (.seq (.push 2 false) ones)
def stage : Program K := .seq copyCode reverseHeader
def program : Program K := .seq stage (.seq stage (.push 2 true))
lemma copyCode_run (v bits out : List Bool) :
    Run copyCode (store v bits out) (7*v.length+3) (store v bits (out++v.reverse)) := by
  have H := appendReverse_run (0:K) 2 3 4 (by decide) (by decide) (by decide) (by decide)
    (store v bits out) rfl rfl
  convert H using 1 <;> first | rfl | (funext i;fin_cases i <;> simp [store])
lemma copyBin_run (v bits out : List Bool) :
    Run copyBin (store v bits out) (7*bits.length+3) (store v bits (out++bits.reverse)) := by
  have H := appendReverse_run (1:K) 2 3 4 (by decide) (by decide) (by decide) (by decide)
    (store v bits out) rfl rfl
  convert H using 1 <;> first | rfl | (funext i;fin_cases i <;> simp [store])
lemma ones_run (v bits out : List Bool) :
    Run ones (store v bits out) (7*bits.length+3) (store v bits (out++List.replicate bits.length true)) := by
  have H := appendOnes_run (1:K) 2 3 4 (by decide) (by decide) (by decide) (by decide)
    (store v bits out) rfl rfl
  convert H using 1 <;> first | rfl | (funext i;fin_cases i <;> simp [store])
lemma push_run (v bits out : List Bool) (b : Bool) :
    Run (.push (2:K) b) (store v bits out) 1 (store v bits (out++[b])) := by
  convert Run.push (store v bits out) (2:K) b using 1
  funext i;fin_cases i <;> simp [store]
lemma reverseHeader_run (v bits out : List Bool) :
    Run reverseHeader (store v bits out) (14*bits.length+7)
      (store v bits (out++(UniversalInput.header bits).reverse)) := by
  have H := Run.seq _ _ _ _ _ _ _ (copyBin_run v bits out)
    (Run.seq _ _ _ _ _ _ _ (push_run v bits (out++bits.reverse) false)
      (ones_run v bits (out++bits.reverse++[false])))
  convert H using 1 <;> first | rfl | simp only [UniversalInput.header,List.reverse_append,
    List.reverse_cons,List.reverse_replicate,List.append_assoc] | omega
lemma stage_run (v bits out : List Bool) :
    Run stage (store v bits out) (7*v.length+14*bits.length+10)
      (store v bits (out++(UniversalInput.header bits++v).reverse)) := by
  have H := Run.seq _ _ _ _ _ _ _ (copyCode_run v bits out) (reverseHeader_run v bits (out++v.reverse))
  convert H using 1 <;> first | rfl | simp only [List.reverse_append,List.append_assoc] | omega

theorem program_run (v : List Bool) :
    Run program (store v (InitialFormula.bin v.length) [])
      (14*v.length+28*InitialFormula.binSize v.length+21)
      (store v (InitialFormula.bin v.length) (WrappedInput.specialize v v).reverse) := by
  have H := Run.seq _ _ _ _ _ _ _ (stage_run v (InitialFormula.bin v.length) [])
    (Run.seq _ _ _ _ _ _ _ (stage_run v (InitialFormula.bin v.length)
      ([]++(UniversalInput.header (InitialFormula.bin v.length)++v).reverse))
      (push_run v (InitialFormula.bin v.length)
        (([]++(UniversalInput.header (InitialFormula.bin v.length)++v).reverse)++
          (UniversalInput.header (InitialFormula.bin v.length)++v).reverse) true))
  convert H using 1 <;> first | rfl | simp only [InitialFormula.bin_length];omega |
    simp only [WrappedInput.specialize,List.reverse_cons,List.reverse_append,List.append_assoc,
      List.nil_append,WrappedInput.enc_header]
end SourceBurnside.QuoteCode

namespace SourceBurnside.TakePrefix
open Structured Structured.Program
abbrev K := Fin 3
def store (todo : List Bool) (count : ℕ) (out : List Bool) : Store K :=
  ![todo.reverse,List.replicate count false,out]
def step : Program K := .pop 0 (fun a => match a with | some b => .push 2 b | none => .skip)
def program : Program K := .loop 1 (fun _ => step)
lemma step_run (b : Bool) (todo out : List Bool) (n : ℕ) :
    Run step (store (b::todo) n out) 2 (store todo n (out++[b])) := by
  refine Run.pop _ _ _ 1 _ ?_
  have hs : store (b::todo) n out 0=todo.reverse++[b] := by simp [store]
  have he : Function.update (store (b::todo) n out) 0 todo.reverse=store todo n out := by
    funext i;fin_cases i <;> simp [store]
  simp only [hs,List.getLast?_concat,List.dropLast_concat,he]
  convert Run.push (store todo n out) (2:K) b using 1
  funext i;fin_cases i <;> simp [store]

lemma program_run (v todo out : List Bool) :
    Run program (store (v++todo) v.length out) (3*v.length+1) (store todo 0 (out++v)) := by
  induction v generalizing out with
  | nil => simpa [program] using Run.loop_nil (store todo 0 out) (1:K) (fun _ => step) rfl
  | cons b v ih =>
    have he : Function.update (store ((b::v)++todo) (b::v).length out) 1 (List.replicate v.length false)=
        store (b::(v++todo)) v.length out := by
      funext i;fin_cases i <;> simp [store]
    have hs : store ((b::v)++todo) (b::v).length out 1=List.replicate v.length false++[false] := by
      simp only [store,Matrix.cons_val_one,Matrix.cons_val_zero,List.length_cons,List.replicate_add,
        List.replicate_one]
    have H := Run.loop_cons (store ((b::v)++todo) (b::v).length out) (1:K) (fun _ => step)
      (List.replicate v.length false) false (store (v++todo) v.length (out++[b]))
      (store todo 0 ((out++[b])++v)) 2 (3*v.length+1) hs
      (by rw [he];exact step_run b (v++todo) out v.length) (ih (out++[b]))
    convert H using 1 <;> first | rfl | (simp only [List.length_cons,List.append_assoc,List.singleton_append] <;> omega)
end SourceBurnside.TakePrefix

namespace SourceBurnside.TwoInputQuote
open Structured Structured.Program Structured.Binary
abbrev K := Fin 7

def store (todo bits v : List Bool) (count : ℕ) (out : List Bool) : Store K :=
  ![todo.reverse,bits,v,List.replicate count false,[],[],out]
def headerSlots : Fin 4 → K := ![0,3,1,4]
def unarySlots : Fin 4 → K := ![2,3,4,5]
def takeSlots : Fin 3 → K := ![0,3,2]
def quoteSlots : Fin 5 → K := ![2,1,6,4,5]
lemma headerSlots_injective : Function.Injective headerSlots := by decide
lemma unarySlots_injective : Function.Injective unarySlots := by decide
lemma takeSlots_injective : Function.Injective takeSlots := by decide
lemma quoteSlots_injective : Function.Injective quoteSlots := by decide
def readHeader : Program K := HeaderProgram.program.relabel headerSlots
def reverseBin : Program K := appendMap id 1 2 4 5
def makeUnary : Program K := BinaryUnary.program.relabel unarySlots
def takeCode : Program K := TakePrefix.program.relabel takeSlots
def qcopyCode : Program K := appendMap id 2 6 4 5
def qcopyBin : Program K := appendMap id 1 6 4 5
def qones : Program K := appendMap (fun _ => true) 1 6 4 5
def qheader : Program K := .seq qcopyBin (.seq (.push 6 false) qones)
def qstage : Program K := .seq qcopyCode qheader
def quote : Program K := .seq qstage (.seq qstage (.push 6 true))
def program : Program K := .seq readHeader (.seq reverseBin (.seq makeUnary (.seq takeCode quote)))
lemma readHeader_run (n : ℕ) (todo : List Bool) :
    Run readHeader (store (InitialFormula.enc n++todo) [] [] 0 [])
      (7*InitialFormula.binSize n+6) (store todo (InitialFormula.bin n) [] 0 []) := by
  have H := HeaderProgram.header_run (InitialFormula.bin n) todo
  rw [←WrappedInput.enc_header,InitialFormula.bin_length] at H
  refine H.relabel_to headerSlots headerSlots_injective _ _ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 2 rfl)
    · rfl
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 3 rfl)
    · rfl
    · rfl
lemma reverseBin_run (bits todo : List Bool) :
    Run reverseBin (store todo bits [] 0 []) (7*bits.length+3) (store todo bits bits.reverse 0 []) := by
  have H := appendReverse_run (1:K) 2 4 5 (by decide) (by decide) (by decide) (by decide)
    (store todo bits [] 0 []) rfl rfl
  convert H using 1 <;> first | rfl | (funext i;fin_cases i <;> simp [store])
lemma makeUnary_run (n : ℕ) (todo : List Bool) :
    ∃t,t≤(7*n+5)*InitialFormula.binSize n+1 ∧
      Run makeUnary (store todo (InitialFormula.bin n) (InitialFormula.bin n).reverse 0 []) t
        (store todo (InitialFormula.bin n) [] n []) := by
  obtain ⟨t,ht,H⟩ := BinaryUnary.numeral_run n
  refine ⟨t,ht,H.relabel_to unarySlots unarySlots_injective _ _ ?_ ?_ ?_⟩
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · rfl
    · rfl
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 2 rfl)
    · exact False.elim (hi 3 rfl)
    · rfl
lemma takeCode_run (v todo bits : List Bool) :
    Run takeCode (store (v++todo) bits [] v.length []) (3*v.length+1) (store todo bits v 0 []) := by
  refine (TakePrefix.program_run v todo []).relabel_to takeSlots takeSlots_injective _ _ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi;fin_cases i
    · exact False.elim (hi 0 rfl)
    · rfl
    · exact False.elim (hi 2 rfl)
    · exact False.elim (hi 1 rfl)
    · rfl
    · rfl
    · rfl
lemma qcopyCode_run (v bits out todo : List Bool) :
    Run qcopyCode (store todo bits v 0 out) (7*v.length+3) (store todo bits v 0 (out++v.reverse)) := by
  have H := appendReverse_run (2:K) 6 4 5 (by decide) (by decide) (by decide) (by decide)
    (store todo bits v 0 out) rfl rfl
  convert H using 1 <;> first | rfl | (funext i;fin_cases i <;> simp [store])
lemma qcopyBin_run (v bits out todo : List Bool) :
    Run qcopyBin (store todo bits v 0 out) (7*bits.length+3) (store todo bits v 0 (out++bits.reverse)) := by
  have H := appendReverse_run (1:K) 6 4 5 (by decide) (by decide) (by decide) (by decide)
    (store todo bits v 0 out) rfl rfl
  convert H using 1 <;> first | rfl | (funext i;fin_cases i <;> simp [store])
lemma qones_run (v bits out todo : List Bool) :
    Run qones (store todo bits v 0 out) (7*bits.length+3) (store todo bits v 0 (out++List.replicate bits.length true)) := by
  have H := appendOnes_run (1:K) 6 4 5 (by decide) (by decide) (by decide) (by decide)
    (store todo bits v 0 out) rfl rfl
  convert H using 1 <;> first | rfl | (funext i;fin_cases i <;> simp [store])
lemma qpush_run (v bits out todo : List Bool) (b : Bool) :
    Run (.push (6:K) b) (store todo bits v 0 out) 1 (store todo bits v 0 (out++[b])) := by
  convert Run.push (store todo bits v 0 out) (6:K) b using 1
  funext i;fin_cases i <;> simp [store]
lemma qheader_run (v bits out todo : List Bool) :
    Run qheader (store todo bits v 0 out) (14*bits.length+7)
      (store todo bits v 0 (out++(UniversalInput.header bits).reverse)) := by
  have H := Run.seq _ _ _ _ _ _ _ (qcopyBin_run v bits out todo)
    (Run.seq _ _ _ _ _ _ _ (qpush_run v bits (out++bits.reverse) todo false)
      (qones_run v bits (out++bits.reverse++[false]) todo))
  convert H using 1 <;> first | rfl | simp only [UniversalInput.header,List.reverse_append,
    List.reverse_cons,List.reverse_replicate,List.append_assoc] | omega
lemma qstage_run (v bits out todo : List Bool) :
    Run qstage (store todo bits v 0 out) (7*v.length+14*bits.length+10)
      (store todo bits v 0 (out++(UniversalInput.header bits++v).reverse)) := by
  have H := Run.seq _ _ _ _ _ _ _ (qcopyCode_run v bits out todo) (qheader_run v bits (out++v.reverse) todo)
  convert H using 1 <;> first | rfl | simp only [List.reverse_append,List.append_assoc] | omega
lemma quote_run (v todo : List Bool) :
    Run quote (store todo (InitialFormula.bin v.length) v 0 [])
      (14*v.length+28*InitialFormula.binSize v.length+21)
      (store todo (InitialFormula.bin v.length) v 0 (WrappedInput.specialize v v).reverse) := by
  have H := Run.seq _ _ _ _ _ _ _ (qstage_run v (InitialFormula.bin v.length) [] todo)
    (Run.seq _ _ _ _ _ _ _ (qstage_run v (InitialFormula.bin v.length)
      ([]++(UniversalInput.header (InitialFormula.bin v.length)++v).reverse) todo)
      (qpush_run v (InitialFormula.bin v.length)
        (([]++(UniversalInput.header (InitialFormula.bin v.length)++v).reverse)++
          (UniversalInput.header (InitialFormula.bin v.length)++v).reverse) todo true))
  convert H using 1 <;> first | rfl | simp only [InitialFormula.bin_length];omega |
    simp only [WrappedInput.specialize,List.reverse_cons,List.reverse_append,List.append_assoc,
      List.nil_append,WrappedInput.enc_header]

theorem program_run (v todo : List Bool) :
    ∃t,t≤(7*v.length+47)*InitialFormula.binSize v.length+17*v.length+32 ∧
      Run program (store (InitialFormula.enc v.length++v++todo) [] [] 0 []) t
        (store todo (InitialFormula.bin v.length) v 0 (WrappedInput.specialize v v).reverse) := by
  obtain ⟨t,ht,h3⟩ := makeUnary_run v.length (v++todo)
  have h1 := readHeader_run v.length (v++todo)
  have h2 := reverseBin_run (InitialFormula.bin v.length) (v++todo)
  rw [InitialFormula.bin_length] at h2
  have h4 := takeCode_run v todo (InitialFormula.bin v.length)
  have h5 := quote_run v todo
  have H := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2
    (Run.seq _ _ _ _ _ _ _ h3 (Run.seq _ _ _ _ _ _ _ h4 h5)))
  refine ⟨(7*InitialFormula.binSize v.length+6)+((7*InitialFormula.binSize v.length+3)+
    (t+((3*v.length+1)+(14*v.length+28*InitialFormula.binSize v.length+21)))),?_,?_⟩
  · nlinarith [ht]
  · simpa only [program,List.append_assoc] using H
end SourceBurnside.TwoInputQuote

namespace SourceBurnside.Structured.Binary
open Program
variable {K : Type*} [DecidableEq K]
def copyInflate (src dst tmp aux : K) (c : ℕ) : Program K :=
  .seq (copy src tmp aux) (inflate tmp dst c)
lemma copyInflate_run (src dst tmp aux : K) (c : ℕ)
    (hst : src≠tmp) (hsa : src≠aux) (hta : tmp≠aux) (htd : tmp≠dst)
    (r : Store K) (ht : r tmp=[]) (ha : r aux=[]) :
    Run (copyInflate src dst tmp aux c) r ((c+7)*(r src).length+3)
      (Function.update r dst (r dst++List.replicate (c*(r src).length) false)) := by
  have h1 := copy_run src tmp aux hst hsa hta r ha
  simp only [ht,List.nil_append] at h1
  have h2 := inflate_run tmp dst htd c (Function.update r tmp (r src))
  have he : Function.update (Function.update (Function.update r tmp (r src)) tmp []) dst
      ((Function.update r tmp (r src)) dst++List.replicate (c*((Function.update r tmp (r src)) tmp).length) false)=
      Function.update r dst (r dst++List.replicate (c*(r src).length) false) := by
    funext i
    by_cases hd : i=dst
    · subst i;simp [Ne.symm htd]
    · by_cases hj : i=tmp
      · subst i;simp [htd,ht]
      · simp [hd,hj]
  rw [he] at h2
  simp only [Function.update_self] at h2
  have H := Run.seq _ _ _ _ _ _ _ h1 h2
  convert H using 1 <;> first | rfl | ring
end SourceBurnside.Structured.Binary

namespace SourceBurnside.RawPadSeed
open Structured Structured.Program Structured.Binary
abbrev K (r : ℕ) := Fin r ⊕ Fin 3
def store {r : ℕ} (v : Fin r → List Bool) (n : ℕ) : Store (K r)
  | .inl i => v i
  | .inr 0 => List.replicate n false
  | .inr _ => []
def step {r : ℕ} (i : Fin r) (c : ℕ) : Program (K r) :=
  copyInflate (.inl i) (.inr 0) (.inr 1) (.inr 2) c
lemma step_run {r : ℕ} (i : Fin r) (c : ℕ) (v : Fin r → List Bool) (n : ℕ) :
    Run (step i c) (store v n) ((c+7)*(v i).length+3) (store v (n+c*(v i).length)) := by
  have H := copyInflate_run (.inl i : K r) (.inr 0) (.inr 1) (.inr 2) c
    (by simp) (by simp) (by simp) (by simp) (store v n) rfl rfl
  convert H using 1 <;> try rfl
  funext j
  cases j with
  | inl j => simp [store]
  | inr j => fin_cases j <;> simp [store]
def steps {r : ℕ} : List (Fin r × ℕ) → Program (K r)
  | [] => .skip
  | (i,c)::rest => .seq (step i c) (steps rest)
def added {r : ℕ} (v : Fin r → List Bool) : List (Fin r × ℕ) → ℕ
  | [] => 0
  | (i,c)::rest => c*(v i).length+added v rest
def time {r : ℕ} (v : Fin r → List Bool) : List (Fin r × ℕ) → ℕ
  | [] => 1
  | (i,c)::rest => (c+7)*(v i).length+3+time v rest
lemma steps_run {r : ℕ} (items : List (Fin r × ℕ)) (v : Fin r → List Bool) (n : ℕ) :
    Run (steps items) (store v n) (time v items) (store v (n+added v items)) := by
  induction items generalizing n with
  | nil => simpa [steps,time,added] using Run.skip (store v n)
  | cons ic rest ih =>
    rcases ic with ⟨i,c⟩
    have H := Run.seq _ _ _ _ _ _ _ (step_run i c v n) (ih (n+c*(v i).length))
    simpa only [steps,time,added,Nat.add_assoc] using H

def program {r : ℕ} (items : List (Fin r × ℕ)) (offset : ℕ) : Program (K r) :=
  .seq (pushes (.inr 0) offset) (steps items)
lemma program_run {r : ℕ} (items : List (Fin r × ℕ)) (offset : ℕ) (v : Fin r → List Bool) :
    Run (program items offset) (store v 0) (offset+1+time v items)
      (store v (offset+added v items)) := by
  have H := pushes_run (.inr 0 : K r) offset (store v 0)
  have he : Function.update (store v 0) (.inr 0) (store v 0 (.inr 0)++List.replicate offset false)=store v offset := by
    funext i
    cases i with
    | inl i => simp [store]
    | inr i => fin_cases i <;> simp [store]
  rw [he] at H
  exact Run.seq _ _ _ _ _ _ _ H (steps_run items v offset)
end SourceBurnside.RawPadSeed

namespace SourceBurnside.CountLength
open Structured Structured.Program Structured.Binary
abbrev K := Fin 7
def store (xs : List Bool) (n : ℕ) (cnt len : List Bool) : Store K :=
  ![xs,List.replicate n false,cnt,len,[],[],[]]
def work (xs : List Bool) (n : ℕ) : Store K :=
  ![xs,List.replicate n false,List.replicate n false,List.replicate n false,xs,[],[]]
def slots : Fin 5 → K := ![4,2,3,5,6]
lemma slots_injective : Function.Injective slots := by decide
def program : Program K := .seq (copy 1 2 5) (.seq (copy 1 3 5)
  (.seq (copy 0 4 5) (.seq (BitSize.program.relabel slots) (clear 3))))
def countBits (xs : List Bool) (n : ℕ) : List Bool :=
  (BitSize.iter xs.reverse (List.replicate n false) (List.replicate n false)).1.reverse
lemma program_run (xs : List Bool) (n : ℕ) :
    ∃t,t≤(13*n+13)*xs.length+12*n+8 ∧
      Run program (store xs n [] []) t (store xs n (countBits xs n) []) := by
  have h1 := copy_run (1:K) 2 5 (by decide) (by decide) (by decide) (store xs n [] []) rfl
  have he1 : Function.update (store xs n [] []) 2 ((store xs n [] [] 2)++(store xs n [] [] 1))=
      store xs n (List.replicate n false) [] := by
    funext i;fin_cases i <;> simp [store]
  rw [he1] at h1
  have hn1 : (store xs n [] [] 1).length=n := by simp [store]
  rw [hn1] at h1
  have h2 := copy_run (1:K) 3 5 (by decide) (by decide) (by decide) (store xs n (List.replicate n false) []) rfl
  have he2 : Function.update (store xs n (List.replicate n false) []) 3
      ((store xs n (List.replicate n false) [] 3)++(store xs n (List.replicate n false) [] 1))=
      store xs n (List.replicate n false) (List.replicate n false) := by
    funext i;fin_cases i <;> simp [store]
  rw [he2] at h2
  have hn2 : (store xs n (List.replicate n false) [] 1).length=n := by simp [store]
  rw [hn2] at h2
  have h3 := copy_run (0:K) 4 5 (by decide) (by decide) (by decide)
    (store xs n (List.replicate n false) (List.replicate n false)) rfl
  have he3 : Function.update (store xs n (List.replicate n false) (List.replicate n false)) 4
      ((store xs n (List.replicate n false) (List.replicate n false) 4)++
        (store xs n (List.replicate n false) (List.replicate n false) 0))=work xs n := by
    funext i;fin_cases i <;> simp [store,work]
  rw [he3] at h3
  let pair := BitSize.iter xs.reverse (List.replicate n false) (List.replicate n false)
  obtain ⟨t,ht,H⟩ := BitSize.program_run xs.reverse (List.replicate n false) (List.replicate n false) rfl
  simp only [List.length_reverse,List.length_replicate] at ht
  have h4 : Run (BitSize.program.relabel slots) (work xs n) t (store xs n pair.1.reverse pair.2.reverse) := by
    refine H.relabel_to slots slots_injective _ _ ?_ ?_ ?_
    · intro i;fin_cases i <;> simp [BitSize.store,work,slots]
    · intro i;fin_cases i <;> rfl
    · intro i hi;fin_cases i
      · rfl
      · rfl
      · exact False.elim (hi 1 rfl)
      · exact False.elim (hi 2 rfl)
      · exact False.elim (hi 0 rfl)
      · exact False.elim (hi 3 rfl)
      · exact False.elim (hi 4 rfl)
  have h5 := clear_run (3:K) (store xs n pair.1.reverse pair.2.reverse)
  have he5 : Function.update (store xs n pair.1.reverse pair.2.reverse) 3 []=store xs n pair.1.reverse [] := by
    funext i;fin_cases i <;> simp [store]
  rw [he5] at h5
  have hp := (BitSize.iter_lengths xs.reverse (List.replicate n false) (List.replicate n false) rfl).2
  have hl5 : (store xs n pair.1.reverse pair.2.reverse 3).length=n := by
    change pair.2.reverse.length=n
    simpa only [List.length_reverse,List.length_replicate] using hp
  rw [hl5] at h5
  have HH := Run.seq _ _ _ _ _ _ _ h1 (Run.seq _ _ _ _ _ _ _ h2
    (Run.seq _ _ _ _ _ _ _ h3 (Run.seq _ _ _ _ _ _ _ h4 h5)))
  refine ⟨(5*n+2)+((5*n+2)+((5*xs.length+2)+(t+(2*n+1)))),?_,?_⟩
  · nlinarith
  · exact HH
lemma countBits_length (xs : List Bool) (n : ℕ) : (countBits xs n).length=n := by
  simpa only [countBits,List.length_reverse,List.length_replicate] using
    (BitSize.iter_lengths xs.reverse (List.replicate n false) (List.replicate n false) rfl).1
lemma countBits_value (xs : List Bool) (n : ℕ) (h : xs.length<2^n) :
    Add.value (countBits xs n).reverse=xs.length := by
  have H := (BitSize.iter_value xs.reverse (List.replicate n false) (List.replicate n false) rfl
    (by simpa only [Device.Constant.value_false,List.length_replicate,List.length_reverse,Nat.zero_add] using h)).1
  simpa only [countBits,List.reverse_reverse,Device.Constant.value_false,List.length_reverse,Nat.zero_add] using H
end SourceBurnside.CountLength

namespace SourceBurnside.PackFamily
open Structured Structured.Program
abbrev K (r : ℕ) := (Fin r ⊕ Fin r) ⊕ Fin 3

def store {r : ℕ} (v out : Fin r → List Bool) (n : ℕ) : Store (K r)
  | .inl (.inl i) => v i
  | .inl (.inr i) => out i
  | .inr 0 => List.replicate n false
  | .inr _ => []
def slots {r : ℕ} (i : Fin r) : Fin 5 → K r :=
  ![.inl (.inl i),.inr 0,.inl (.inr i),.inr 1,.inr 2]
lemma slots_injective {r : ℕ} (i : Fin r) : Function.Injective (slots i) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [slots] at h ⊢
def pad (xs : List Bool) (n : ℕ) := List.replicate (n-xs.length) false++xs
def step {r : ℕ} (i : Fin r) : Program (K r) := PadRegister.program.relabel (slots i)
lemma step_run {r : ℕ} (i : Fin r) (v out : Fin r → List Bool) (n : ℕ)
    (hlen : (v i).length≤n) (he : out i=[]) :
    Run (step i) (store v out n) (5*n+13*(v i).length+7)
      (store v (Function.update out i (pad (v i) n)) n) := by
  refine (PadRegister.program_run (v i) n hlen).relabel_to (slots i) (slots_injective i) _ _ ?_ ?_ ?_
  · intro j;fin_cases j <;> simp [slots,store,PadRegister.store,he]
  · intro j;fin_cases j <;> simp [slots,store,PadRegister.store,pad]
  · intro j hj
    cases j with
    | inl j =>
      cases j with
      | inl k => rfl
      | inr k =>
        have hk : k≠i := by intro h;subst k;exact hj 2 rfl
        simp [store,hk]
    | inr j => fin_cases j <;> rfl
def program {r : ℕ} : List (Fin r) → Program (K r)
  | [] => .skip
  | i::rest => .seq (step i) (program rest)
def time {r : ℕ} (v : Fin r → List Bool) (n : ℕ) : List (Fin r) → ℕ
  | [] => 1
  | i::rest => (5*n+13*(v i).length+7)+time v n rest
def outputs {r : ℕ} (v out : Fin r → List Bool) (n : ℕ) (items : List (Fin r)) : Fin r → List Bool :=
  fun i => if i∈items then pad (v i) n else out i
lemma program_run {r : ℕ} (items : List (Fin r)) (hd : items.Nodup)
    (v out : Fin r → List Bool) (n : ℕ) (hlen : ∀i∈items,(v i).length≤n)
    (he : ∀i∈items,out i=[]) :
    Run (program items) (store v out n) (time v n items) (store v (outputs v out n items) n) := by
  induction items generalizing out with
  | nil =>
    have h0 : outputs v out n []=out := by funext i;simp only [outputs,List.not_mem_nil,↓reduceIte]
    rw [h0]
    exact Run.skip _
  | cons i rest ih =>
    have hdi := List.nodup_cons.mp hd
    let next := Function.update out i (pad (v i) n)
    have hrest := ih hdi.2 next (by intro k hk;exact hlen k (by simp [hk])) (by
      intro k hk
      have hki : k≠i := by intro h;subst k;exact hdi.1 hk
      simp [next,hki,he k (by simp [hk])])
    have heq : outputs v next n rest=outputs v out n (i::rest) := by
      funext k
      by_cases hk : k=i
      · subst k;simp [outputs,next,hdi.1]
      · simp [outputs,next,hk]
    rw [heq] at hrest
    exact Run.seq _ _ _ _ _ _ _ (step_run i v out n (hlen i (by simp)) (he i (by simp))) hrest

theorem all_run {r : ℕ} (v : Fin r → List Bool) (n : ℕ) (hlen : ∀i,(v i).length≤n) :
    Run (program (List.finRange r)) (store v (fun _ => []) n)
      (time v n (List.finRange r)) (store v (fun i => pad (v i) n) n) := by
  have H := program_run (List.finRange r) (List.nodup_finRange r) v (fun _ => []) n
    (by intro i _;exact hlen i) (by simp)
  have he : outputs v (fun _ => []) n (List.finRange r)=(fun i => pad (v i) n) := by
    funext i;simp only [outputs,List.mem_finRange,↓reduceIte]
  rwa [he] at H
lemma time_le {r : ℕ} (items : List (Fin r)) (v : Fin r → List Bool) (n : ℕ)
    (hlen : ∀i∈items,(v i).length≤n) : time v n items≤ items.length*(18*n+7)+1 := by
  induction items with
  | nil => simp [time]
  | cons i rest ih =>
    have h0 := hlen i (by simp)
    have h1 := ih (by intro j hj;exact hlen j (by simp [hj]))
    simp only [time,List.length_cons]
    nlinarith
end SourceBurnside.PackFamily

end

end OAI
