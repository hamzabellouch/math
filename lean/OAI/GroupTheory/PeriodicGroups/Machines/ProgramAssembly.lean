import Mathlib
import OAI.GroupTheory.PeriodicGroups.Machines.InputEncoding

namespace OAI

section
universe u v w
namespace SourceBurnside.RawNumberPrep
open Structured Structured.Program Structured.Binary
abbrev K := Fin 6 ⊕ Fin 7

def store (v : Fin 6 → List Bool) (n : ℕ) (cl dl : List Bool) : Store K
  | .inl i => v i
  | .inr 0 => List.replicate n false
  | .inr 1 => cl
  | .inr 2 => dl
  | .inr _ => []
def raw (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : Fin 6 → List Bool :=
  ![code.reverse,InitialFormula.bin h,InitialFormula.bin l,[z],data.reverse,List.replicate h false]
def before (code input : List Bool) : Fin 6 → List Bool := ![code.reverse,[],[],[],input.reverse,[]]
def parsed (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : Fin 6 → List Bool :=
  ![code.reverse,InitialFormula.bin h,InitialFormula.bin l,[z],data.reverse,[]]
def headerSlots : Fin 6 → K := ![.inl 4,.inr 5,.inl 1,.inr 6,.inl 2,.inl 3]
def unarySlots : Fin 4 → K := ![.inr 3,.inl 5,.inr 5,.inr 6]
def seedSlots : RawPadSeed.K 6 → K
  | .inl i => .inl i
  | .inr 0 => .inr 0
  | .inr 1 => .inr 5
  | .inr _ => .inr 6
lemma headerSlots_injective : Function.Injective headerSlots := by decide
lemma unarySlots_injective : Function.Injective unarySlots := by decide
lemma seedSlots_injective : Function.Injective seedSlots := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => simpa [seedSlots] using h
    | inr b => fin_cases b <;> simp [seedSlots] at h
  | inr a => cases b with
    | inl b => fin_cases a <;> simp [seedSlots] at h
    | inr b => fin_cases a <;> fin_cases b <;> simp [seedSlots] at h ⊢
def readHeader : Program K := RawHeader.program.relabel headerSlots
def makeUnary : Program K := .seq (appendMap id (.inl 1) (.inr 3) (.inr 5) (.inr 6))
  (BinaryUnary.program.relabel unarySlots)
lemma header_run (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    Run readHeader (store (before code (RawHeader.request h l z data)) 0 [] [])
      (7*(InitialFormula.binSize h+InitialFormula.binSize l)+14)
      (store (parsed code h l z data) 0 [] []) := by
  refine (RawHeader.program_run h l z data).relabel_to headerSlots headerSlots_injective _ _ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i hi
    cases i with
    | inl i =>
      fin_cases i
      · rfl
      · exact False.elim (hi 2 rfl)
      · exact False.elim (hi 4 rfl)
      · exact False.elim (hi 5 rfl)
      · exact False.elim (hi 0 rfl)
      · rfl
    | inr i => fin_cases i <;> rfl
lemma unary_run (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    ∃t,t≤(7*h+12)*InitialFormula.binSize h+4 ∧
      Run makeUnary (store (parsed code h l z data) 0 [] []) t (store (raw code h l z data) 0 [] []) := by
  let r := store (parsed code h l z data) 0 [] []
  let s := Function.update r (.inr 3) (InitialFormula.bin h).reverse
  have h1 := appendReverse_run (.inl 1 : K) (.inr 3) (.inr 5) (.inr 6)
    (by decide) (by decide) (by decide) (by decide) r rfl rfl
  have hs : Function.update r (.inr 3) (r (.inr 3)++(r (.inl 1)).reverse)=s := rfl
  rw [hs] at h1
  have hn : (r (.inl 1)).length=InitialFormula.binSize h := InitialFormula.bin_length h
  rw [hn] at h1
  obtain ⟨t,ht,H⟩ := BinaryUnary.numeral_run h
  have h2 : Run (BinaryUnary.program.relabel unarySlots) s t (store (raw code h l z data) 0 [] []) := by
    refine H.relabel_to unarySlots unarySlots_injective _ _ ?_ ?_ ?_
    · intro i;fin_cases i <;> simp [s,r,store,parsed,unarySlots,BinaryUnary.store]
    · intro i;fin_cases i <;> rfl
    · intro i hi
      cases i with
      | inl i =>
        fin_cases i
        all_goals first | rfl | exact False.elim (hi 1 rfl)
      | inr i =>
        fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl)
  exact ⟨7*InitialFormula.binSize h+3+t,by nlinarith,Run.seq _ _ _ _ _ _ _ h1 h2⟩

def items (W D : ℕ) : List (Fin 6 × ℕ) := [(5,W*(10000*(D+20))),(0,W),(4,W),(2,W)]
def offset (W D : ℕ) := W*(10000*(D+20)+33)
def width (W D h : ℕ) (code data bits : List Bool) : ℕ :=
  W*(RawLocalBody.limit D h code.length+data.length+bits.length+1)
def seed (W D : ℕ) : Program K :=
  (RawPadSeed.program (items W D) (offset W D)).relabel seedSlots
lemma seed_run (W D : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    Run (seed W D) (store (raw code h l z data) 0 [] [])
      (offset W D+1+RawPadSeed.time (raw code h l z data) (items W D))
      (store (raw code h l z data) (width W D h code data (InitialFormula.bin l)) [] []) := by
  have hn : offset W D+RawPadSeed.added (raw code h l z data) (items W D)=
      width W D h code data (InitialFormula.bin l) := by
    simp only [offset,items,RawPadSeed.added,raw,Matrix.cons_val_zero,
      List.length_reverse,width,RawLocalBody.limit]
    dsimp
    simp only [List.length_reverse,List.length_replicate]
    ring
  have H := RawPadSeed.program_run (items W D) (offset W D) (raw code h l z data)
  rw [hn] at H
  refine H.relabel_to seedSlots seedSlots_injective _ _ ?_ ?_ ?_
  · intro i;cases i with
    | inl i => rfl
    | inr i => fin_cases i <;> rfl
  · intro i;cases i with
    | inl i => rfl
    | inr i => fin_cases i <;> rfl
  · intro i hi;cases i with
    | inl i => rfl
    | inr i =>
      fin_cases i
      all_goals first | rfl | exact False.elim (hi (.inr 0) rfl)

def countSlots (b : Bool) : Fin 7 → K :=
  ![.inl (if b then 4 else 0),.inr 0,.inr (if b then 2 else 1),.inr 3,.inr 4,.inr 5,.inr 6]
lemma countSlots_injective (b : Bool) : Function.Injective (countSlots b) := by cases b <;> decide
def count (b : Bool) : Program K := CountLength.program.relabel (countSlots b)
lemma count_run (b : Bool) (v : Fin 6 → List Bool) (n : ℕ) (other : List Bool) :
    ∃t,t≤(13*n+13)*(v (if b then 4 else 0)).length+12*n+8 ∧
      Run (count b) (store v n (if b then other else []) (if b then [] else other)) t
        (store v n (if b then other else CountLength.countBits (v 0) n)
          (if b then CountLength.countBits (v 4) n else other)) := by
  obtain ⟨t,ht,H⟩ := CountLength.program_run (v (if b then 4 else 0)) n
  refine ⟨t,ht,H.relabel_to (countSlots b) (countSlots_injective b) _ _ ?_ ?_ ?_⟩
  · intro i;cases b <;> fin_cases i <;> rfl
  · intro i;cases b <;> fin_cases i <;> rfl
  · intro i hi
    cases i with
    | inl i => rfl
    | inr i =>
      cases b <;> fin_cases i
      all_goals first | rfl | exact False.elim (hi 2 rfl)

def program (W D : ℕ) : Program K :=
  .seq readHeader (.seq makeUnary (.seq (seed W D) (.seq (count false) (count true))))

theorem program_run (W D : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    let v := raw code h l z data
    let n := width W D h code data (InitialFormula.bin l)
    ∃t,t≤7*(InitialFormula.binSize h+InitialFormula.binSize l)+14+
        ((7*h+12)*InitialFormula.binSize h+4)+
        (offset W D+1+RawPadSeed.time v (items W D))+
        ((13*n+13)*(code.length+data.length)+24*n+16) ∧
      Run (program W D) (store (before code (RawHeader.request h l z data)) 0 [] []) t
        (store v n (CountLength.countBits code.reverse n) (CountLength.countBits data.reverse n)) := by
  dsimp only
  let v := raw code h l z data
  let n := width W D h code data (InitialFormula.bin l)
  obtain ⟨tu,hu,Hu⟩ := unary_run code h l z data
  obtain ⟨tc,hc,Hc⟩ := count_run false v n []
  obtain ⟨td,hd,Hd⟩ := count_run true v n (CountLength.countBits (v 0) n)
  simp only [Bool.false_eq_true,ite_false,ite_true] at hc hd Hc Hd
  have hc0 : (v 0).length=code.length := by simp [v,raw]
  have hd0 : (v 4).length=data.length := by simp [v,raw]
  rw [hc0] at hc
  rw [hd0] at hd
  have H := Run.seq _ _ _ _ _ _ _ (header_run code h l z data)
    (Run.seq _ _ _ _ _ _ _ Hu (Run.seq _ _ _ _ _ _ _ (seed_run W D code h l z data)
      (Run.seq _ _ _ _ _ _ _ Hc Hd)))
  refine ⟨(7*(InitialFormula.binSize h+InitialFormula.binSize l)+14)+
    (tu+((offset W D+1+RawPadSeed.time v (items W D))+(tc+td))),?_,?_⟩
  · nlinarith
  · exact H
end SourceBurnside.RawNumberPrep

namespace SourceBurnside.RawPreparedInputs
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
open FiniteTable.Codec
abbrev I := Fin 7
def bound (D h : ℕ) (code data : List Bool) (l : ℕ) :=
  RawLocalBody.limit D h code.length+data.length+InitialFormula.binSize l
def semantic (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : I → ℕ :=
  ![binaryValue code,code.length,h,l,CellRepr.boolean z,binaryValue data,data.length]
def fields : I → RawNumberPrep.K := ![.inl 0,.inr 1,.inl 1,.inl 2,.inl 3,.inl 4,.inr 2]
lemma fields_injective : Function.Injective fields := by decide
def inputs (n : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : I → List Bool :=
  ![code.reverse,CountLength.countBits code.reverse n,InitialFormula.bin h,InitialFormula.bin l,[z],
    data.reverse,CountLength.countBits data.reverse n]
lemma agrees_inputs (n : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    Agrees fields (inputs n code h l z data)
      (RawNumberPrep.store (RawNumberPrep.raw code h l z data) n
        (CountLength.countBits code.reverse n) (CountLength.countBits data.reverse n)) := by
  intro i;fin_cases i <;> rfl
lemma bound_limits (D h l : ℕ) (code data : List Bool) :
    h+1≤bound D h code data l+1 ∧ code.length≤bound D h code data l+1 ∧
    data.length≤bound D h code data l+1 ∧ InitialFormula.binSize l≤bound D h code data l+1 := by
  unfold bound RawLocalBody.limit
  constructor
  · nlinarith
  · omega
lemma semantic_bounded (D h l : ℕ) (code : List Bool) (z : Bool) (data : List Bool) :
    ∀i,semantic code h l z data i<2^(bound D h code data l+1) := by
  have hb := bound_limits D h l code data
  have hlt : l<2^(InitialFormula.binSize l) := by
    have H := Add.value_lt (InitialFormula.bin l).reverse
    simpa only [InitialFormula.bin_value,List.length_reverse,InitialFormula.bin_length] using H
  have hp : 1<2^(bound D h code data l+1) := Nat.one_lt_two_pow (by omega : bound D h code data l+1≠0)
  intro i;fin_cases i
  · exact (binaryValue_lt code).trans_le (Nat.pow_le_pow_right (by omega) hb.2.1)
  · exact hb.2.1.trans_lt Nat.lt_two_pow_self
  · exact (by omega : h<bound D h code data l+1).trans Nat.lt_two_pow_self
  · exact hlt.trans_le (Nat.pow_le_pow_right (by omega) hb.2.2.2)
  · change CellRepr.boolean z<_;cases z <;> simp only [CellRepr.boolean,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · exact (binaryValue_lt data).trans_le (Nat.pow_le_pow_right (by omega) hb.2.2.1)
  · exact hb.2.2.1.trans_lt Nat.lt_two_pow_self
lemma inputs_lengths (D h l n : ℕ) (code : List Bool) (z : Bool) (data : List Bool)
    (hn : bound D h code data l+1≤n) : ∀i,(inputs n code h l z data i).length≤n := by
  have hb := bound_limits D h l code data
  intro i;fin_cases i
  · simpa [inputs] using hb.2.1.trans hn
  · simp [inputs,CountLength.countBits_length]
  · change (InitialFormula.bin h).length≤n
    rw [InitialFormula.bin_length]
    exact (InitialFormula.binSize_le_self h).trans (hb.1.trans hn)
  · simpa [inputs,InitialFormula.bin_length] using hb.2.2.2.trans hn
  · simp [inputs];omega
  · simpa [inputs] using hb.2.2.1.trans hn
  · simp [inputs,CountLength.countBits_length]
lemma inputs_values (D h l n : ℕ) (code : List Bool) (z : Bool) (data : List Bool)
    (hn : bound D h code data l+1≤n) : values (inputs n code h l z data)=semantic code h l z data := by
  have hb := bound_limits D h l code data
  have hc : code.reverse.length<2^n := by
    simpa only [List.length_reverse] using (hb.2.1.trans hn).trans_lt Nat.lt_two_pow_self
  have hd : data.reverse.length<2^n := by
    simpa only [List.length_reverse] using (hb.2.2.1.trans hn).trans_lt Nat.lt_two_pow_self
  funext i;fin_cases i
  · simpa [inputs,values,semantic,List.reverse_reverse] using (binaryValue_eq code).symm
  · simpa [inputs,values,semantic] using CountLength.countBits_value code.reverse n hc
  · simpa [inputs,values,semantic] using InitialFormula.bin_value h
  · simpa [inputs,values,semantic] using InitialFormula.bin_value l
  · cases z <;> rfl
  · simpa [inputs,values,semantic,List.reverse_reverse] using (binaryValue_eq data).symm
  · simpa [inputs,values,semantic] using CountLength.countBits_value data.reverse n hd
def packed (n : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : I → List Bool :=
  fun i => PackFamily.pad (inputs n code h l z data i) n
lemma packed_lengths (D h l n : ℕ) (code : List Bool) (z : Bool) (data : List Bool)
    (hn : bound D h code data l+1≤n) : ∀i,(packed n code h l z data i).length=n := by
  intro i;exact PadRegister.result_length _ n (inputs_lengths D h l n code z data hn i)
lemma packed_values (D h l n : ℕ) (code : List Bool) (z : Bool) (data : List Bool)
    (hn : bound D h code data l+1≤n) : values (packed n code h l z data)=semantic code h l z data := by
  rw [←inputs_values D h l n code z data hn]
  funext i;exact PadRegister.result_value _ _
lemma body_exponents (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool)
    (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    (RawLocalBody.checkedBody β g D c output blank initial accept encoding).Exponents
      (bound D h code data l) (semantic code h l z data) := by
  apply exponents_mono _ (RawLocalBody.checkedBody_exponents β g D c output blank initial accept encoding (semantic code h l z data))
  change RawLocalBody.limit D h code.length≤bound D h code data l
  unfold bound;omega
end SourceBurnside.RawPreparedInputs

namespace SourceBurnside.Structured
variable {A B : Type*} [DecidableEq A] [DecidableEq B]

lemma Run.extend_left {p : Program A} {r s : Store A} {t : ℕ} (h : Run p r t s) (u : Store B) :
    Run (p.relabel Sum.inl) (Sum.elim r u) t (Sum.elim s u) := by
  refine h.relabel_to Sum.inl Sum.inl_injective _ _ (by intro a;rfl) (by intro a;rfl) ?_
  intro x hx;cases x with
  | inl a => exact False.elim (hx a rfl)
  | inr b => rfl
end SourceBurnside.Structured

namespace SourceBurnside.RawAssembler
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
abbrev K := RawNumberPrep.K ⊕ Fin 7
def store (r : Store RawNumberPrep.K) (out : Fin 7 → List Bool) : Store K := Sum.elim r out
def packSlots : PackFamily.K 7 → K
  | .inl (.inl i) => .inl (RawPreparedInputs.fields i)
  | .inl (.inr i) => .inr i
  | .inr 0 => .inl (.inr 0)
  | .inr 1 => .inl (.inr 5)
  | .inr _ => .inl (.inr 6)
lemma packSlots_injective : Function.Injective packSlots := by decide
def pack : Program K := (PackFamily.program (List.finRange 7)).relabel packSlots
lemma pack_run (D h l n : ℕ) (code : List Bool) (z : Bool) (data : List Bool)
    (hn : RawPreparedInputs.bound D h code data l+1≤n) :
    let r := RawNumberPrep.store (RawNumberPrep.raw code h l z data) n
      (CountLength.countBits code.reverse n) (CountLength.countBits data.reverse n)
    Run pack (store r (fun _ => []))
      (PackFamily.time (RawPreparedInputs.inputs n code h l z data) n (List.finRange 7))
      (store r (RawPreparedInputs.packed n code h l z data)) := by
  dsimp only
  have H := PackFamily.all_run (RawPreparedInputs.inputs n code h l z data) n
    (RawPreparedInputs.inputs_lengths D h l n code z data hn)
  refine H.relabel_to packSlots packSlots_injective _ _ ?_ ?_ ?_
  · intro j;cases j with
    | inl j => cases j with
      | inl i => exact RawPreparedInputs.agrees_inputs n code h l z data i
      | inr i => rfl
    | inr i => fin_cases i <;> rfl
  · intro j;cases j with
    | inl j => cases j with
      | inl i => exact RawPreparedInputs.agrees_inputs n code h l z data i
      | inr i => rfl
    | inr i => fin_cases i <;> rfl
  · intro j hj;cases j with
    | inl j => rfl
    | inr j => exact False.elim (hj (.inl (.inr j)) rfl)
def program (W D : ℕ) : Program K := .seq ((RawNumberPrep.program W D).relabel Sum.inl) pack
lemma time_bound (W D h l : ℕ) (code data : List Bool) :
    let v := RawNumberPrep.raw code h l false data
    let Q := h+code.length+data.length+InitialFormula.binSize l+1
    RawNumberPrep.offset W D+1+RawPadSeed.time v (RawNumberPrep.items W D) ≤
      (W*(10000*(D+20)+33)+100)*(Q+1) := by
  dsimp
  simp only [RawNumberPrep.offset,RawPadSeed.time,RawNumberPrep.items,RawNumberPrep.raw]
  dsimp
  simp only [List.length_reverse,List.length_replicate,InitialFormula.bin_length]
  let C := W*(10000*(D+20)+33)+100
  have h0 : W*(10000*(D+20))+7≤C := by dsimp [C];nlinarith
  have h1 : W+7≤C := by dsimp [C];nlinarith
  have h2 := Nat.mul_le_mul_right h h0
  have h3 := Nat.mul_le_mul_right code.length h1
  have h4 := Nat.mul_le_mul_right data.length h1
  have h5 := Nat.mul_le_mul_right (InitialFormula.binSize l) h1
  change _ ≤ C*(h+code.length+data.length+InitialFormula.binSize l+1+1)
  dsimp [C] at h2 h3 h4 h5 ⊢
  nlinarith

theorem program_run (W D : ℕ) (hW : 0<W) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) :
    let n := RawNumberPrep.width W D h code data (InitialFormula.bin l)
    let r := RawNumberPrep.store (RawNumberPrep.raw code h l z data) n
      (CountLength.countBits code.reverse n) (CountLength.countBits data.reverse n)
    ∃t,t≤7*(InitialFormula.binSize h+InitialFormula.binSize l)+14+
        ((7*h+12)*InitialFormula.binSize h+4)+
        (RawNumberPrep.offset W D+1+RawPadSeed.time (RawNumberPrep.raw code h l z data) (RawNumberPrep.items W D))+
        ((13*n+13)*(code.length+data.length)+24*n+16)+(7*(18*n+7)+1) ∧
      Run (program W D)
        (store (RawNumberPrep.store (RawNumberPrep.before code (RawHeader.request h l z data)) 0 [] []) (fun _ => [])) t
        (store r (RawPreparedInputs.packed n code h l z data)) := by
  dsimp only
  let n := RawNumberPrep.width W D h code data (InitialFormula.bin l)
  have hn : RawPreparedInputs.bound D h code data l+1≤n := by
    dsimp [n,RawNumberPrep.width,RawPreparedInputs.bound]
    rw [InitialFormula.bin_length]
    nlinarith
  obtain ⟨t,ht,H⟩ := RawNumberPrep.program_run W D code h l z data
  have H0 := H.extend_left (fun _ : Fin 7 => [])
  have H1 := pack_run D h l n code z data hn
  have htime := PackFamily.time_le (List.finRange 7) (RawPreparedInputs.inputs n code h l z data) n
    (by intro i _;exact RawPreparedInputs.inputs_lengths D h l n code z data hn i)
  simp only [List.length_finRange] at htime
  refine ⟨t+PackFamily.time (RawPreparedInputs.inputs n code h l z data) n (List.finRange 7),by omega,?_⟩
  exact Run.seq _ _ _ _ _ _ _ H0 H1
end SourceBurnside.RawAssembler

namespace SourceBurnside.RawCompiled
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
variable {f : (Fin 7 → ℕ) → ℕ} {Pre : ℕ → (Fin 7 → ℕ) → Prop}
abbrev K (R : Realizer f Pre) := RawAssembler.K ⊕ R.W
def slots (R : Realizer f Pre) : Fin 7 ⊕ R.W → K R
  | .inl i => .inl (.inr i)
  | .inr w => .inr w
lemma slots_injective (R : Realizer f Pre) : Function.Injective (slots R) := by
  intro x y h;cases x <;> cases y <;> simp_all [slots]
def before (R : Realizer f Pre) (code request : List Bool) : Store (K R) :=
  Sum.elim (RawAssembler.store (RawNumberPrep.store (RawNumberPrep.before code request) 0 [] []) (fun _ => [])) (fun _ => [])
def prepared (R : Realizer f Pre) (n : ℕ) (code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool) : Store (K R) :=
  Sum.elim (RawAssembler.store
    (RawNumberPrep.store (RawNumberPrep.raw code h l z data) n
      (CountLength.countBits code.reverse n) (CountLength.countBits data.reverse n))
    (RawPreparedInputs.packed n code h l z data)) (fun _ => [])
def program (R : Realizer f Pre) (W D : ℕ) : Program (K R) :=
  .seq ((RawAssembler.program W D).relabel Sum.inl) (R.program.relabel (slots R))
lemma body_lift (R : Realizer f Pre) {n t : ℕ} {code : List Bool} {h l : ℕ} {z : Bool} {data y : List Bool}
    (H : Run R.program (input (RawPreparedInputs.packed n code h l z data)) t
      (result (RawPreparedInputs.packed n code h l z data) R.out y)) :
    Run (R.program.relabel (slots R)) (prepared R n code h l z data) t
      (Function.update (prepared R n code h l z data) (.inr R.out) y) := by
  have hi : Agrees (slots R) (input (RawPreparedInputs.packed n code h l z data)) (prepared R n code h l z data) := by
    intro i;cases i <;> rfl
  exact H.relabel_to (slots R) (slots_injective R) _ _ hi
    (agrees_update (slots R) (slots_injective R) _ _ hi (.inr R.out) y)
    (outside_update (slots R) _ (.inr R.out) y)
def setupBound (W D h l : ℕ) (code data : List Bool) : ℕ :=
  let n := RawNumberPrep.width W D h code data (InitialFormula.bin l)
  7*(InitialFormula.binSize h+InitialFormula.binSize l)+14+
    ((7*h+12)*InitialFormula.binSize h+4)+
    (RawNumberPrep.offset W D+1+RawPadSeed.time (RawNumberPrep.raw code h l false data) (RawNumberPrep.items W D))+
    ((13*n+13)*(code.length+data.length)+24*n+16)+(7*(18*n+7)+1)
lemma setup_tag_independent (W D h l : ℕ) (code data : List Bool) (z : Bool) :
    RawPadSeed.time (RawNumberPrep.raw code h l z data) (RawNumberPrep.items W D)=
      RawPadSeed.time (RawNumberPrep.raw code h l false data) (RawNumberPrep.items W D) := rfl

theorem generic_trace (e : Formula (Fin 7)) (D : ℕ)
    (hE : ∀code h l z data,e.Exponents (RawPreparedInputs.bound D h code data l)
      (RawPreparedInputs.semantic code h l z data)) :
    ∃R : Realizer e.totalize.eval (fun n v => e.totalize.Safe n v),
      ∀(code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool),
        let n := RawNumberPrep.width e.weight D h code data (InitialFormula.bin l)
        ∃t y,t ≤ setupBound e.weight D h l code data+R.coefficient*(n+1)^2 ∧ y.length=n ∧
          Add.value y.reverse=e.eval (RawPreparedInputs.semantic code h l z data) ∧
          Run (program R e.weight D) (before R code (RawHeader.request h l z data)) t
            (Function.update (prepared R n code h l z data) (.inr R.out) y) := by
  obtain ⟨R,hR⟩ := timed_total (0:Fin 7) e
  refine ⟨R,?_⟩
  intro code h l z data
  let M := RawPreparedInputs.bound D h code data l
  let n := RawNumberPrep.width e.weight D h code data (InitialFormula.bin l)
  have hn0 : n=e.weight*(M+1) := by simp only [n,M,RawNumberPrep.width,RawPreparedInputs.bound,InitialFormula.bin_length]
  have hn : M+1≤n := by rw [hn0];have := e.weight_pos;nlinarith
  have hv := RawPreparedInputs.packed_values D h l n code z data hn
  have hl := RawPreparedInputs.packed_lengths D h l n code z data hn
  obtain ⟨tb,y,hb,hy,hyv,HB⟩ := hR M (RawPreparedInputs.packed n code h l z data) (fun i => (hl i).trans hn0)
    (by rw [hv];exact RawPreparedInputs.semantic_bounded D h l code z data)
    (by rw [hv];exact hE code h l z data)
  rw [←hn0] at hb hy
  rw [hv] at hyv
  obtain ⟨ta,ha,HA⟩ := RawAssembler.program_run e.weight D e.weight_pos code h l z data
  have has : ta ≤ setupBound e.weight D h l code data := by
    simpa only [setup_tag_independent,setupBound] using ha
  have H0 := HA.extend_left (fun _ : R.W => [])
  have H1 := body_lift R HB
  exact ⟨ta+tb,y,Nat.add_le_add has hb,hy,hyv,Run.seq _ _ _ _ _ _ _ H0 H1⟩
theorem program_trace (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) :
    let e := RawLocalBody.checkedBody β g D c output blank initial accept encoding
    ∃R : Realizer e.totalize.eval (fun n v => e.totalize.Safe n v),
      ∀(code : List Bool) (h l : ℕ) (z : Bool) (data : List Bool),
        let n := RawNumberPrep.width e.weight D h code data (InitialFormula.bin l)
        ∃t y,t ≤ setupBound e.weight D h l code data+R.coefficient*(n+1)^2 ∧ y.length=n ∧
          Add.value y.reverse=e.eval (RawPreparedInputs.semantic code h l z data) ∧
          Run (program R e.weight D) (before R code (RawHeader.request h l z data)) t
            (Function.update (prepared R n code h l z data) (.inr R.out) y) := by
  exact generic_trace _ D (RawPreparedInputs.body_exponents β g D c output blank initial accept encoding)
end SourceBurnside.RawCompiled

namespace SourceBurnside.RawPolynomial
open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula
def size (h l : ℕ) (code data : List Bool) : ℕ := h+code.length+data.length+InitialFormula.binSize l+1
def factor (W D : ℕ) : ℕ := W*(10000*(D+20)+33)
lemma size_bounds (h l : ℕ) (code data : List Bool) :
    1 ≤ size h l code data ∧ h+1 ≤ size h l code data ∧
    InitialFormula.binSize h ≤ size h l code data ∧ InitialFormula.binSize l ≤ size h l code data ∧
    code.length+data.length ≤ size h l code data := by
  have := InitialFormula.binSize_le_self h
  unfold size;omega
lemma width_le (W D h l : ℕ) (code data : List Bool) :
    RawNumberPrep.width W D h code data (InitialFormula.bin l) ≤ factor W D*size h l code data := by
  have H := size_bounds h l code data
  have Hh := Nat.mul_le_mul_left (10000*(D+20)) H.2.1
  have Hp : code.length+data.length+InitialFormula.binSize l+33 ≤ 33*size h l code data := by
    unfold size;nlinarith
  unfold RawNumberPrep.width RawLocalBody.limit
  rw [InitialFormula.bin_length]
  unfold factor
  calc
    _  ≤  W*((10000*(D+20)+33)*size h l code data) := Nat.mul_le_mul_left W (by nlinarith)
    _ = _ := by ring
lemma squash {a b B C : ℕ} (ha : a ≤ C*B) (hb : b ≤ B) : a*b ≤ C*B^2 := by
  calc a*b ≤ (C*B)*B := Nat.mul_le_mul ha hb
       _ = C*B^2 := by ring
lemma linear_square {a B C : ℕ} (hB : 1 ≤ B) (ha : a ≤ C*B) : a ≤ C*B^2 := by
  have hs : B ≤ B^2 := by nlinarith
  exact ha.trans (Nat.mul_le_mul_left C hs)
lemma setup_le (W D h l : ℕ) (code data : List Bool) :
    RawCompiled.setupBound W D h l code data  ≤
      (200*factor W D+1000)*(size h l code data+1)^2 := by
  let B := size h l code data+1
  let N := factor W D
  let n := RawNumberPrep.width W D h code data (InitialFormula.bin l)
  have HS := size_bounds h l code data
  have hB : 1 ≤ B := by dsimp [B];omega
  have hh : h ≤ B := by dsimp [B];omega
  have hbh : InitialFormula.binSize h ≤ B := by dsimp [B];omega
  have hbl : InitialFormula.binSize l ≤ B := by dsimp [B];omega
  have hcd : code.length+data.length ≤ B := by dsimp [B];omega
  have hn : n ≤ N*B := (width_le W D h l code data).trans (Nat.mul_le_mul_left _ (by omega))
  have h1 : 7*(InitialFormula.binSize h+InitialFormula.binSize l)+14 ≤ 28*B^2 :=
    linear_square hB (by omega)
  have h2m := squash (show 7*h+12 ≤ 19*B by omega) hbh
  have h4 : 4 ≤ 4*B^2 := by have := linear_square hB (show 4 ≤ 4*B by omega);omega
  have h2 : (7*h+12)*InitialFormula.binSize h+4 ≤ 23*B^2 := by omega
  have ht := RawAssembler.time_bound W D h l code data
  have h3 : RawNumberPrep.offset W D+1+RawPadSeed.time
      (RawNumberPrep.raw code h l false data) (RawNumberPrep.items W D) ≤ (N+100)*B^2 :=
    linear_square hB ht
  have hc1 := squash (show 13*n+13 ≤ (13*N+13)*B by nlinarith) hcd
  have hc2 : 24*n+16 ≤ (24*N+16)*B^2 := linear_square hB (by nlinarith)
  have hcount : (13*n+13)*(code.length+data.length)+24*n+16 ≤ (37*N+29)*B^2 := by
    nlinarith only [hc1,hc2]
  have hpack : 7*(18*n+7)+1 ≤ (126*N+50)*B^2 := linear_square hB (by nlinarith)
  change _  ≤  (200*N+1000)*B^2
  unfold RawCompiled.setupBound
  change 7*(InitialFormula.binSize h+InitialFormula.binSize l)+14+
    ((7*h+12)*InitialFormula.binSize h+4)+
    (RawNumberPrep.offset W D+1+RawPadSeed.time (RawNumberPrep.raw code h l false data) (RawNumberPrep.items W D))+
    ((13*n+13)*(code.length+data.length)+24*n+16)+(7*(18*n+7)+1) ≤ _
  nlinarith only [h1,h2,h3,hcount,hpack]
lemma body_le (W D h l c : ℕ) (code data : List Bool) :
    c*(RawNumberPrep.width W D h code data (InitialFormula.bin l)+1)^2 ≤
      (c*(factor W D+1)^2)*(size h l code data+1)^2 := by
  have hn := width_le W D h l code data
  have H : RawNumberPrep.width W D h code data (InitialFormula.bin l)+1 ≤
      (factor W D+1)*(size h l code data+1) := by nlinarith
  calc
    _  ≤  c*((factor W D+1)*(size h l code data+1))^2 := Nat.mul_le_mul_left c (Nat.pow_le_pow_left H 2)
    _ = _ := by ring
end SourceBurnside.RawPolynomial

namespace SourceBurnside.RawFit
open Structured Structured.Device Structured.Device.Formula
abbrev F := Formula (Fin 7)
def height : F := .read 2
def q : F := .powTwo height
def capacity : F := .powTwo (.mul (.constant 2) height)
def time : F := .powTwo (.div height (.constant 5))
def width : F := .mul (.constant 4) time
def nextHeight (D : ℕ) : F := .mul (.constant D) height
def payload (D : ℕ) : F := .mul (.constant 10000) (nextHeight D)
def binSize (x : F) : F := .branch x (.bitLength x) (.constant 1)
def certificate (β g : ℕ) : F :=
  .add (.mul (.mul (.constant β) width) time)
    (.mul (.mul (.constant g) (.sub width (.constant 2))) (.sub time (.constant 1)))
def clauses (β g : ℕ) : F :=
  .add (.add (.add (.mul (.constant (2*β)) width) (.mul (.constant (2*β)) (.sub time (.constant 1))))
    (.mul (.mul (.constant (3*g+2*β)) (.sub width (.constant 2))) (.sub time (.constant 1)))) (.constant β)

def inputLength (D : ℕ) : F :=
  .add (.add (.add (.add (.read 1) (.mul (.constant 2) (binSize (.read 1))))
    (.mul (.constant 2) (binSize (nextHeight D)))) (.constant 12)) (.mul (.constant 20) (payload D))

def fits (β g D : ℕ) : F := all [
  .le (.add (.mul (.constant 64) height) (.constant 512)) (.mul (.constant 10000) height),
  .le (.constant 10) capacity,
  .le q capacity,
  .le (payload D) q,
  .le (certificate β g) q,
  .le (clauses β g) q,
  less (inputLength D) (.div time (.constant 4))]
def trivialBody : F := all [RawLocalBody.lengthOK,equal (.read 3) (.constant 1),equal (.read 4) (.constant 1)]
def body (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) : F :=
  .branch (fits β g D) (RawLocalBody.checkedBody β g D c output blank initial accept encoding) trivialBody
@[simp] lemma binSize_eval (x : F) (v : Fin 7 → ℕ) : (binSize x).eval v=InitialFormula.binSize (x.eval v) := by
  by_cases h : x.eval v=0 <;> simp [binSize,eval,InitialFormula.binSize,h]
lemma fits_exponents (β g D M : ℕ) (v : Fin 7 → ℕ) (hM : 2*v 2 ≤ M) :
    (fits β g D).Exponents M v := by
  have hh : v 2 ≤ M := by omega
  have ht : v 2/5 ≤ M := (Nat.div_le_self _ _).trans hh
  have qb : q.Exponents M v := ⟨trivial,hh⟩
  have cb : capacity.Exponents M v := ⟨⟨trivial,trivial⟩,hM⟩
  have tb : time.Exponents M v := ⟨⟨trivial,trivial⟩,ht⟩
  have bsz (x : F) (hx : x.Exponents M v) : (binSize x).Exponents M v :=
    exponents_branch hx hx trivial
  have ib : (inputLength D).Exponents M v := by
    exact ⟨⟨⟨⟨trivial,⟨trivial,bsz _ trivial⟩⟩,⟨trivial,bsz _ ⟨trivial,trivial⟩⟩⟩,trivial⟩,
      ⟨trivial,⟨trivial,⟨trivial,trivial⟩⟩⟩⟩
  have ce : (certificate β g).Exponents M v :=
    ⟨⟨⟨trivial,⟨trivial,tb⟩⟩,tb⟩,⟨⟨trivial,⟨⟨trivial,tb⟩,trivial⟩⟩,⟨tb,trivial⟩⟩⟩
  have cl : (clauses β g).Exponents M v :=
    ⟨⟨⟨⟨trivial,⟨trivial,tb⟩⟩,⟨trivial,⟨tb,trivial⟩⟩⟩,
      ⟨⟨trivial,⟨⟨trivial,tb⟩,trivial⟩⟩,⟨tb,trivial⟩⟩⟩,trivial⟩
  apply exponents_all
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨⟨⟨trivial,trivial⟩,trivial⟩,⟨trivial,trivial⟩⟩
  · exact ⟨trivial,cb⟩
  · exact ⟨qb,cb⟩
  · exact ⟨⟨trivial,⟨trivial,trivial⟩⟩,qb⟩
  · exact ⟨ce,qb⟩
  · exact ⟨cl,qb⟩
  · exact exponents_less ib ⟨tb,trivial⟩
lemma trivial_exponents (M : ℕ) (v : Fin 7 → ℕ) : trivialBody.Exponents M v := by
  apply exponents_all
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl
  · exact RawLocalBody.lengthOK_exponents M v
  · exact exponents_equal trivial trivial
  · exact exponents_equal trivial trivial
lemma body_exponents (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Fin 7 → ℕ) :
    (body β g D c output blank initial accept encoding).Exponents (RawLocalBody.limit D (v 2) (v 1)) v := by
  apply exponents_branch
  · apply fits_exponents;unfold RawLocalBody.limit;nlinarith
  · exact RawLocalBody.checkedBody_exponents β g D c output blank initial accept encoding v
  · exact trivial_exponents _ _

def Fits (β g D h n : ℕ) : Prop :=
  let T := 2^(h/5)
  let W := 4*T
  64*h+512 ≤ 10000*h ∧ 10 ≤ 2^(2*h) ∧ 2^h ≤ 2^(2*h) ∧
  10000*(D*h) ≤ 2^h ∧
  β*W*T+g*(W-2)*(T-1) ≤ 2^h ∧
  2*β*W+2*β*(T-1)+(3*g+2*β)*(W-2)*(T-1)+β ≤ 2^h ∧
  n+2*InitialFormula.binSize n+2*InitialFormula.binSize (D*h)+12+20*(10000*(D*h)) < T/4
instance (β g D h n : ℕ) : Decidable (Fits β g D h n) := inferInstanceAs (Decidable (_ ∧ _))
lemma fits_eval (β g D : ℕ) (v : Fin 7 → ℕ) :
    (fits β g D).eval v=if Fits β g D (v 2) (v 1) then 1 else 0 := by
  simp [fits,all_eval,certificate,clauses,inputLength,height,width,time,q,capacity,nextHeight,payload,
    eval,Fits]
  rfl
lemma fallback_eval (v : Fin 7 → ℕ) :
    trivialBody.eval v=if RawLocalBody.lengthOK.eval v≠0 ∧ v 3=1 ∧ v 4=1 then 1 else 0 := by
  simp [trivialBody,all_eval,eval]
lemma body_eval (β g D : ℕ) (c : Tableau.Circuit (3*β) g) (output : Fin β → Tableau.Wire (3*β+g))
    (blank initial accept : Fin β → Bool) (encoding : Bool → Fin β → Bool) (v : Fin 7 → ℕ) :
    (body β g D c output blank initial accept encoding).eval v=
      if Fits β g D (v 2) (v 1) then (RawLocalBody.checkedBody β g D c output blank initial accept encoding).eval v
      else if RawLocalBody.lengthOK.eval v≠0 ∧ v 3=1 ∧ v 4=1 then 1 else 0 := by
  by_cases h : Fits β g D (v 2) (v 1) <;> simp [body,eval,fits_eval,h,fallback_eval]
end SourceBurnside.RawFit

namespace SourceBurnside.Structured
variable {A B : Type*} [DecidableEq A] [DecidableEq B]
lemma Run.extend_right {p : Program B} {r s : Store B} {t : ℕ} (h : Run p r t s) (u : Store A) :
    Run (p.relabel Sum.inr) (Sum.elim u r) t (Sum.elim u s) := by
  refine h.relabel_to Sum.inr Sum.inr_injective _ _ (by intro a;rfl) (by intro a;rfl) ?_
  intro x hx;cases x with
  | inr a => exact False.elim (hx a rfl)
  | inl b => rfl
end SourceBurnside.Structured

end

end OAI
