import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.Recognizer
import OAI.GroupTheory.PeriodicGroups.Machines.RegisterLoops

namespace OAI

universe u v w

namespace SourceBurnside.Structured.Device.Formula
section
variable {ι : Type}

def equal (x y : Formula ι) : Formula ι := .branch (.le x y) (.le y x) (.constant 0)
def less (x y : Formula ι) : Formula ι := .branch (.le y x) (.constant 0) (.constant 1)
def neg (e : Formula ι) : Formula ι := .branch e (.constant 0) (.constant 1)
def and (e f : Formula ι) : Formula ι := .branch e f (.constant 0)
def or (e f : Formula ι) : Formula ι := .branch e (.constant 1) f
def all (es : List (Formula ι)) : Formula ι := es.foldr and (.constant 1)
def any (es : List (Formula ι)) : Formula ι := es.foldr or (.constant 0)

def satSub (x y : Formula ι) : Formula ι := .branch (.le y x) (.sub x y) (.constant 0)
def field (x offset width : Formula ι) : Formula ι :=
  .mod (.div x (.powTwo offset)) (.powTwo width)
def bitAt (x index : Formula ι) : Formula ι := field x index (.constant 1)

@[simp] lemma equal_eval (x y : Formula ι) (vs : ι → ℕ) :
    (equal x y).eval vs=if x.eval vs=y.eval vs then 1 else 0 := by
  by_cases h : x.eval vs=y.eval vs
  · simp [equal,eval,h]
  · by_cases hxy : x.eval vs≤y.eval vs <;>
      simp [equal,eval,h,hxy]
    omega
@[simp] lemma less_eval (x y : Formula ι) (vs : ι → ℕ) :
    (less x y).eval vs=if x.eval vs<y.eval vs then 1 else 0 := by
  by_cases h : y.eval vs≤x.eval vs <;> simp [less,eval,h]
@[simp] lemma neg_eval (x : Formula ι) (vs : ι → ℕ) :
    (neg x).eval vs=if x.eval vs=0 then 1 else 0 := rfl
@[simp] lemma and_eval (x y : Formula ι) (vs : ι → ℕ) :
    (and x y).eval vs=if x.eval vs=0 then 0 else y.eval vs := rfl
@[simp] lemma or_eval (x y : Formula ι) (vs : ι → ℕ) :
    (or x y).eval vs=if x.eval vs=0 then y.eval vs else 1 := rfl
@[simp] lemma all_eval [DecidableEq ι] (es : List (Formula ι)) (vs : ι → ℕ) :
    (all es).eval vs=if ∀e∈es,e.eval vs≠0 then 1 else 0 := by
  induction es with
  | nil => simp [all,eval]
  | cons e es ih =>
    change (and e (all es)).eval vs=_
    rw [and_eval,ih]
    by_cases h : e.eval vs=0 <;> simp [h]
@[simp] lemma any_eval [DecidableEq ι] (es : List (Formula ι)) (vs : ι → ℕ) :
    (any es).eval vs=if ∃e∈es,e.eval vs≠0 then 1 else 0 := by
  induction es with
  | nil => simp [any,eval]
  | cons e es ih =>
    change (or e (any es)).eval vs=_
    rw [or_eval,ih]
    by_cases h : e.eval vs=0 <;> simp [h]
@[simp] lemma satSub_eval (x y : Formula ι) (vs : ι → ℕ) :
    (satSub x y).eval vs=x.eval vs-y.eval vs := by
  by_cases h : y.eval vs≤x.eval vs <;> simp [satSub,eval,h]
  omega
@[simp] lemma field_eval (x index width : Formula ι) (vs : ι → ℕ) :
    (field x index width).eval vs=(x.eval vs/2^(index.eval vs))%2^(width.eval vs) := rfl

lemma bool_all [DecidableEq ι] (es : List (Formula ι)) (vs : ι → ℕ) : (all es).eval vs≤1 := by rw [all_eval];split <;> omega
lemma bool_any [DecidableEq ι] (es : List (Formula ι)) (vs : ι → ℕ) : (any es).eval vs≤1 := by rw [any_eval];split <;> omega
lemma bool_equal (x y : Formula ι) (vs : ι → ℕ) : (equal x y).eval vs≤1 := by rw [equal_eval];split <;> omega
lemma bool_less (x y : Formula ι) (vs : ι → ℕ) : (less x y).eval vs≤1 := by rw [less_eval];split <;> omega
lemma bool_neg (x : Formula ι) (vs : ι → ℕ) : (neg x).eval vs≤1 := by rw [neg_eval];split <;> omega

lemma safe_equal {x y : Formula ι} {n : ℕ} {vs : ι → ℕ} (hx : x.Safe n vs) (hy : y.Safe n vs) :
    (equal x y).Safe n vs := by
  simp only [equal,Safe,eval]
  refine ⟨⟨hx,hy⟩,?_,?_⟩
  · split <;> omega
  · split_ifs <;> simp_all
lemma safe_less {x y : Formula ι} {n : ℕ} {vs : ι → ℕ} (hn : 0<n)
    (hx : x.Safe n vs) (hy : y.Safe n vs) : (less x y).Safe n vs := by
  simp only [less,Safe,eval]
  refine ⟨⟨hy,hx⟩,?_,?_⟩
  · split <;> omega
  · split_ifs <;> simp_all
    omega
lemma safe_neg {x : Formula ι} {n : ℕ} {vs : ι → ℕ} (hn : 0<n)
    (hx : x.Safe n vs) (hb : x.eval vs≤1) : (neg x).Safe n vs := by
  simp only [neg,Safe]
  exact ⟨hx,hb,by
    split_ifs <;> simp_all
    omega⟩
lemma safe_and {x y : Formula ι} {n : ℕ} {vs : ι → ℕ}
    (hx : x.Safe n vs) (hy : y.Safe n vs) (hb : x.eval vs≤1) : (and x y).Safe n vs := by
  simp only [and,Safe]
  exact ⟨hx,hb,by split_ifs <;> simp_all⟩
lemma safe_or {x y : Formula ι} {n : ℕ} {vs : ι → ℕ} (hn : 0<n)
    (hx : x.Safe n vs) (hy : y.Safe n vs) (hb : x.eval vs≤1) : (or x y).Safe n vs := by
  simp only [or,Safe]
  exact ⟨hx,hb,by
    split_ifs <;> simp_all
    omega⟩
lemma safe_all {es : List (Formula ι)} {n : ℕ} {vs : ι → ℕ} (hn : 0<n)
    (h : ∀e∈es,e.Safe n vs ∧ e.eval vs≤1) : (all es).Safe n vs := by
  induction es with
  | nil => simp [all,Safe];omega
  | cons e es ih =>
    exact safe_and (h e (by simp)).1 (ih (by intro a ha;exact h a (by simp [ha]))) (h e (by simp)).2
lemma safe_any {es : List (Formula ι)} {n : ℕ} {vs : ι → ℕ} (hn : 0<n)
    (h : ∀e∈es,e.Safe n vs ∧ e.eval vs≤1) : (any es).Safe n vs := by
  induction es with
  | nil => simp [any,Safe]
  | cons e es ih =>
    exact safe_or hn (h e (by simp)).1 (ih (by intro a ha;exact h a (by simp [ha]))) (h e (by simp)).2
lemma safe_satSub {x y : Formula ι} {n : ℕ} {vs : ι → ℕ}
    (hx : x.Safe n vs) (hy : y.Safe n vs) : (satSub x y).Safe n vs := by
  simp only [satSub,Safe,eval]
  refine ⟨⟨hy,hx⟩,?_,?_⟩
  · split <;> omega
  · split_ifs <;> simp_all

end

variable {ι : Type}
def implies (x y : Formula ι) : Formula ι := .branch x y (.constant 1)
lemma implies_eval (x y : Formula ι) (v : ι → ℕ) :
    (implies x y).eval v=if x.eval v=0 then 1 else y.eval v := rfl
@[simp] lemma implies_ne_zero (x y : Formula ι) (v : ι → ℕ) :
    (implies x y).eval v≠0 ↔ (x.eval v≠0 → y.eval v≠0) := by
  by_cases h : x.eval v=0 <;> simp [implies_eval,h]
lemma bool_implies (x y : Formula ι) (v : ι → ℕ) (hy : y.eval v≤1) :
    (implies x y).eval v≤1 := by rw [implies_eval];split <;> omega
lemma safe_implies {x y : Formula ι} {n : ℕ} {v : ι → ℕ} (hn : 0<n)
    (hx : x.Safe n v) (hy : y.Safe n v) (hb : x.eval v≤1) : (implies x y).Safe n v := by
  simp only [implies,Safe]
  exact ⟨hx,hb,by
    split_ifs <;> simp_all
    omega⟩

lemma safe_field {x i w : Formula ι} {n : ℕ} {v : ι → ℕ}
    (hx : x.Safe n v) (hi : i.Safe n v) (hw : w.Safe n v)
    (hin : i.eval v<n) (hwn : w.eval v<n) : (field x i w).Safe n v := by
  have H (a : ℕ) (ha : a<n) : 2*(2^a)≤2^n := by
    rw [←Nat.pow_succ']
    exact Nat.pow_le_pow_right (by omega) (by omega)
  exact ⟨⟨hx,⟨hi,hin⟩,by change 0<2^(i.eval v);positivity,H _ hin⟩,⟨hw,hwn⟩,by change 0<2^(w.eval v);positivity,H _ hwn⟩
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.RawFormula
open Structured.Device Structured.Device.Formula FiniteTable.Codec
instance (q : ℕ) (v : Fin 32 → ℕ) : Decidable (InRange q v) := by unfold InRange;infer_instance
abbrev F := Formula (Fin 2)
def height : F := .read 0
def word : F := .read 1
def scale (a : ℕ) : F := .mul (.constant a) height
def slot (s : Fin 32) : F := field word (scale (2*s.val)) (scale 2)
def flag (s : Fin 512) : F := bitAt word (.add (scale 64) (.constant s.val))
def bound : F := .powTwo height

def ranges : F := all
  [less (slot 0) (.constant 3),less (slot 1) bound,
   implies (equal (slot 0) (.constant 2)) (equal (slot 1) (.constant 0)),
   less (slot 2) (.constant 5),less (slot 3) (.constant 10),.le (slot 4) (slot 3),
   less (slot 5) (.constant 3),less (slot 6) bound,
   implies (equal (slot 5) (.constant 0)) (equal (slot 6) (.constant 0)),
   less (slot 7) bound,less (slot 8) (.constant 9)]
def reservation : F := and
  (equal (field word (scale 18) (scale 46)) (.constant 0))
  (equal (.div word (.powTwo (.add (scale 64) (.constant 8)))) (.constant 0))
def valid : F := and ranges reservation

def inputs (h w : ℕ) : Fin 2 → ℕ := ![h,w]
@[simp] lemma height_eval (h w : ℕ) : height.eval (inputs h w)=h := rfl
@[simp] lemma word_eval (h w : ℕ) : word.eval (inputs h w)=w := rfl
@[simp] lemma scale_eval (a h w : ℕ) : (scale a).eval (inputs h w)=a*h := rfl
@[simp] lemma slot_eval (s : Fin 32) (h w : ℕ) :
    (slot s).eval (inputs h w)=(w/2^(s.val*(2*h)))%2^(2*h) := by
  simp [slot,Nat.mul_comm,Nat.mul_left_comm]
@[simp] lemma bound_eval (h w : ℕ) : bound.eval (inputs h w)=2^h := rfl

lemma ranges_eval (h w : ℕ) : ranges.eval (inputs h w)=
    if InRange (2^h) (fun s : Fin 32 => (w/2^(s.val*(2*h)))%2^(2*h)) then 1 else 0 := by
  simp [ranges,InRange,eval,and_assoc]

lemma reservation_eval (h w : ℕ) : reservation.eval (inputs h w)=
    if (w/2^(18*h))%2^(46*h)=0 ∧ w/2^(64*h+8)=0 then 1 else 0 := by
  simp only [reservation,and_eval,equal_eval,field_eval,scale_eval,word_eval,eval]
  by_cases H : (w/2^(18*h))%2^(46*h)=0 <;>
    by_cases J : w/2^(64*h+8)=0 <;> simp [H,J]

lemma valid_eval (h w : ℕ) : valid.eval (inputs h w)=
    if InRange (2^h) (fun s : Fin 32 => (w/2^(s.val*(2*h)))%2^(2*h)) ∧
      ((w/2^(18*h))%2^(46*h)=0 ∧ w/2^(64*h+8)=0) then 1 else 0 := by
  rw [valid,and_eval,ranges_eval,reservation_eval]
  split_ifs <;> simp_all

theorem accepts_iff_decode {h : ℕ} (hh : 0<h) (w : Raw h) :
    valid.eval (inputs h (natCode w))=1 ↔ (decode hh w).isSome=true := by
  rw [decode_isSome_arithmetic hh w,valid_eval]
  split_ifs <;> simp_all

lemma valid_boolean (h w : ℕ) : valid.eval (inputs h w)≤1 := by rw [valid_eval];split_ifs <;> omega

lemma safe_constant {a n : ℕ} (ha : a ≤ 64) (hn : 7≤n) (v : Fin 2 → ℕ) :
    (Formula.constant a : F).Safe n v := by
  change a.bits.length≤n
  have hb : a<2^7 := by norm_num;omega
  have h := (Nat.size_le).mpr hb
  simpa only [Nat.size_eq_bits_len] using h.trans hn

lemma scale_safe {a h w n : ℕ} (ha : a≤64) (hn : 64*h+10≤n) :
    (scale a).Safe n (inputs h w) := by
  refine ⟨safe_constant ha (by omega) _,trivial,?_⟩
  have H : a*h<n := by nlinarith
  exact H.trans (Nat.lt_two_pow_self)

lemma slots_safe {h w n : ℕ} (_hh : 0<h) (hn : 64*h+10≤n) (s : Fin 32) :
    (slot s).Safe n (inputs h w) := by
  apply safe_field (x:=word) (i:=scale (2*s.val)) (w:=scale 2) (n:=n) (v:=inputs h w) trivial
    (scale_safe (by have := s.isLt;omega) hn) (scale_safe (by omega) hn)
  · rw [scale_eval]
    have := s.isLt
    nlinarith
  · rw [scale_eval];omega

lemma bound_safe {h w n : ℕ} (hn : 64*h+10≤n) : bound.Safe n (inputs h w) := by
  exact ⟨trivial,by change h<n;omega⟩

lemma ranges_safe {h w n : ℕ} (hh : 0<h) (hn : 64*h+10≤n) : ranges.Safe n (inputs h w) := by
  have Hn : 0<n := by omega
  have HC (a : ℕ) (ha : a≤64) : (Formula.constant a : F).Safe n (inputs h w) := safe_constant ha (by omega) _
  have HS := slots_safe (w:=w) hh hn
  have HB := bound_safe (w:=w) hn
  apply safe_all Hn
  intro e he
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals constructor
  all_goals first
    | exact safe_less Hn (HS _) HB
    | exact safe_less Hn (HS _) (HC _ (by omega))
    | exact safe_implies Hn (safe_equal (HS _) (HC _ (by omega)))
        (safe_equal (HS _) (HC _ (by omega))) (bool_equal _ _ _)
    | exact ⟨HS _,HS _⟩
    | exact bool_less _ _ _
    | exact bool_implies _ _ _ (bool_equal _ _ _)
    | (simp only [eval];split_ifs <;> omega)

lemma reservation_safe {h w n : ℕ} (_hh : 0<h) (hn : 64*h+10≤n) :
    reservation.Safe n (inputs h w) := by
  have H0 := safe_constant (a:=0) (by omega) (show 7≤n by omega) (inputs h w)
  have Hf := safe_field (x:=word) (i:=scale 18) (w:=scale 46) (n:=n) (v:=inputs h w) trivial
    (scale_safe (by omega) hn) (scale_safe (by omega) hn)
    (by rw [scale_eval];omega) (by rw [scale_eval];omega)
  have Ha : (Formula.add (scale 64) (.constant 8)).Safe n (inputs h w) := by
    refine ⟨scale_safe (by omega) hn,safe_constant (by omega) (by omega) _,?_⟩
    change 64*h+8<2^n
    exact (show 64*h+8<n by omega).trans Nat.lt_two_pow_self
  have Hp : (Formula.powTwo (.add (scale 64) (.constant 8))).Safe n (inputs h w) := ⟨Ha,by change 64*h+8<n;omega⟩
  have Hd : (Formula.div word (.powTwo (.add (scale 64) (.constant 8)))).Safe n (inputs h w) := by
    refine ⟨trivial,Hp,by change 0<2^(64*h+8);positivity,?_⟩
    change 2*2^(64*h+8)≤2^n
    rw [←Nat.pow_succ']
    exact Nat.pow_le_pow_right (by omega) (by omega)
  exact safe_and (safe_equal Hf H0) (safe_equal Hd H0) (bool_equal _ _ _)

theorem valid_safe {h w n : ℕ} (hh : 0<h) (hn : 64*h+10≤n) : valid.Safe n (inputs h w) :=
  safe_and (ranges_safe hh hn) (reservation_safe hh hn) (bool_all _ _)

end SourceBurnside.RawFormula

namespace SourceBurnside.CellRepr
open LocalSyntax FiniteTable FiniteTable.Codec

def boolean (b : Bool) : ℕ := if b then 1 else 0
@[simp] lemma boolean_false : boolean false=0 := rfl
@[simp] lemma boolean_true : boolean true=1 := rfl
lemma boolean_injective : Function.Injective boolean := by intro a b;cases a <;> cases b <;> simp [boolean]
@[simp] lemma boolean_eq_zero (b : Bool) : boolean b=0 ↔ b=false := by cases b <;> decide
@[simp] lemma boolean_eq_one (b : Bool) : boolean b=1 ↔ b=true := by cases b <;> decide
@[simp] lemma boolean_bit_zero : boolean (bit 0)=0 := rfl
lemma boolean_lt_two (b : Bool) : boolean b<2 := by cases b <;> decide

abbrev Record (A : Type) := (Fin 9 → A) × (Fin 8 → A)
def cellRecord {q : ℕ} (c : Cell q) : Record ℕ :=
  ⟨fun s => integers c ⟨s.val,by have := s.isLt;omega⟩,
   fun s => boolean (flags c ⟨s.val,by have := s.isLt;omega⟩)⟩

lemma repr_injective {h : ℕ} (hh : 4≤h) : Function.Injective (cellRecord (q:=2^h)) := by
  intro c d H
  apply encode_injective hh
  unfold encode
  congr 1
  · funext s
    by_cases hs : s.val<9
    · have Hs := congrArg (fun r : Record ℕ => r.1 ⟨s.val,hs⟩) H
      exact Hs
    · rw [integers_unused c s (by omega),integers_unused d s (by omega)]
  · funext s
    by_cases hs : s.val<8
    · have Hs := congrArg (fun r : Record ℕ => r.2 ⟨s.val,hs⟩) H
      exact boolean_injective Hs
    · rw [flags_unused c s (by omega),flags_unused d s (by omega)]

lemma repr_integer {q : ℕ} (c : Cell q) (i : Fin 9) :
    (cellRecord c).1 i=integers c ⟨i.val,by have := i.isLt;omega⟩ := rfl
lemma repr_flag {q : ℕ} (c : Cell q) (i : Fin 8) :
    (cellRecord c).2 i=boolean (flags c ⟨i.val,by have := i.isLt;omega⟩) := rfl

end SourceBurnside.CellRepr

namespace SourceBurnside.CellFormula
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
abbrev Expr := Record (Formula ι)

def evaluate (a : Expr (ι:=ι)) (v : ι → ℕ) : Record ℕ :=
  ⟨fun i => (a.1 i).eval v,fun i => (a.2 i).eval v⟩

def ofRaw (height word : Formula ι) : Expr (ι:=ι) :=
  ⟨fun i => field word (.mul (.constant (2*i.val)) height) (.mul (.constant 2) height),
   fun i => bitAt word (.add (.mul (.constant 64) height) (.constant i.val))⟩

omit [DecidableEq ι] in
lemma ofRaw_represents {h : ℕ} (hh : 4≤h) (c : Cell (2^h)) (H W : Formula ι) (v : ι → ℕ)
    (hH : H.eval v=h) (hW : W.eval v=natCode (encode c)) :
    evaluate (ofRaw H W) v=cellRecord c := by
  apply Prod.ext
  · funext i
    have HR := readInt_arithmetic (show 0<h by omega) (encode c) ⟨i.val,by have := i.isLt;omega⟩
    rw [readInt_encode hh] at HR
    simpa [evaluate,ofRaw,Formula.eval,hH,hW,cellRecord,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using HR.symm
  · funext i
    have HR := flag_as_nat (show 0<h by omega) (encode c) ⟨i.val,by have := i.isLt;omega⟩
    rw [readFlag_encode] at HR
    simpa [evaluate,ofRaw,bitAt,Formula.eval,hH,hW,cellRecord,boolean] using HR.symm

def equalCells (a b : Expr (ι:=ι)) : Formula ι :=
  and (all (List.ofFn (fun i : Fin 9 => equal (a.1 i) (b.1 i))))
    (all (List.ofFn (fun i : Fin 8 => equal (a.2 i) (b.2 i))))

lemma equalCells_eval (a b : Expr (ι:=ι)) (v : ι → ℕ) :
    (equalCells a b).eval v=if evaluate a v=evaluate b v then 1 else 0 := by
  simp only [equalCells,and_eval,all_eval]
  have H (n : ℕ) (a b : Fin n → Formula ι) :
      (∀e∈List.ofFn (fun i => equal (a i) (b i)),e.eval v≠0) ↔
        (fun i => (a i).eval v)=(fun i => (b i).eval v) := by
    simp [funext_iff]
  simp only [H]
  simp only [evaluate,Prod.mk.injEq]
  split_ifs <;> simp_all

lemma equality_exact {h : ℕ} (hh : 4≤h) (a b : Expr (ι:=ι)) (v : ι → ℕ)
    (c d : Cell (2^h)) (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d) :
    (equalCells a b).eval v=1 ↔ c=d := by
  simp only [equalCells_eval,ha,hb,(repr_injective hh).eq_iff]
  split_ifs <;> simp_all

lemma equalCells_bool (a b : Expr (ι:=ι)) (v : ι → ℕ) : (equalCells a b).eval v≤1 := by
  rw [equalCells_eval];split_ifs <;> omega

def wing (a : Expr (ι:=ι)) (m : Marker) : Expr (ι:=ι) :=
  ⟨fun i => match i.val with | 2 => .constant (markerTag m) | 7 | 8 => .constant 0 | _ => a.1 i,
   fun i => match i.val with | 1 | 5 | 6 | 7 => .constant 0 | _ => a.2 i⟩
def boundary (a : Expr (ι:=ι)) (side : Formula ι) : Expr (ι:=ι) :=
  ⟨(wing a .boundary).1,
   fun i => match i.val with | 1 => side | 5 | 6 | 7 => .constant 0 | _ => a.2 i⟩
def full (a : Expr (ι:=ι)) (side clause : Formula ι) (phase : Phase)
    (reg : Fin 3 → Formula ι) : Expr (ι:=ι) :=
  ⟨fun i => match i.val with | 2 => .constant 3 | 7 => clause | 8 => .constant (phaseTag phase) | _ => a.1 i,
   fun i => match i.val with | 1 => side | 5 => reg 0 | 6 => reg 1 | 7 => reg 2 | _ => a.2 i⟩
def idle (a : Expr (ι:=ι)) (side : Formula ι) : Expr (ι:=ι) :=
  ⟨fun i => match i.val with | 2 | 3 | 4 | 7 | 8 => .constant 0 | _ => a.1 i,
   fun i => if i.val=2 then .branch side (a.2 3) (a.2 2) else .constant 0⟩
def setChecker (a : Expr (ι:=ι)) (tag index : Formula ι) : Expr (ι:=ι) :=
  ⟨fun i => match i.val with | 5 => tag | 6 => index | _ => a.1 i,a.2⟩
def setColor (a : Expr (ι:=ι)) (color : Formula ι) : Expr (ι:=ι) :=
  ⟨fun i => match i.val with | 0 => .constant 1 | 1 => color | _ => a.1 i,a.2⟩

omit [DecidableEq ι]

lemma represent_int {q : ℕ} {a : Expr (ι:=ι)} {v : ι → ℕ} {c : Cell q}
    (h : evaluate a v=cellRecord c) (i : Fin 9) : (a.1 i).eval v=(cellRecord c).1 i := congrArg (fun r => r.1 i) h
lemma represent_flag {q : ℕ} {a : Expr (ι:=ι)} {v : ι → ℕ} {c : Cell q}
    (h : evaluate a v=cellRecord c) (i : Fin 8) : (a.2 i).eval v=(cellRecord c).2 i := congrArg (fun r => r.2 i) h

variable {q : ℕ} [NeZero q] {a : Expr (ι:=ι)} {v : ι → ℕ} {c : Cell q}
variable (ha : evaluate a v=cellRecord c)
include ha

lemma wing_represents (m : Marker) : evaluate (wing a m) v=cellRecord (c.wing m) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,wing,Formula.eval,represent_int ha,represent_flag ha,cellRecord,
      integers,flags,Cell.wing,Skeleton.mark,defaultHead,Cell.pos,Cell.marker,Cell.metadata,phaseTag]

lemma boundary_represents (side : Formula ι) (s : Bool) (hs : side.eval v=boolean s) :
    evaluate (boundary a side) v=cellRecord (c.boundary s) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,boundary,wing,Formula.eval,represent_int ha,represent_flag ha,hs,cellRecord,
      integers,flags,Cell.boundary,Skeleton.mark,defaultHead,Cell.pos,Cell.marker,Cell.metadata,phaseTag]

omit [NeZero q] in
lemma full_represents (side clause : Formula ι) (phase : Phase) (reg : Fin 3 → Formula ι)
    (s : Bool) (j : Fin q) (r : Reg) (hs : side.eval v=boolean s) (hj : clause.eval v=j.val)
    (hr : ∀i,(reg i).eval v=boolean (bit (r i))) :
    evaluate (full a side clause phase reg) v=cellRecord (c.full s j phase r) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,full,Formula.eval,represent_int ha,represent_flag ha,hs,hj,hr,cellRecord,
      integers,flags,Cell.full,Skeleton.mark,Cell.pos,Cell.marker,Cell.metadata,markerTag]

lemma idle_represents (side : Formula ι) (s : Bool) (hs : side.eval v=boolean s) :
    evaluate (idle a side) v=cellRecord (c.idle s) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,idle,Formula.eval,represent_int ha,represent_flag ha,hs,cellRecord,
      integers,flags,Cell.idle,defaultHead,defaultMeta,Cell.pos,Cell.marker,Cell.metadata,
      markerTag,phaseTag,bit,boolean]
  cases s <;> simp

omit [NeZero q] in
lemma setChecker_represents (tag index : Formula ι) (ch : Palette.Check (Fin q))
    (ht : tag.eval v=checkerTag ch) (hi : index.eval v=checkerIndex ch) :
    evaluate (setChecker a tag index) v=cellRecord (c.setChecker ch) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,setChecker,represent_int ha,represent_flag ha,ht,hi,cellRecord,
      integers,flags,Cell.setChecker,Cell.pos,Cell.marker,Cell.metadata]

omit [NeZero q] in
lemma setColor_represents (color : Formula ι) (col : Fin q) (hc : color.eval v=col.val) :
    evaluate (setColor a color) v=cellRecord (c.setColor col) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [evaluate,setColor,Formula.eval,represent_int ha,represent_flag ha,hc,cellRecord,
      integers,flags,Cell.setColor,Cell.pos,Cell.marker,Cell.metadata,positionTag,positionIndex]

end SourceBurnside.CellFormula

namespace SourceBurnside.Structured.Device.Formula
variable {ι : Type}
@[simp] lemma constant_eval (k : ℕ) (v : ι → ℕ) : (.constant k : Formula ι).eval v=k := rfl
@[simp] lemma add_eval (a b : Formula ι) (v : ι → ℕ) : (Formula.add a b).eval v=a.eval v+b.eval v := rfl
@[simp↓] lemma equal_ne_zero (x y : Formula ι) (v : ι → ℕ) :
    (equal x y).eval v≠0 ↔ x.eval v=y.eval v := by simp [equal_eval]
@[simp↓] lemma all_ne_zero [DecidableEq ι] (es : List (Formula ι)) (v : ι → ℕ) :
    (all es).eval v≠0 ↔ ∀e∈es,e.eval v≠0 := by simp [all_eval]
@[simp↓] lemma any_ne_zero [DecidableEq ι] (es : List (Formula ι)) (v : ι → ℕ) :
    (any es).eval v≠0 ↔ ∃e∈es,e.eval v≠0 := by simp [any_eval]
@[simp↓] lemma and_ne_zero (x y : Formula ι) (v : ι → ℕ) :
    (and x y).eval v≠0 ↔ x.eval v≠0 ∧ y.eval v≠0 := by
  rw [and_eval];split_ifs <;> simp_all
@[simp↓] lemma or_ne_zero (x y : Formula ι) (v : ι → ℕ) :
    (or x y).eval v≠0 ↔ x.eval v≠0 ∨ y.eval v≠0 := by
  rw [or_eval];split_ifs <;> simp_all
@[simp↓] lemma neg_ne_zero (x : Formula ι) (v : ι → ℕ) :
    (neg x).eval v≠0 ↔ ¬x.eval v≠0 := by simp [neg_eval]
attribute [-simp] equal_eval all_eval any_eval and_eval or_eval neg_eval
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.CellFormula
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def first (a : Expr (ι:=ι)) : Formula ι :=
  all [equal (a.1 4) (.constant 0),equal (a.1 0) (.constant 0),equal (a.1 1) (.constant 0)]
def last (a : Expr (ι:=ι)) : Formula ι :=
  all [equal (a.1 4) (a.1 3),equal (a.1 0) (.constant 2)]
def hasMarker (a : Expr (ι:=ι)) (m : Marker) := equal (a.1 2) (.constant (markerTag m))
def hasPhase (a : Expr (ι:=ι)) (p : Phase) := equal (a.1 8) (.constant (phaseTag p))
def isCore (a : Expr (ι:=ι)) := equal (a.1 0) (.constant 0)
def isPalette (a : Expr (ι:=ι)) := equal (a.1 0) (.constant 1)
def isStop (a : Expr (ι:=ι)) := equal (a.1 0) (.constant 2)
def hasHead (a : Expr (ι:=ι)) := or (hasMarker a .boundary) (hasMarker a .full)
def endpoint (a : Expr (ι:=ι)) := any ([Phase.acquisition,.beforeGate,.afterGate,.finish,.success].map (hasPhase a))

def admissible (a : Expr (ι:=ι)) : Formula ι :=
  and (implies (hasMarker a .right) (neg (first a)))
    (implies (hasMarker a .left) (neg (last a)))
def leftExternal (a : Expr (ι:=ι)) : Formula ι :=
  or (hasMarker a .idle) (and (neg (hasMarker a .right)) (first a))
def rightExternal (a : Expr (ι:=ι)) : Formula ι :=
  or (hasMarker a .idle) (or (hasMarker a .boundary) (and (neg (hasMarker a .left)) (last a)))
def acceptsLeft (a b : Expr (ι:=ι)) : Formula ι :=
  .branch (hasMarker a .right) (or (hasMarker b .full) (hasMarker b .right)) (hasMarker b .left)
def acceptsRight (a b : Expr (ι:=ι)) : Formula ι :=
  .branch (hasMarker a .left) (any [hasMarker b .left,hasMarker b .boundary,hasMarker b .full]) (hasMarker b .right)
def structural (a b : Expr (ι:=ι)) (Q : Formula ι) : Formula ι :=
  any [all [isCore a,isCore b,equal (.add (a.1 1) (.constant 1)) (b.1 1)],
    all [isCore a,isPalette b,equal (.add (a.1 1) (.constant 1)) Q],
    and (isPalette a) (isPalette b),and (isPalette a) (isStop b),
    all [isStop a,isCore b,equal (b.1 1) (.constant 0)]]
def internal (a b : Expr (ι:=ι)) : Formula ι :=
  all [equal (a.1 3) (b.1 3),equal (a.2 0) (b.2 0),
    .branch (isStop a) (equal (.add (a.1 4) (.constant 1)) (b.1 4)) (equal (a.1 4) (b.1 4)),
    neg (first b),neg (last a)]
def skeletonPair (a b : Expr (ι:=ι)) (Q : Formula ι) : Formula ι :=
  and (structural a b Q) (or (and (rightExternal a) (leftExternal b))
    (all [neg (rightExternal a),neg (leftExternal b),acceptsRight a b,acceptsLeft b a,internal a b]))

lemma markerTag_injective : Function.Injective markerTag := by intro a b;cases a <;> cases b <;> simp [markerTag]
lemma phaseTag_injective : Function.Injective phaseTag := by intro a b;cases a <;> cases b <;> simp [phaseTag]

variable {q : ℕ} [NeZero q] {a b : Expr (ι:=ι)} {v : ι → ℕ} {c d : Cell q}
variable (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)
include ha
lemma first_exact : (first a).eval v≠0 ↔ c.skeleton.first := by
  cases hp : c.skeleton.pos <;>
    simp [first,represent_int ha,cellRecord,integers,Skeleton.first,Cell.pos,hp,
      positionTag,positionIndex,Cell.metadata]
omit [NeZero q] in
lemma last_exact : (last a).eval v≠0 ↔ c.skeleton.last := by
  cases hp : c.skeleton.pos <;>
    simp [last,represent_int ha,cellRecord,integers,Skeleton.last,Cell.pos,hp,
      positionTag,Cell.metadata]
omit [DecidableEq ι] [NeZero q] in
lemma marker_exact (m : Marker) : (hasMarker a m).eval v≠0 ↔ c.marker=m := by
  simp [hasMarker,represent_int ha,cellRecord,integers,markerTag_injective.eq_iff]
omit [DecidableEq ι] [NeZero q] in
lemma phase_exact (p : Phase) : (hasPhase a p).eval v≠0 ↔ c.head.phase=p := by
  simp [hasPhase,represent_int ha,cellRecord,integers,phaseTag_injective.eq_iff]
omit [DecidableEq ι] in
lemma core_exact : (isCore a).eval v≠0 ↔ c.isCore := by
  cases hp : c.skeleton.pos <;> simp [isCore,represent_int ha,cellRecord,integers,Cell.isCore,Cell.pos,hp,positionTag]
omit [DecidableEq ι] in
lemma palette_exact : (isPalette a).eval v≠0 ↔ c.isPalette := by
  cases hp : c.skeleton.pos <;> simp [isPalette,represent_int ha,cellRecord,integers,Cell.isPalette,Cell.pos,hp,positionTag]
omit [DecidableEq ι] [NeZero q] in
lemma stop_exact : (isStop a).eval v≠0 ↔ c.pos=.stop := by
  cases hp : c.skeleton.pos <;> simp [isStop,represent_int ha,cellRecord,integers,Cell.pos,hp,positionTag]
omit [DecidableEq ι] [NeZero q] in
lemma head_exact : (hasHead a).eval v≠0 ↔ Skeleton.IsHead c.skeleton := by
  simp only [hasHead,Formula.or_ne_zero,marker_exact ha,Skeleton.IsHead,Cell.marker]
omit [NeZero q] in
lemma endpoint_exact : (endpoint a).eval v≠0 ↔ Cell.endpoint c.head.phase := by
  simp only [endpoint,Formula.any_ne_zero,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,exists_eq_left,phase_exact ha,Cell.endpoint]
lemma admissible_exact : (admissible a).eval v≠0 ↔ c.skeleton.Admissible := by
  simp [admissible,first_exact ha,last_exact ha,marker_exact ha,Skeleton.Admissible,Cell.marker]
lemma leftExternal_exact : (leftExternal a).eval v≠0 ↔ c.skeleton.leftExternal := by
  simp only [leftExternal,Formula.or_ne_zero,Formula.and_ne_zero,Formula.neg_ne_zero,first_exact ha,marker_exact ha,Skeleton.leftExternal,Cell.marker]
omit [NeZero q] in
lemma rightExternal_exact : (rightExternal a).eval v≠0 ↔ c.skeleton.rightExternal := by
  simp only [rightExternal,Formula.or_ne_zero,Formula.and_ne_zero,Formula.neg_ne_zero,last_exact ha,marker_exact ha,Skeleton.rightExternal,Cell.marker]
include hb
omit [DecidableEq ι] [NeZero q] in
lemma acceptsLeft_exact : (acceptsLeft a b).eval v≠0 ↔ c.skeleton.acceptsLeft d.marker := by
  change (if (hasMarker a .right).eval v=0 then (hasMarker b .left).eval v else
    (or (hasMarker b .full) (hasMarker b .right)).eval v)≠0 ↔ _
  by_cases h : c.skeleton.marker=.right
  · have H := (marker_exact ha .right).mpr h
    simp only [H,ite_false,ite_true,Formula.or_ne_zero,marker_exact hb,Skeleton.acceptsLeft,Cell.marker,h]
  · have H : (hasMarker a .right).eval v=0 := not_not.mp (mt (marker_exact ha .right).mp h)
    simp [H,marker_exact hb,Skeleton.acceptsLeft,Cell.marker,h]
omit [NeZero q] in
lemma acceptsRight_exact : (acceptsRight a b).eval v≠0 ↔ c.skeleton.acceptsRight d.marker := by
  change (if (hasMarker a .left).eval v=0 then (hasMarker b .right).eval v else
    (any [hasMarker b .left,hasMarker b .boundary,hasMarker b .full]).eval v)≠0 ↔ _
  by_cases h : c.skeleton.marker=.left
  · have H := (marker_exact ha .left).mpr h
    simp only [H,ite_false,ite_true,marker_exact hb,Skeleton.acceptsRight,Cell.marker,h,Formula.any_ne_zero,List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,exists_eq_left]
  · have H : (hasMarker a .left).eval v=0 := not_not.mp (mt (marker_exact ha .left).mp h)
    simp only [H,ite_false,ite_true,marker_exact hb,Skeleton.acceptsRight,Cell.marker,h]
lemma structural_exact (Q : Formula ι) (hQ : Q.eval v=q) :
    (structural a b Q).eval v≠0 ↔ Skeleton.Structural c.skeleton d.skeleton := by
  simp only [structural,any_ne_zero,all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,
    exists_eq_or_imp,exists_eq_left,forall_eq_or_imp,forall_eq,and_ne_zero,core_exact ha,core_exact hb,palette_exact ha,
    palette_exact hb,stop_exact ha,stop_exact hb,equal_ne_zero,Formula.constant_eval,Formula.add_eval,represent_int ha,
    represent_int hb,hQ,cellRecord,integers]
  cases hp : c.skeleton.pos <;> cases hr : d.skeleton.pos <;>
    simp [Cell.isCore,Cell.isPalette,hp,hr,positionIndex,Skeleton.Structural,Cell.pos]
lemma internal_exact : (internal a b).eval v≠0 ↔ Skeleton.Internal c.skeleton d.skeleton := by
  have B : (Formula.branch (isStop a)
      (equal (.add (a.1 4) (.constant 1)) (b.1 4)) (equal (a.1 4) (b.1 4))).eval v≠0 ↔
      (if c.pos=.stop then c.metadata.block.val+1=d.metadata.block.val
        else c.metadata.block.val=d.metadata.block.val) := by
    change (if (isStop a).eval v=0 then (equal (a.1 4) (b.1 4)).eval v
      else (equal (.add (a.1 4) (.constant 1)) (b.1 4)).eval v)≠0 ↔ _
    by_cases hp : c.pos=.stop
    · have HS := (stop_exact ha).mpr hp
      simp [HS,hp,represent_int ha,represent_int hb,cellRecord,integers]
    · have HS : (isStop a).eval v=0 := not_not.mp (mt (stop_exact ha).mp hp)
      simp [HS,hp,represent_int ha,represent_int hb,cellRecord,integers]
  simp only [internal,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,Formula.equal_ne_zero,B,Formula.neg_ne_zero]
  simp [represent_int ha,represent_int hb,represent_flag ha,represent_flag hb,cellRecord,integers,flags,
    boolean_injective.eq_iff,first_exact hb,last_exact ha,Skeleton.Internal,Cell.metadata,Cell.pos]
  simp only [Fin.ext_iff]
  rfl
lemma skeletonPair_exact (Q : Formula ι) (hQ : Q.eval v=q) :
    (skeletonPair a b Q).eval v≠0 ↔ Skeleton.Pair c.skeleton d.skeleton := by
  simp only [skeletonPair,Formula.and_ne_zero,Formula.or_ne_zero,Formula.all_ne_zero,Formula.neg_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,structural_exact ha hb Q hQ,rightExternal_exact ha,leftExternal_exact hb,
    acceptsRight_exact ha hb,acceptsLeft_exact hb ha,internal_exact ha hb,Skeleton.Pair,Cell.marker]
end SourceBurnside.CellFormula

namespace SourceBurnside.CellRepr
open FiniteTable FiniteTable.Codec
@[simp] lemma bit_false_iff (x : ZMod 2) : bit x=false ↔ x=0 := by
  constructor
  · intro H
    have HH := congrArg unbit H
    rw [unbit_bit] at HH
    exact HH
  · rintro rfl;rfl
@[simp] lemma bit_true_iff (x : ZMod 2) : bit x=true ↔ x=1 := by
  constructor
  · intro H
    have HH := congrArg unbit H
    rw [unbit_bit] at HH
    exact HH
  · rintro rfl;rfl
@[simp] lemma boolean_bit_zero_iff (x : ZMod 2) : boolean (bit x)=0 ↔ x=0 := by simp
@[simp] lemma boolean_bit_one_iff (x : ZMod 2) : boolean (bit x)=1 ↔ x=1 := by simp
lemma boolean_bit_add (x y : ZMod 2) :
    boolean (bit (x+y))=(boolean (bit x)+boolean (bit y))%2 := by
  fin_cases x <;> fin_cases y <;> decide
end SourceBurnside.CellRepr

namespace SourceBurnside.Structured.Device.Formula
variable {ι : Type}
@[simp↓] lemma le_ne_zero (a b : Formula ι) (v : ι → ℕ) :
    (Formula.le a b).eval v≠0 ↔ a.eval v≤b.eval v := by simp [eval]
@[simp↓] lemma less_ne_zero (a b : Formula ι) (v : ι → ℕ) :
    (less a b).eval v≠0 ↔ a.eval v<b.eval v := by simp [less_eval]
attribute [-simp] less_eval
end SourceBurnside.Structured.Device.Formula

namespace SourceBurnside.CellFormula
section
open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
def regZero (a : Expr (ι:=ι)) : Formula ι :=
  all [equal (a.2 5) (.constant 0),equal (a.2 6) (.constant 0),equal (a.2 7) (.constant 0)]
def headZero (a : Expr (ι:=ι)) : Formula ι :=
  all [equal (a.2 1) (.constant 0),equal (a.1 7) (.constant 0),hasPhase a .acquisition,regZero a]
def metaZero (a : Expr (ι:=ι)) : Formula ι :=
  and (equal (a.1 3) (.constant 0)) (equal (a.2 0) (.constant 0))
def dataZero (a : Expr (ι:=ι)) : Formula ι :=
  and (equal (a.2 2) (.constant 0)) (equal (a.2 3) (.constant 0))
def checkerIdle (a : Expr (ι:=ι)) : Formula ι := equal (a.1 5) (.constant 0)
def checkerPassed (a : Expr (ι:=ι)) : Formula ι := equal (a.1 5) (.constant 1)
def checkerHead (a : Expr (ι:=ι)) : Formula ι := equal (a.1 5) (.constant 2)
def headFree (a : Expr (ι:=ι)) : Formula ι := and (neg (hasHead a)) (neg (checkerHead a))
def coreLimit (a : Expr (ι:=ι)) (size : Formula ι) : Formula ι :=
  implies (and (isCore a) (.le size (a.1 1))) (dataZero a)
def formats (a : Expr (ι:=ι)) (size count : Formula ι) : Formula ι := all
  [admissible a,
   implies (neg (isPalette a)) (checkerIdle a),
   coreLimit a size,
   implies (neg (isCore a)) (and (dataZero a) (equal (a.2 4) (.constant 0))),
   implies (hasMarker a .idle) (all [metaZero a,headZero a,equal (a.2 3) (.constant 0),equal (a.2 4) (.constant 0)]),
   implies (or (hasMarker a .left) (hasMarker a .right)) (headZero a),
   implies (hasMarker a .boundary) (all [equal (a.1 7) (.constant 0),hasPhase a .acquisition,regZero a]),
   implies (hasHead a) (implies (equal (a.2 0) (.constant 1)) (equal (a.2 1) (.constant 0))),
   implies (hasMarker a .full) (all [implies (hasPhase a .success) (equal (a.1 7) (.constant 0)),
     implies (neg (hasPhase a .success)) (less (a.1 7) count),implies (endpoint a) (last a)])]

def palettePair (a b : Expr (ι:=ι)) : Formula ι := any
  [and (checkerIdle a) (checkerIdle b),
   all [checkerPassed a,checkerPassed b,equal (a.1 6) (b.1 6)],
   all [checkerPassed a,checkerHead b,equal (a.1 6) (b.1 6)],
   and (checkerHead a) (checkerIdle b)]
def checkerPair (a b : Expr (ι:=ι)) : Formula ι :=
  and (implies (and (isPalette a) (isPalette b)) (palettePair a b))
    (implies (and (isPalette a) (isStop b)) (neg (checkerPassed a)))
def pair (a b : Expr (ι:=ι)) (Q : Formula ι) : Formula ι := and (skeletonPair a b Q) (checkerPair a b)

lemma reg_zero_iff (r : Reg) : r=0 ↔ r 0=0 ∧ r 1=0 ∧ r 2=0 := by
  constructor
  · rintro rfl;simp
  · intro h;funext i;fin_cases i <;> simp_all
lemma data_zero_iff (f : Bool → ZMod 2) : f=0 ↔ f false=0 ∧ f true=0 := by
  constructor
  · rintro rfl;simp
  · intro h;funext i;cases i <;> simp_all
lemma meta_zero_iff (m : Meta) : m=defaultMeta ↔ m.arity=0 ∧ m.zeroTask=false := by
  constructor
  · rintro rfl;simp [defaultMeta]
  · rcases m with ⟨arity,task,block⟩;dsimp only
    rintro ⟨rfl,rfl⟩
    have H : block=0 := by
      apply Fin.ext
      have HB := block.isLt
      norm_num at HB ⊢
    subst block;rfl
lemma head_zero_iff {q : ℕ} [NeZero q] (h : Head q) : h=defaultHead ↔
    h.side=false ∧ h.clause=0 ∧ h.phase=.acquisition ∧ h.reg=0 := by
  cases h;simp [defaultHead,Head.mk.injEq]

variable {q : ℕ} [NeZero q] {a b : Expr (ι:=ι)} {v : ι → ℕ} {c d : Cell q}
variable (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)
include ha
omit [NeZero q] in
lemma regZero_exact : (regZero a).eval v≠0 ↔ c.head.reg=0 := by
  simp only [regZero,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    Formula.equal_ne_zero,Formula.constant_eval]
  simp [represent_flag ha,cellRecord,flags,reg_zero_iff]
omit [DecidableEq ι] [NeZero q] in
lemma dataZero_exact : (dataZero a).eval v≠0 ↔ c.data=0 := by
  simp only [dataZero,Formula.and_ne_zero,Formula.equal_ne_zero,Formula.constant_eval]
  simp [represent_flag ha,cellRecord,flags,data_zero_iff]
omit [DecidableEq ι] [NeZero q] in
lemma metaZero_exact : (metaZero a).eval v≠0 ↔ c.metadata=defaultMeta := by
  simp only [metaZero,Formula.and_ne_zero,Formula.equal_ne_zero,Formula.constant_eval]
  simp [represent_int ha,represent_flag ha,cellRecord,integers,flags,meta_zero_iff]
lemma headZero_exact : (headZero a).eval v≠0 ↔ c.head=defaultHead := by
  simp only [headZero,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    Formula.equal_ne_zero,Formula.constant_eval,phase_exact ha,regZero_exact ha]
  simp [represent_int ha,represent_flag ha,cellRecord,integers,flags,head_zero_iff]
omit [DecidableEq ι] [NeZero q] in
lemma checkerIdle_exact : (checkerIdle a).eval v≠0 ↔ c.checker=.idle := by
  cases hc : c.checker <;> simp [checkerIdle,represent_int ha,cellRecord,integers,hc,checkerTag]
omit [DecidableEq ι] in
lemma checkerPassed_exact : (checkerPassed a).eval v≠0 ↔ ∃ x,c.checker=.passed x := by
  cases hc : c.checker <;> simp [checkerPassed,represent_int ha,cellRecord,integers,hc,checkerTag]
omit [DecidableEq ι] in
lemma checkerHead_exact : (checkerHead a).eval v≠0 ↔ ∃ x,c.checker=.head x := by
  cases hc : c.checker <;> simp [checkerHead,represent_int ha,cellRecord,integers,hc,checkerTag]
omit [DecidableEq ι] in
lemma headFree_exact : (headFree a).eval v≠0 ↔ c.HeadFree := by
  simp only [headFree,Formula.and_ne_zero,Formula.neg_ne_zero,head_exact ha,checkerHead_exact ha]
  simp [Cell.HeadFree]
omit [DecidableEq ι] in
lemma coreLimit_exact (size : Formula ι) (n : ℕ) (hn : size.eval v=n) :
    (coreLimit a size).eval v≠0 ↔ ∀p,c.pos=.core p → n≤p.val → c.data=0 := by
  simp only [coreLimit,implies_ne_zero,Formula.and_ne_zero,core_exact ha,le_ne_zero,hn,dataZero_exact ha]
  cases hp : c.pos <;>
    simp [represent_int ha,cellRecord,integers,Cell.isCore,hp,positionIndex]
lemma formats_exact (S : Schedule q) (size count : Formula ι) (n : ℕ)
    (hn : size.eval v=n) (hc : count.eval v=(S.count c.metadata.task).val) :
    (formats a size count).eval v≠0 ↔ c.Format S n := by
  simp only [formats,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    implies_ne_zero,Formula.and_ne_zero,Formula.or_ne_zero,Formula.neg_ne_zero,
    admissible_exact ha,checkerIdle_exact ha,core_exact ha,palette_exact ha,coreLimit_exact ha size n hn,
    dataZero_exact ha,marker_exact ha,metaZero_exact ha,headZero_exact ha,head_exact ha,
    phase_exact ha,regZero_exact ha,endpoint_exact ha,last_exact ha,Formula.equal_ne_zero,
    Formula.constant_eval,less_ne_zero,hc]
  simp [represent_int ha,represent_flag ha,cellRecord,integers,flags,Cell.Format]

end

open LocalSyntax FiniteTable FiniteTable.Codec CellRepr Structured.Device Structured.Device.Formula
variable {ι : Type} [DecidableEq ι]
lemma check_pair_iff {q : ℕ} (x y : Palette.Check (Fin q)) : Palette.Pair x y ↔
    (x=.idle ∧ y=.idle) ∨ (∃z,x=.passed z ∧ y=.passed z) ∨
      (∃z,x=.passed z ∧ y=.head z) ∨ (∃z,x=.head z ∧ y=.idle) := by
  constructor
  · intro h;cases h <;> simp
  · rintro (⟨rfl,rfl⟩ | ⟨z,rfl,rfl⟩ | ⟨z,rfl,rfl⟩ | ⟨z,rfl,rfl⟩)
    · exact .idle
    · exact .passed z
    · exact .next z
    · exact .rest z

def passedOwn (a : Expr (ι:=ι)) : Formula ι :=
  all [isPalette a,checkerPassed a,equal (a.1 1) (a.1 6)]
def duplicate (a b : Expr (ι:=ι)) : Formula ι :=
  all [isPalette a,isPalette b,equal (a.1 1) (b.1 1)]
def missing (a b : Expr (ι:=ι)) : Formula ι :=
  all [isPalette a,checkerHead a,isStop b,neg (equal (a.1 1) (a.1 6))]
def semanticZero (a : Expr (ι:=ι)) (truth : Formula ι) : Formula ι :=
  and (hasMarker a .full) (any
    [and (any [hasPhase a .acquisition,hasPhase a .finish,hasPhase a .success]) (neg (regZero a)),
     and (hasPhase a .afterGate) (equal truth (.constant 0)),
     and (hasPhase a .success) (equal (a.2 0) (.constant 1))])
def unaryZero (a : Expr (ι:=ι)) (size count truth : Formula ι) : Formula ι :=
  any [neg (formats a size count),semanticZero a truth,passedOwn a]
def binaryZero (a b : Expr (ι:=ι)) (Q : Formula ι) : Formula ι :=
  any [neg (pair a b Q),duplicate a b,missing a b]

variable {q : ℕ} [NeZero q] {a b : Expr (ι:=ι)} {v : ι → ℕ} {c d : Cell q}
variable (ha : evaluate a v=cellRecord c) (hb : evaluate b v=cellRecord d)
include ha hb
lemma palettePair_exact : (palettePair a b).eval v≠0 ↔ Palette.Pair c.checker d.checker := by
  rw [check_pair_iff]
  simp only [palettePair,Formula.any_ne_zero,Formula.all_ne_zero,Formula.and_ne_zero,
    List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,exists_eq_left,forall_eq_or_imp,forall_eq,
    checkerIdle_exact ha,checkerIdle_exact hb,checkerPassed_exact ha,checkerPassed_exact hb,
    checkerHead_exact ha,checkerHead_exact hb,Formula.equal_ne_zero]
  cases hc : c.checker <;> cases hd : d.checker <;>
    simp [represent_int ha,represent_int hb,cellRecord,integers,hc,hd,checkerIndex]
  all_goals simp only [Fin.ext_iff]
  all_goals exact eq_comm
lemma checkerPair_exact : (checkerPair a b).eval v≠0 ↔ CheckerPair c d := by
  have HL : (¬∃ x,c.checker=.passed x) ↔ Palette.LastOK c.checker := by
    cases c.checker <;> simp [Palette.LastOK]
  simp only [checkerPair,Formula.and_ne_zero,implies_ne_zero,Formula.neg_ne_zero,
    palette_exact ha,palette_exact hb,stop_exact hb,palettePair_exact ha hb,checkerPassed_exact ha,HL,CheckerPair]
lemma pair_exact (Q : Formula ι) (hQ : Q.eval v=q) :
    (pair a b Q).eval v≠0 ↔ Pair c d := by
  simp only [pair,Formula.and_ne_zero,skeletonPair_exact ha hb Q hQ,checkerPair_exact ha hb,Pair]
omit hb in
lemma passedOwn_exact : (passedOwn a).eval v≠0 ↔ ∃x,c.pos=.palette x ∧ c.checker=.passed x := by
  simp only [passedOwn,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    palette_exact ha,checkerPassed_exact ha,Formula.equal_ne_zero]
  cases hp : c.pos <;> cases hc : c.checker <;>
    simp [represent_int ha,cellRecord,integers,hp,hc,Cell.isPalette,checkerIndex,positionIndex]
  simp only [Fin.ext_iff]
  exact eq_comm
lemma duplicate_exact : (duplicate a b).eval v≠0 ↔ ∃x,c.pos=.palette x ∧ d.pos=.palette x := by
  simp only [duplicate,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    palette_exact ha,palette_exact hb,Formula.equal_ne_zero]
  cases hp : c.pos <;> cases hr : d.pos <;>
    simp [represent_int ha,represent_int hb,cellRecord,integers,hp,hr,Cell.isPalette,positionIndex]
  simp only [Fin.ext_iff]
  exact eq_comm
lemma missing_exact : (missing a b).eval v≠0 ↔
    ∃ x y,c.pos=.palette x ∧ c.checker=.head y ∧ d.pos=.stop ∧ x≠y := by
  simp only [missing,Formula.all_ne_zero,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    palette_exact ha,checkerHead_exact ha,stop_exact hb,Formula.neg_ne_zero,Formula.equal_ne_zero]
  cases hp : c.pos <;> cases hc : c.checker <;>
    simp [represent_int ha,cellRecord,integers,hp,hc,Cell.isPalette,checkerIndex,positionIndex]
  simp only [Fin.ext_iff]
  simp
omit hb [NeZero q] in
lemma semanticZero_exact (S : Schedule q) (truth : Formula ι)
    (ht : truth.eval v=boolean ((S.clause c.metadata.task c.head.clause).truth c.head.reg)) :
    (semanticZero a truth).eval v≠0 ↔ SemanticZero S c := by
  simp only [semanticZero,Formula.and_ne_zero,Formula.any_ne_zero,Formula.neg_ne_zero,
    List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,exists_eq_left,
    marker_exact ha,phase_exact ha,regZero_exact ha,Formula.equal_ne_zero,Formula.constant_eval,ht]
  simp [represent_flag ha,cellRecord,flags,SemanticZero]
omit hb in
lemma unaryZero_exact (S : Schedule q) (size count truth : Formula ι) (n : ℕ)
    (hn : size.eval v=n) (hc : count.eval v=(S.count c.metadata.task).val)
    (ht : truth.eval v=boolean ((S.clause c.metadata.task c.head.clause).truth c.head.reg)) :
    (unaryZero a size count truth).eval v≠0 ↔ UnaryZero S n c := by
  simp only [unaryZero,Formula.any_ne_zero,Formula.neg_ne_zero,List.mem_cons,List.not_mem_nil,
    or_false,exists_eq_or_imp,exists_eq_left,formats_exact ha S size count n hn hc,
    semanticZero_exact ha S truth ht,passedOwn_exact ha,UnaryZero]
lemma binaryZero_exact (Q : Formula ι) (hQ : Q.eval v=q) :
    (binaryZero a b Q).eval v≠0 ↔ BinaryZero c d := by
  simp only [binaryZero,Formula.any_ne_zero,Formula.neg_ne_zero,List.mem_cons,List.not_mem_nil,
    or_false,exists_eq_or_imp,exists_eq_left,pair_exact ha hb Q hQ,duplicate_exact ha hb,
    missing_exact ha hb,BinaryZero]
end SourceBurnside.CellFormula

end OAI
