import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.State
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack6

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations
namespace WordList.Find

def optionEncode : Option (List Bool) → List Bool
  | none => []
  | some w => true::w

def context : List Bool → List Bool := extractPrefix
def item : List Bool → List Bool := extractPrefix ∘ discardPrefix
def accum : List Bool → List Bool := discardPrefix ∘ discardPrefix
noncomputable def context_computes : PolyComputes context := extractPrefix_computes
noncomputable def item_computes : PolyComputes item := discardPrefix_computes.comp extractPrefix_computes
noncomputable def accum_computes : PolyComputes accum := discardPrefix_computes.comp discardPrefix_computes

def operation (p : List Bool → Bool) (x : List Bool) : List Bool :=
  if accum x=[] then if p (pairBits (context x,item x)) then true::item x else [] else accum x
noncomputable def operation_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (operation p) := by
  have hc := (context_computes.pair item_computes).comp hp
  have hi := item_computes.comp (prefix_computes true)
  have h₁ := hc.cond hi (const_computes [])
  have h₂ := (accum_computes.comp isEmpty_computes).cond h₁ accum_computes
  unfold operation
  simpa only [Function.comp_def,decide_eq_true_eq] using h₂

lemma operation_pack (p : List Bool → Bool) (ctx a w : List Bool) :
    Fold.operation (operation p) ctx a w=
      if a=[] then if p (pairBits (ctx,w)) then true::w else [] else a := by
  simp only [Fold.operation,operation,accum,item,context,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits]
lemma fold_result (p : List Bool → Bool) (ctx a : List Bool) (ws : List (List Bool)) :
    ws.foldl (Fold.operation (operation p) ctx) a=
      if a=[] then optionEncode (ws.find? (fun w=>p (pairBits (ctx,w)))) else a := by
  induction ws generalizing a with
  | nil => simp only [List.foldl_nil,List.find?_nil,optionEncode]; split_ifs with h <;> simp_all
  | cons w ws ih =>
    rw [List.foldl_cons,operation_pack,ih]
    by_cases ha : a=[]
    · subst a
      simp only [ite_true]
      cases hp : p (pairBits (ctx,w)) <;> simp [hp,optionEncode]
    · simp only [ha,ite_false]

noncomputable def run (p : List Bool → Bool) : List Bool → List Bool :=
  Fold.run (operation p) (3*Polynomial.X+3) ∘
    (fun x=>Fold.pack (discardPrefix x) (extractPrefix x) [])
noncomputable def run_computes {p : List Bool → Bool} (hp : PolyComputes (fun x=>[p x])) :
    PolyComputes (run p) :=
  (Fold.pack_computes discardPrefix_computes extractPrefix_computes (const_computes [])).comp
    (Fold.run_computes (operation_computes hp) (3*Polynomial.X+3))

lemma optionEncode_bound {ws : List (List Bool)} {p : List Bool → Bool} :
    (optionEncode (ws.find? p)).length≤(encode ws).length+1 := by
  cases h : ws.find? p with
  | none => simp only [optionEncode,List.length_nil]; omega
  | some w =>
    have hw : w∈ws := List.mem_of_find?_eq_some h
    have hh := length_member_le_encode hw
    simpa only [optionEncode,List.length_cons] using Nat.add_le_add_right hh 1
lemma run_encode (p : List Bool → Bool) (ctx : List Bool) (ws : List (List Bool)) :
    run p (pairBits (ctx,encode ws))=optionEncode (ws.find? (fun w=>p (pairBits (ctx,w)))) := by
  unfold run
  simp only [Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [Fold.run_encode (operation p) (3*Polynomial.X+3) ctx [] ws ((encode ws).length+1)]
  · simp only [fold_result,ite_true]
  · intro j
    rw [fold_result,ite_eq_left rfl]
    have hb : (optionEncode ((ws.take j).find? (fun w=>p (pairBits (ctx,w))))).length≤
        (encode (ws.take j)).length+1 := optionEncode_bound
    have he := length_encode_append (ws.take j) (ws.drop j)
    rw [List.take_append_drop] at he
    omega
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,Fold.length_pack,List.length_nil]
    omega
end WordList.Find
end
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryRow
open RationalMatrix

def encode {n : ℕ} (r : Row n) : List Bool := pairBits (rowEncode r.coeff,BinaryRational.encode r.bound)
def rowsEncode {n : ℕ} (rows : List (Row n)) : List Bool := WordList.encode (rows.map encode)
def bound : List Bool → List Bool := discardPrefix ∘ discardPrefix
def coeff : List Bool → List Bool := extractPrefix ∘ discardPrefix
noncomputable def bound_computes : PolyComputes bound := discardPrefix_computes.comp discardPrefix_computes
noncomputable def coeff_computes : PolyComputes coeff := discardPrefix_computes.comp extractPrefix_computes
def dotInput (x : List Bool) : List Bool := pairBits (coeff x,extractPrefix x)
noncomputable def dotInput_computes : PolyComputes dotInput := coeff_computes.pair extractPrefix_computes
noncomputable def dot : List Bool → List Bool := RationalArray.dotListsWords ∘ dotInput
noncomputable def dot_computes : PolyComputes dot := dotInput_computes.comp RationalArray.dotListsWords_computes
noncomputable def good (x : List Bool) : Bool := decide (BinaryRational.decode (dot x)≤BinaryRational.decode (bound x))
noncomputable def good_computes : PolyComputes (fun x=>[good x]) := by
  have hh := ((RatOps.ofWords dot_computes).pair (RatOps.ofWords bound_computes)).comp BinaryRational.leWords_computes
  simpa only [good,Function.comp_def,BinaryRational.leWords_pair] using hh
noncomputable def bad (x : List Bool) : Bool := !good x
noncomputable def bad_computes : PolyComputes (fun x=>[bad x]) := by
  have hh := good_computes.cond (const_computes [false]) (const_computes [true])
  change PolyComputes (fun x=>[!good x])
  convert hh using 1
  funext x
  cases good x <;> rfl
lemma bad_pack {n : ℕ} (r : Row n) (c : Fin n → ℚ) :
    bad (pairBits (rowEncode c,encode r))=decide (r.bound<r.value c) := by
  simp only [bad,good,dot,Function.comp_apply,dotInput,coeff,bound,encode,
    extractPrefix_pairBits,discardPrefix_pairBits,RationalMatrix.dotListsWords_ofFn,
    BinaryRational.decode_encode,Row.value]
  simp only [←decide_not,not_le]
  rfl
lemma find_map {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) :
    (rows.map encode).find? (fun w=>bad (pairBits (rowEncode c,w)))=
      (Ellipsoid.badRow rows c).map encode := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.map_cons,List.find?_cons,bad_pack,Ellipsoid.badRow] at *
    split <;> simp_all
noncomputable def run : List Bool → List Bool := WordList.Find.run bad
noncomputable def run_computes : PolyComputes run := WordList.Find.run_computes bad_computes
lemma run_pack {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) :
    run (pairBits (rowEncode c,rowsEncode rows))=
      WordList.Find.optionEncode ((Ellipsoid.badRow rows c).map encode) := by
  rw [run,rowsEncode,WordList.Find.run_encode,find_map]
end BinaryRow
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

def stateEncode {n : ℕ} (S : State n) : List Bool := pairBits (encode S.shape,rowEncode S.center)
def pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : List Bool :=
  pairBits (n.bits,pairBits (D.bits,pairBits (BinaryRow.rowsEncode rs,stateEncode S)))
def dim : List Bool → List Bool := extractPrefix
def rest : List Bool → List Bool := discardPrefix
def precision : List Bool → List Bool := extractPrefix ∘ rest
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest
def rows : List Bool → List Bool := extractPrefix ∘ rest₂
def stored : List Bool → List Bool := discardPrefix ∘ rest₂
def shape : List Bool → List Bool := extractPrefix ∘ stored
def center : List Bool → List Bool := discardPrefix ∘ stored
noncomputable def dim_computes : PolyComputes dim := extractPrefix_computes
noncomputable def precision_computes : PolyComputes precision := discardPrefix_computes.comp extractPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := discardPrefix_computes.comp discardPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₂_computes.comp extractPrefix_computes
noncomputable def stored_computes : PolyComputes stored := rest₂_computes.comp discardPrefix_computes
noncomputable def shape_computes : PolyComputes shape := stored_computes.comp extractPrefix_computes
noncomputable def center_computes : PolyComputes center := stored_computes.comp discardPrefix_computes
lemma dim_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : dim (pack D rs S)=n.bits := by
  simp only [dim,pack,extractPrefix_pairBits]
lemma precision_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : precision (pack D rs S)=D.bits := by
  simp only [precision,rest,Function.comp_apply,pack,extractPrefix_pairBits,discardPrefix_pairBits]
lemma rows_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : rows (pack D rs S)=BinaryRow.rowsEncode rs := by
  simp only [rows,rest₂,rest,Function.comp_apply,pack,extractPrefix_pairBits,discardPrefix_pairBits]
lemma stored_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : stored (pack D rs S)=stateEncode S := by
  simp only [stored,rest₂,rest,Function.comp_apply,pack,discardPrefix_pairBits]
lemma shape_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : shape (pack D rs S)=encode S.shape := by
  simp only [shape,Function.comp_apply,stored_pack,stateEncode,extractPrefix_pairBits]
lemma center_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : center (pack D rs S)=rowEncode S.center := by
  simp only [center,Function.comp_apply,stored_pack,stateEncode,discardPrefix_pairBits]
noncomputable def found (x : List Bool) : List Bool := BinaryRow.run (pairBits (center x,rows x))
noncomputable def found_computes : PolyComputes found := (center_computes.pair rows_computes).comp BinaryRow.run_computes
lemma found_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) :
    found (pack D rs S)=WordList.Find.optionEncode ((badRow rs S.center).map BinaryRow.encode) := by
  simp only [found,center_pack,rows_pack,BinaryRow.run_pack]
noncomputable def direction (x : List Bool) : List Bool := extractPrefix (found x).tail
noncomputable def direction_computes : PolyComputes direction :=
  (found_computes.comp tail_computes).comp extractPrefix_computes
lemma direction_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) (r : Row n)
    (h : badRow rs S.center=some r) : direction (pack D rs S)=rowEncode r.coeff := by
  simp only [direction,found_pack,h,Option.map_some,WordList.Find.optionEncode,List.tail_cons,
    BinaryRow.encode,extractPrefix_pairBits]

noncomputable def normWords (x : List Bool) : List Bool :=
  RationalArray.dotListsWords (pairBits (direction x,direction x))
noncomputable def normWords_computes : PolyComputes normWords :=
  (direction_computes.pair direction_computes).comp RationalArray.dotListsWords_computes
noncomputable def zeroDirection (x : List Bool) : Bool := decide (BinaryRational.decode (normWords x)≤0)
noncomputable def zeroDirection_computes : PolyComputes (fun x=>[zeroDirection x]) := by
  have hh := ((RatOps.ofWords normWords_computes).pair (RatOps.const 0)).comp BinaryRational.leWords_computes
  simpa only [zeroDirection,Function.comp_def,BinaryRational.leWords_pair] using hh
lemma normWords_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) (r : Row n)
    (h : badRow rs S.center=some r) :
    normWords (pack D rs S)=BinaryRational.encode (r.coeff ⬝ᵥ r.coeff) := by
  simp only [normWords,direction_pack D rs S r h,RationalMatrix.dotListsWords_ofFn]
  rfl
lemma zeroDirection_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) (r : Row n)
    (h : badRow rs S.center=some r) : zeroDirection (pack D rs S)=decide (r.coeff=0) := by
  rw [zeroDirection,normWords_pack D rs S r h,BinaryRational.decode_encode]
  congr 1
  have hn : (0:ℚ)≤r.coeff ⬝ᵥ r.coeff := by
    unfold dotProduct
    exact Finset.sum_nonneg (fun i _=>mul_self_nonneg (r.coeff i))
  exact propext ⟨fun hh=>dotProduct_self_eq_zero.mp (le_antisymm hh hn),
    fun hh=>by rw [hh,dotProduct_zero]⟩

noncomputable def cutInput (x : List Bool) : List Bool :=
  pairBits (dim x,pairBits (shape x,pairBits (direction x,pairBits (center x,precision x))))
noncomputable def cutInput_computes : PolyComputes cutInput :=
  dim_computes.pair (shape_computes.pair (direction_computes.pair (center_computes.pair precision_computes)))
lemma cutInput_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) (r : Row n)
    (h : badRow rs S.center=some r) : cutInput (pack D rs S)=BinaryEllipsoidCut.pack S.shape r.coeff S.center D := by
  simp only [cutInput,dim_pack,shape_pack,direction_pack D rs S r h,center_pack,precision_pack,BinaryEllipsoidCut.pack]
noncomputable def updated (x : List Bool) : List Bool :=
  pairBits (BinaryEllipsoidCut.shapeWords (cutInput x),BinaryEllipsoidCut.centerWords (cutInput x))
noncomputable def updated_computes : PolyComputes updated := by
  unfold updated
  simpa only [Function.comp_def] using
    (cutInput_computes.comp BinaryEllipsoidCut.shapeWords_computes).pair
      (cutInput_computes.comp BinaryEllipsoidCut.centerWords_computes)
noncomputable def nextState (x : List Bool) : List Bool :=
  if found x=[] then stored x else if zeroDirection x then stored x else updated x
noncomputable def nextState_computes : PolyComputes nextState := by
  have hh := (found_computes.comp isEmpty_computes).cond stored_computes
    (zeroDirection_computes.cond stored_computes updated_computes)
  unfold nextState
  simpa only [Function.comp_def,decide_eq_true_eq] using hh
lemma nextState_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) :
    nextState (pack D rs S)=stateEncode (advance D rs S) := by
  unfold nextState advance
  rw [found_pack,stored_pack]
  cases h : badRow rs S.center with
  | none => simp only [Option.map_none,WordList.Find.optionEncode,ite_true]
  | some r =>
    simp only [Option.map_some,WordList.Find.optionEncode,reduceCtorEq,ite_false,
      zeroDirection_pack D rs S r h,decide_eq_true_eq]
    split_ifs with hz
    · rfl
    · simp only [updated,cutInput_pack D rs S r h,BinaryEllipsoidCut.shapeWords_pack,
        BinaryEllipsoidCut.centerWords_pack,stateEncode]
noncomputable def run (x : List Bool) : List Bool :=
  pairBits (dim x,pairBits (precision x,pairBits (rows x,nextState x)))
noncomputable def run_computes : PolyComputes run :=
  dim_computes.pair (precision_computes.pair (rows_computes.pair nextState_computes))
lemma run_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) :
    run (pack D rs S)=pack D rs (advance D rs S) := by
  simp only [run,dim_pack,precision_pack,rows_pack,nextState_pack]
  rfl
lemma iterate_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) (t : ℕ) :
    run^[t] (pack D rs S)=pack D rs (Ellipsoid.iterate D rs S t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,run_pack]; rfl
end BinaryEllipsoidAdvance
end MetricKMedianRecovery.BitMachine

end OAI
