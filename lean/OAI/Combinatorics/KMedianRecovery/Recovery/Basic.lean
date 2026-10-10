import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Rectangular

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace RatOps
noncomputable def le {f g : List Bool → ℚ}
    (hf : PolyComputes (fun x=>BinaryRational.encode (f x)))
    (hg : PolyComputes (fun x=>BinaryRational.encode (g x))) :
    PolyComputes (fun x=>[decide (f x≤g x)]) := by
  have hh := (hf.pair hg).comp BinaryRational.leWords_computes
  simpa only [Function.comp_def,BinaryRational.leWords_pair] using hh
end RatOps
namespace MetricTable
open WordList

def context : List Bool → List Bool := extractPrefix ∘ extractPrefix
def row : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix
noncomputable def context_computes : PolyComputes context := extractPrefix_computes.comp extractPrefix_computes
noncomputable def row_computes : PolyComputes row := extractPrefix_computes.comp discardPrefix_computes
noncomputable def col_computes : PolyComputes col := discardPrefix_computes
noncomputable def getRow (x : List Bool) : List Bool := Lookup.run (pairBits (row x,context x))
noncomputable def getRow_computes : PolyComputes getRow := (row_computes.pair context_computes).comp Lookup.run_computes
noncomputable def get (x : List Bool) : List Bool := Lookup.run (pairBits (col x,getRow x))
noncomputable def get_computes : PolyComputes get := (col_computes.pair getRow_computes).comp Lookup.run_computes
lemma get_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (f : Fin m) (j : Fin d) :
    get (pairBits (pairBits (Rectangular.encode distance,f.val.bits),j.val.bits))=
      BinaryRational.encode (distance f j) := by
  simp only [get,getRow,context,row,col,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,Rectangular.encode,lookup_ofFn,
    RationalMatrix.rowEncode_eq]
end MetricTable
namespace BinaryOpeningActivity
open WordList

def context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ) (j : Fin d) : List Bool :=
  pairBits (pairBits (Rectangular.encode distance,j.val.bits),
    pairBits (BinaryRational.encode v,BinaryRational.encode z))
def indices {m : ℕ} (fs : List (Fin m)) : List Bool :=
  WordList.encode (fs.map (fun f=>f.val.bits))
def table : List Bool → List Bool := extractPrefix ∘ extractPrefix ∘ extractPrefix
def client : List Bool → List Bool := discardPrefix ∘ extractPrefix ∘ extractPrefix
def paramV : List Bool → List Bool := extractPrefix ∘ discardPrefix ∘ extractPrefix
def paramZ : List Bool → List Bool := discardPrefix ∘ discardPrefix ∘ extractPrefix
noncomputable def table_computes : PolyComputes table :=
  (extractPrefix_computes.comp extractPrefix_computes).comp extractPrefix_computes
noncomputable def client_computes : PolyComputes client :=
  (extractPrefix_computes.comp extractPrefix_computes).comp discardPrefix_computes
noncomputable def paramV_computes : PolyComputes paramV :=
  (extractPrefix_computes.comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def paramZ_computes : PolyComputes paramZ :=
  (extractPrefix_computes.comp discardPrefix_computes).comp discardPrefix_computes
noncomputable def distanceWord (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (table x,discardPrefix x),client x))
noncomputable def distanceWord_computes : PolyComputes distanceWord := by
  unfold distanceWord
  simpa only [Function.comp_def] using
    (PolyComputes.comp
      (f:=fun input=>pairBits (pairBits (table input,discardPrefix input),client input))
      (g:=MetricTable.get)
      ((table_computes.pair discardPrefix_computes).pair client_computes)
      MetricTable.get_computes)
noncomputable def fails (x : List Bool) : Bool := decide
  ((1-3*BinaryRational.decode (paramV x))*BinaryRational.decode (distanceWord x)≤
    BinaryRational.decode (paramZ x))
noncomputable def fails_computes : PolyComputes (fun x=>[fails x]) :=
  RatOps.le
    (RatOps.mul (RatOps.sub (RatOps.const 1) (RatOps.mul (RatOps.const 3)
      (RatOps.ofWords paramV_computes))) (RatOps.ofWords distanceWord_computes))
    (RatOps.ofWords paramZ_computes)
lemma fails_context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (j : Fin d) (f : Fin m) :
    fails (pairBits (context distance v z j,f.val.bits))=decide ((1-3*v)*distance f j≤z) := by
  unfold fails distanceWord
  simp only [table,client,paramV,paramZ,context,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode]
  rw [MetricTable.get_pack,BinaryRational.decode_encode]
noncomputable def run (x : List Bool) : List Bool := [decide (Find.run fails x=[])]
noncomputable def run_computes : PolyComputes run := (Find.run_computes fails_computes).comp isEmpty_computes
lemma optionEncode_nil_iff (o : Option (List Bool)) : Find.optionEncode o=[] ↔ o=none := by
  cases o <;> simp [Find.optionEncode]
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (j : Fin d) (fs : List (Fin m)) :
    run (pairBits (context distance v z j,indices fs))=
      [decide (∀ f∈fs,z<(1-3*v)*distance f j)] := by
  unfold run indices
  rw [Find.run_encode]
  congr 1
  apply decide_eq_decide.mpr
  rw [optionEncode_nil_iff,List.find?_eq_none]
  simp only [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,fails_context,
    Bool.not_eq_true,decide_eq_false_iff_not,not_le]
lemma run_source {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (j : Fin d) (W : Finset (Fin m)) :
    run (pairBits (context distance v z j,
      indices ((EffectiveOpenability.subtypeList W).map Subtype.val)))=
      [decide (EffectiveOpenability.active distance v z W j)] := by
  rw [run_pack]
  congr 1
  apply decide_eq_decide.mpr
  simp only [EffectiveOpenability.active,List.mem_map,forall_exists_index,and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro h f hf
    exact h ⟨f,hf⟩ (EffectiveOpenability.mem_subtypeList W ⟨f,hf⟩)
  · intro h f _
    exact h f.val f.property
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
namespace RationalMin
open WordList
def choose (x : List Bool) : List Bool :=
  if BinaryRational.decode (Find.item x)≤BinaryRational.decode (Fold.accum x)
  then Find.item x else Fold.accum x
noncomputable def choose_computes : PolyComputes choose := by
  have hh := (RatOps.le (RatOps.ofWords Find.item_computes)
    (RatOps.ofWords Fold.accum_computes)).cond Find.item_computes Fold.accum_computes
  unfold choose
  simpa only [decide_eq_true_eq] using hh
lemma operation_pair (ctx a w : List Bool) :
    Fold.operation choose ctx a w=if BinaryRational.decode w≤BinaryRational.decode a then w else a := by
  simp only [Fold.operation,choose,Find.item,Fold.accum,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
lemma fold_encode (qs : List ℚ) (a : ℚ) (ctx : List Bool) :
    (qs.map BinaryRational.encode).foldl (Fold.operation choose ctx) (BinaryRational.encode a)=
      BinaryRational.encode (qs.foldl min a) := by
  induction qs generalizing a with
  | nil=>rfl
  | cons q qs ih=>
    simp only [List.map_cons,List.foldl_cons,operation_pair,BinaryRational.decode_encode]
    by_cases h : q≤a
    · simp only [h,ite_true,min_eq_right h,ih]
    · have ha : a≤q := le_of_lt (lt_of_not_ge h)
      simp only [h,ite_false,min_eq_left ha,ih]
lemma fold_length (ws : List (List Bool)) (a ctx : List Bool) :
    (ws.foldl (Fold.operation choose ctx) a).length≤a.length+(encode ws).length := by
  induction ws generalizing a with
  | nil=>simp only [List.foldl_nil,encode,List.length_nil,Nat.add_zero,Nat.le_refl]
  | cons w ws ih=>
    rw [List.foldl_cons,operation_pair]
    simp only [encode,length_cons]
    split_ifs
    · have hh := ih w; omega
    · have hh := ih a; omega

def seed (x : List Bool) : List Bool := if x=[] then BinaryRational.encode 0 else WordList.head x
noncomputable def seed_computes : PolyComputes seed := by
  have hh := isEmpty_computes.cond (const_computes (BinaryRational.encode 0)) WordList.head_computes
  unfold seed
  simpa only [decide_eq_true_eq] using hh
lemma seed_encode (qs : List ℚ) : seed (RationalArray.encode qs)=BinaryRational.encode (qs.head?.getD 0) := by
  cases qs with
  | nil=>rfl
  | cons q qs=>simp only [seed,RationalArray.encode,List.map_cons,encode,cons_ne_nil,
      ite_false,head_cons,List.head?_cons,Option.getD_some]
noncomputable def run (x : List Bool) : List Bool :=
  Fold.run choose (3*Polynomial.X+3) (Fold.pack x [] (seed x))
noncomputable def run_computes : PolyComputes run :=
  (Fold.pack_computes id_computes (const_computes []) seed_computes).comp
    (Fold.run_computes choose_computes (3*Polynomial.X+3))
def minimum (qs : List ℚ) : ℚ := qs.foldl min (qs.head?.getD 0)
lemma run_encode (qs : List ℚ) : run (RationalArray.encode qs)=BinaryRational.encode (minimum qs) := by
  unfold run
  rw [show RationalArray.encode qs=encode (qs.map BinaryRational.encode) from rfl]
  rw [Fold.run_encode choose (3*Polynomial.X+3) [] (seed (encode (qs.map BinaryRational.encode)))
    (qs.map BinaryRational.encode)
    ((seed (encode (qs.map BinaryRational.encode))).length+(encode (qs.map BinaryRational.encode)).length)]
  · rw [show seed (encode (qs.map BinaryRational.encode))=BinaryRational.encode (qs.head?.getD 0) from seed_encode qs,
      fold_encode]
    rfl
  · intro j
    have hh := fold_length ((qs.map BinaryRational.encode).take j)
      (seed (encode (qs.map BinaryRational.encode))) []
    exact hh.trans (Nat.add_le_add_left (length_encode_take _ _) _)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil]
    omega

lemma fold_lower (qs : List ℚ) (a u : ℚ) (ha : u≤a) (hq : ∀ q∈qs,u≤q) : u≤qs.foldl min a := by
  induction qs generalizing a with
  | nil=>exact ha
  | cons q qs ih=>
    rw [List.foldl_cons]
    exact ih (min a q) (le_min ha (hq q (by simp))) (by intro r hr; exact hq r (by simp [hr]))
lemma fold_le_init (qs : List ℚ) (a : ℚ) : qs.foldl min a≤a := by
  induction qs generalizing a with
  | nil=>exact le_rfl
  | cons q qs ih=>exact (ih (min a q)).trans (min_le_left a q)
lemma fold_le_mem (qs : List ℚ) (a q : ℚ) (hq : q∈qs) : qs.foldl min a≤q := by
  induction qs generalizing a with
  | nil=>simp only [List.not_mem_nil] at hq
  | cons r rs ih=>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hq with rfl|hq
    · exact (fold_le_init rs (min a q)).trans (min_le_right a q)
    · exact ih (min a r) hq
lemma minimum_lower (qs : List ℚ) (u : ℚ) (hne : qs≠[]) (hu : ∀q∈qs,u≤q) : u ≤ minimum qs := by
  cases qs with
  | nil=>exact (hne rfl).elim
  | cons q qs=>
    apply fold_lower
    · exact hu q (by simp)
    · exact hu
lemma minimum_le_mem (qs : List ℚ) (q : ℚ) (hq : q∈qs) : minimum qs≤q := fold_le_mem qs _ q hq
end RationalMin
end MetricKMedianRecovery.BitMachine

end OAI
