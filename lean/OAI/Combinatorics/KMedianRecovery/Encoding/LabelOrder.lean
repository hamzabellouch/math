import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.SortMath
import OAI.Combinatorics.KMedianRecovery.Recovery.DecisionOps
import OAI.Combinatorics.KMedianRecovery.Branching.CopyAge

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [LinearOrder V]
def rationalHeight : Label V → ℚ
  | .inl _=>0
  | .inr c=>c.2.2

lemma label_lt (a b : Label V) : @LT.lt _ (labelLinearOrder.toLT) a b ↔
    level a<level b ∨ level a=level b ∧
      (parent a<parent b ∨ parent a=parent b ∧ rationalHeight a<rationalHeight b) := by
  change Sum.Lex (fun a b : V=>a<b)
    (fun a b : ℕ × V × ℚ=>Prod.Lex (·<·) (Prod.Lex (·<·) (·<·)) a b) a b ↔ _
  cases a with
  | inl a=>
    cases b with
    | inl b=>simp [Sum.lex_inl_inl,level,parent,rationalHeight]
    | inr b=>simp [Sum.Lex.sep,level]
  | inr a=>
    cases b with
    | inl b=>simp [Sum.lex_inr_inl,level]
    | inr b=>simp [Sum.lex_inr_inr,Prod.lex_iff,level,parent,root,rationalHeight]

omit [LinearOrder V] in
lemma rows_height {d : ℕ} (distance : V → Fin d → ℚ) (x : Label V) (j : Fin d) :
    rows distance x j=distance (parent x) j+max (rationalHeight x) 0 := by
  cases x <;> simp [rows,parent,rationalHeight]
end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves

def encode {m : ℕ} (x : Label (Fin m)) : List Bool :=
  pairBits ((level x).bits,pairBits ((parent x).val.bits,BinaryRational.encode (rationalHeight x)))
def levelWords : List Bool → List Bool := extractPrefix
def parentWords : List Bool → List Bool := extractPrefix ∘ discardPrefix
def heightWords : List Bool → List Bool := discardPrefix ∘ discardPrefix
noncomputable def levelWords_computes : PolyComputes levelWords := extractPrefix_computes
noncomputable def parentWords_computes : PolyComputes parentWords := discardPrefix_computes.comp extractPrefix_computes
noncomputable def heightWords_computes : PolyComputes heightWords := discardPrefix_computes.comp discardPrefix_computes

@[simp] lemma levelWords_encode {m : ℕ} (x : Label (Fin m)) : levelWords (encode x)=(level x).bits := by
  simp only [levelWords,encode,extractPrefix_pairBits]
@[simp] lemma parentWords_encode {m : ℕ} (x : Label (Fin m)) : parentWords (encode x)=(parent x).val.bits := by
  simp only [parentWords,encode,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
@[simp] lemma heightWords_encode {m : ℕ} (x : Label (Fin m)) : heightWords (encode x)=BinaryRational.encode (rationalHeight x) := by
  simp only [heightWords,encode,Function.comp_apply,discardPrefix_pairBits]

def lt (x : List Bool) : Bool :=
  decide (value (levelWords (extractPrefix x))<value (levelWords (discardPrefix x))) ||
    (decide (value (levelWords (extractPrefix x))=value (levelWords (discardPrefix x))) &&
      (decide (value (parentWords (extractPrefix x))<value (parentWords (discardPrefix x))) ||
        (decide (value (parentWords (extractPrefix x))=value (parentWords (discardPrefix x))) &&
          decide (BinaryRational.decode (heightWords (extractPrefix x))<BinaryRational.decode (heightWords (discardPrefix x))))))
noncomputable def lt_computes : PolyComputes (fun x=>[lt x]) :=
  (NatOps.lt (extractPrefix_computes.comp levelWords_computes) (discardPrefix_computes.comp levelWords_computes)).or
    ((NatOps.eq (extractPrefix_computes.comp levelWords_computes) (discardPrefix_computes.comp levelWords_computes)).and
      ((NatOps.lt (extractPrefix_computes.comp parentWords_computes) (discardPrefix_computes.comp parentWords_computes)).or
        ((NatOps.eq (extractPrefix_computes.comp parentWords_computes) (discardPrefix_computes.comp parentWords_computes)).and
          (RatOps.lt (RatOps.ofWords (extractPrefix_computes.comp heightWords_computes))
            (RatOps.ofWords (discardPrefix_computes.comp heightWords_computes))))))

lemma lt_pair {m : ℕ} (a b : Label (Fin m)) : lt (pairBits (encode a,encode b))=
    decide (level a<level b ∨ level a=level b ∧
      ((parent a).val<(parent b).val ∨ (parent a).val=(parent b).val ∧ rationalHeight a<rationalHeight b)) := by
  simp only [lt,extractPrefix_pairBits,discardPrefix_pairBits,levelWords_encode,parentWords_encode,
    heightWords_encode,value_bits,BinaryRational.decode_encode,Bool.decide_or,Bool.decide_and]

def orderedSort {α : Type*} [LinearOrder α] (s : Finset α) : List α := s.sort (·≤·)

noncomputable def sort : List Bool → List Bool := WordList.Sort.run lt
noncomputable def sort_computes : PolyComputes sort := WordList.Sort.run_computes lt_computes
lemma sort_encode {m : ℕ} (xs : List (Label (Fin m))) :
    sort (WordList.encode (xs.map encode))=WordList.encode ((orderedSort xs.toFinset).map encode) := by
  apply WordList.Sort.run_encode
  intro a b
  rw [lt_pair]
  apply decide_eq_decide.mpr
  simpa only [Fin.lt_def,Fin.ext_iff] using (label_lt a b).symm

def table : List Bool → List Bool := extractPrefix ∘ extractPrefix
def label : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix
noncomputable def table_computes : PolyComputes table := extractPrefix_computes.comp extractPrefix_computes
noncomputable def label_computes : PolyComputes label := extractPrefix_computes.comp discardPrefix_computes
noncomputable def col_computes : PolyComputes col := discardPrefix_computes
noncomputable def rawRow (x : List Bool) : List Bool :=
  MetricTable.get (pairBits (pairBits (table x,parentWords (label x)),col x))
attribute [local irreducible] MetricTable.get
noncomputable def rawRow_computes : PolyComputes rawRow :=
  ((table_computes.pair (label_computes.comp parentWords_computes)).pair col_computes).comp MetricTable.get_computes
noncomputable def row (x : List Bool) : List Bool :=
  BinaryRational.encode (BinaryRational.decode (rawRow x)+max (BinaryRational.decode (heightWords (label x))) 0)
noncomputable def row_computes : PolyComputes row :=
  RatOps.add (RatOps.ofWords rawRow_computes)
    (RatOps.max (RatOps.ofWords (label_computes.comp heightWords_computes)) (RatOps.const 0))
lemma row_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (x : Label (Fin m)) (j : Fin d) :
    row (pairBits (pairBits (Rectangular.encode distance,encode x),j.val.bits))=
      BinaryRational.encode (rows distance x j) := by
  simp only [row,rawRow,table,label,col,Function.comp_apply,extractPrefix_pairBits,
    discardPrefix_pairBits,parentWords_encode,heightWords_encode,MetricTable.get_pack,BinaryRational.decode_encode,rows_height]
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelMatrix
open WordOperations WordList RationalLeaves
attribute [local irreducible] mapWith

def table : List Bool → List Bool := extractPrefix ∘ extractPrefix ∘ extractPrefix
def width : List Bool → List Bool := discardPrefix ∘ extractPrefix ∘ extractPrefix
def item : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix
noncomputable def table_computes : PolyComputes table := (extractPrefix_computes.comp extractPrefix_computes).comp extractPrefix_computes
noncomputable def width_computes : PolyComputes width := (extractPrefix_computes.comp extractPrefix_computes).comp discardPrefix_computes
noncomputable def item_computes : PolyComputes item := extractPrefix_computes.comp discardPrefix_computes
noncomputable def col_computes : PolyComputes col := discardPrefix_computes
noncomputable def entry (x : List Bool) : List Bool :=
  BinaryLabel.row (pairBits (pairBits (table x,item x),col x))
noncomputable def entry_computes : PolyComputes entry :=
  ((table_computes.pair item_computes).pair col_computes).comp BinaryLabel.row_computes
lemma entry_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (x : Label (Fin m)) (j : Fin d) :
    entry (pairBits (pairBits (pairBits (Rectangular.encode distance,List.replicate d true),BinaryLabel.encode x),j.val.bits))=
      BinaryRational.encode (rows distance x j) := by
  simp only [entry,table,item,col,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,BinaryLabel.row_pack]

noncomputable def row (x : List Bool) : List Bool :=
  mapWith entry (pairBits (x,BinaryEllipsoidInitial.indices (discardPrefix (extractPrefix x))))
noncomputable def row_computes : PolyComputes row :=
  (id_computes.pair ((extractPrefix_computes.comp discardPrefix_computes).comp BinaryEllipsoidInitial.indices_computes)).comp
    (mapWith_computes entry_computes)
lemma row_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (x : Label (Fin m)) :
    row (pairBits (pairBits (Rectangular.encode distance,List.replicate d true),BinaryLabel.encode x))=
      RationalMatrix.rowEncode (rows distance x) := by
  simp only [row,extractPrefix_pairBits,discardPrefix_pairBits,BinaryEllipsoidInitial.indices_replicate,
    mapWith_ofFn,entry_pack,RationalMatrix.rowEncode_eq]

noncomputable def run : List Bool → List Bool := mapWith row
noncomputable def run_computes : PolyComputes run := mapWith_computes row_computes
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (xs : List (Label (Fin m))) :
    run (pairBits (pairBits (Rectangular.encode distance,List.replicate d true),encode (xs.map BinaryLabel.encode)))=
      Rectangular.encode (fun i : Fin xs.length=>rows distance (xs.get i)) := by
  rw [run,mapWith_encode,List.map_map]
  change encode (xs.map (fun x=>row (pairBits (pairBits (Rectangular.encode distance,List.replicate d true),BinaryLabel.encode x))))=_
  simp only [row_pack]
  unfold Rectangular.encode
  congr 1
  exact (List.ofFn_getElem_eq_map xs (RationalMatrix.rowEncode ∘ rows distance)).symm
end MetricKMedianRecovery.BitMachine.BinaryLabelMatrix

end OAI
