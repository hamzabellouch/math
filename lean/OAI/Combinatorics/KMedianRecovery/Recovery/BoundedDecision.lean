import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DataHeight
import OAI.Combinatorics.KMedianRecovery.Recovery.BoundOp

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryBoundedDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList RationalMatrix

def pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : List Bool :=
  pairBits (List.replicate n true,pairBits (List.replicate m true,
    pairBits (B.bits,BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (A r) (b r))))))
def nword : List Bool → List Bool := extractPrefix
def rest₁ : List Bool → List Bool := discardPrefix
def mword : List Bool → List Bool := extractPrefix ∘ rest₁
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest₁
def bound : List Bool → List Bool := extractPrefix ∘ rest₂
def rows : List Bool → List Bool := discardPrefix ∘ rest₂
noncomputable def nword_computes : PolyComputes nword := extractPrefix_computes
noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def mword_computes : PolyComputes mword := rest₁_computes.comp extractPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def bound_computes : PolyComputes bound := rest₂_computes.comp extractPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₂_computes.comp discardPrefix_computes
lemma projections_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    nword (pack A b B)=List.replicate n true ∧ mword (pack A b B)=List.replicate m true ∧
    bound (pack A b B)=B.bits ∧
    rows (pack A b B)=BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (A r) (b r))) := by
  simp only [pack,nword,mword,rest₁,rest₂,bound,rows,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,and_self]

def numAbs (x : List Bool) : List Bool := (extractPrefix x).tail
noncomputable def numAbs_computes : PolyComputes numAbs := extractPrefix_computes.comp WordOperations.tail_computes
lemma numAbs_encode (q : ℚ) : numAbs (BinaryRational.encode q)=q.num.natAbs.bits := by
  simp only [numAbs,BinaryRational.encode,extractPrefix_pairBits,Signed.encode,List.tail_cons]
def numAbsOp : List Bool → List Bool := numAbs ∘ discardPrefix
noncomputable def numAbsOp_computes : PolyComputes numAbsOp := discardPrefix_computes.comp numAbs_computes
noncomputable def coeffAbs (x : List Bool) : List Bool := mapWith numAbsOp (pairBits ([],extractPrefix x))
noncomputable def coeffAbs_computes : PolyComputes coeffAbs := by
  unfold coeffAbs
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],extractPrefix input)) (g:=mapWith numAbsOp)
      ((const_computes []).pair extractPrefix_computes) (mapWith_computes numAbsOp_computes))
lemma coeffAbs_row {n : ℕ} (a : Fin n → ℤ) (b : ℤ) :
    coeffAbs (BinaryRow.encode (integerRow a b))=NaturalArray.encode (List.ofFn (fun j=>(a j).natAbs)) := by
  simp [coeffAbs,BinaryRow.encode,integerRow,extractPrefix_pairBits,rowEncode_eq,mapWith_ofFn,
    numAbsOp,numAbs_encode,NaturalArray.encode,Function.comp_def]
noncomputable def coeffSum : List Bool → List Bool := NaturalArray.sumWords ∘ coeffAbs
noncomputable def coeffSum_computes : PolyComputes coeffSum := coeffAbs_computes.comp NaturalArray.sumWords_computes
lemma coeffSum_row {n : ℕ} (a : Fin n → ℤ) (b : ℤ) :
    coeffSum (BinaryRow.encode (integerRow a b))=(∑ j, (a j).natAbs).bits := by
  rw [coeffSum,Function.comp_apply,coeffAbs_row,NaturalArray.sumWords_encode,List.sum_ofFn]
noncomputable def rowHeight (x : List Bool) : List Bool :=
  (value (numAbs (discardPrefix x))+value (coeffSum x)).bits
noncomputable def rowHeight_computes : PolyComputes rowHeight :=
  NatOps.add (discardPrefix_computes.comp numAbs_computes) coeffSum_computes
lemma rowHeight_row {n : ℕ} (a : Fin n → ℤ) (b : ℤ) :
    rowHeight (BinaryRow.encode (integerRow a b))=(b.natAbs+∑ j, (a j).natAbs).bits := by
  unfold rowHeight
  rw [coeffSum_row]
  simp [BinaryRow.encode,integerRow,numAbs_encode,discardPrefix_pairBits,value_bits]
noncomputable def rowHeightOp : List Bool → List Bool := rowHeight ∘ discardPrefix
noncomputable def rowHeightOp_computes : PolyComputes rowHeightOp := discardPrefix_computes.comp rowHeight_computes
noncomputable def rowHeights (x : List Bool) : List Bool := mapWith rowHeightOp (pairBits ([],rows x))
noncomputable def rowHeights_computes : PolyComputes rowHeights := by
  unfold rowHeights
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],rows input)) (g:=mapWith rowHeightOp)
      ((const_computes []).pair rows_computes) (mapWith_computes rowHeightOp_computes))
lemma rowHeights_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    rowHeights (pack A b B)=NaturalArray.encode (List.ofFn (fun r=>(b r).natAbs+∑ j, (A r j).natAbs)) := by
  simp only [rowHeights,(projections_pack A b B).2.2.2,BinaryRow.rowsEncode,List.map_ofFn,
    Function.comp_def,mapWith_ofFn,rowHeightOp,discardPrefix_pairBits,rowHeight_row,NaturalArray.encode]
noncomputable def heightSum : List Bool → List Bool := NaturalArray.sumWords ∘ rowHeights
noncomputable def heightSum_computes : PolyComputes heightSum := rowHeights_computes.comp NaturalArray.sumWords_computes
noncomputable def height (x : List Bool) : List Bool := (value (bound x)+1+value (heightSum x)).bits
noncomputable def height_computes : PolyComputes height := by
  unfold height
  have hh := NatOps.add (NatOps.add bound_computes (const_computes (1:ℕ).bits)) heightSum_computes
  simpa only [value_bits] using hh
lemma height_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    height (pack A b B)=(dataHeight A b B).bits := by
  simp only [height,(projections_pack A b B).2.2.1,heightSum,Function.comp_apply,rowHeights_pack,
    NaturalArray.sumWords_encode,List.sum_ofFn,value_bits,dataHeight]
lemma dataHeight_pad {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    dataHeight (padMatrix A) b B=dataHeight A b B := by
  simp [dataHeight,padMatrix,Fin.sum_univ_add]

def padRow (x : List Bool) : List Bool :=
  pairBits (extractPrefix x++WordList.encode [BinaryRational.encode 0,BinaryRational.encode 0],discardPrefix x)
noncomputable def padRow_computes : PolyComputes padRow :=
  (extractPrefix_computes.append (const_computes (WordList.encode [BinaryRational.encode 0,BinaryRational.encode 0]))).pair
    discardPrefix_computes
lemma padRow_row {n : ℕ} (a : Fin n → ℤ) (b : ℤ) :
    padRow (BinaryRow.encode (integerRow a b))=BinaryRow.encode (integerRow (Fin.append a (fun _ : Fin 2=>0)) b) := by
  have he : (fun j : Fin (n+2) => ((Fin.append a (fun _ : Fin 2=>(0:ℤ)) j : ℤ):ℚ))=Fin.append (fun j=>(a j:ℚ)) (fun _ : Fin 2=>0) := by
    funext j
    refine Fin.addCases (fun i=>?_) (fun i=>?_) j <;> simp
  simp only [padRow,BinaryRow.encode,integerRow,extractPrefix_pairBits,discardPrefix_pairBits,he,rowEncode,
    List.ofFn_fin_append,RationalArray.encode,List.map_append,encode_append]
  rfl
noncomputable def padRowOp : List Bool → List Bool := padRow ∘ discardPrefix
noncomputable def padRowOp_computes : PolyComputes padRowOp := discardPrefix_computes.comp padRow_computes
noncomputable def paddedRows (x : List Bool) : List Bool := mapWith padRowOp (pairBits ([],rows x))
noncomputable def paddedRows_computes : PolyComputes paddedRows := by
  unfold paddedRows
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],rows input)) (g:=mapWith padRowOp)
      ((const_computes []).pair rows_computes) (mapWith_computes padRowOp_computes))
lemma paddedRows_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    paddedRows (pack A b B)=BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (padMatrix A r) (b r))) := by
  simp only [paddedRows,(projections_pack A b B).2.2.2,BinaryRow.rowsEncode,List.map_ofFn,
    Function.comp_def,mapWith_ofFn,padRowOp,discardPrefix_pairBits,padRow_row,padMatrix]
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (nword x++[true,true],pairBits (mword x,pairBits (bound x,pairBits (height x,paddedRows x))))
noncomputable def prepared_computes : PolyComputes prepared :=
  (nword_computes.append (const_computes [true,true])).pair
    (mword_computes.pair (bound_computes.pair (height_computes.pair paddedRows_computes)))
lemma prepared_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    prepared (pack A b B)=BinaryDecision.pack (padMatrix A) b B (dataHeight (padMatrix A) b B) := by
  simp only [prepared,(projections_pack A b B).1,(projections_pack A b B).2.1,
    (projections_pack A b B).2.2.1,height_pack,paddedRows_pack,dataHeight_pad,BinaryDecision.pack]
  congr 2
  simpa using (List.replicate_add n 2 true).symm
noncomputable def run : List Bool → List Bool := BinaryDecision.run ∘ prepared
noncomputable def run_computes : PolyComputes run := prepared_computes.comp BinaryDecision.run_computes
lemma run_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    run (pack A b B)=[boundedIntegerDecide A b B] := by
  rw [run,Function.comp_apply,prepared_pack,BinaryDecision.run_pack _ _ _ _ (by omega)]
  rfl
lemma run_correct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    run (pack A b B)=[true] ↔
      ∃ x : Fin n → ℝ, (∀ r, (∑ j, (A r j:ℝ)*x j)≤(b r:ℝ)) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  rw [run_pack]
  simpa only [List.cons.injEq,and_true] using boundedIntegerDecide_correct A b B
end BinaryBoundedDecision
namespace BinaryClearRow
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid PolytopeCertificate
open WordList RationalMatrix

def entries (x : List Bool) : List Bool := cons (discardPrefix x) (extractPrefix x)
noncomputable def entries_computes : PolyComputes entries := cons_computes discardPrefix_computes extractPrefix_computes
lemma entries_row {n : ℕ} (r : Row n) :
    entries (BinaryRow.encode r)=RationalArray.encode (r.bound::List.ofFn r.coeff) := by
  simp only [entries,BinaryRow.encode,extractPrefix_pairBits,discardPrefix_pairBits,RationalArray.encode,
    List.map_cons,WordList.encode,rowEncode]
def denOp : List Bool → List Bool := BinaryRational.denominator ∘ discardPrefix
noncomputable def denOp_computes : PolyComputes denOp := discardPrefix_computes.comp BinaryRational.denominator_computes
noncomputable def denominators (x : List Bool) : List Bool := mapWith denOp (pairBits ([],entries x))
noncomputable def denominators_computes : PolyComputes denominators := by
  unfold denominators
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],entries input)) (g:=mapWith denOp)
      ((const_computes []).pair entries_computes) (mapWith_computes denOp_computes))
lemma denominators_row {n : ℕ} (r : Row n) : denominators (BinaryRow.encode r)=
    NaturalArray.encode ((r.bound::List.ofFn r.coeff).map Rat.den) := by
  simp only [denominators,entries_row,RationalArray.encode,mapWith_encode,List.map_map,Function.comp_def,
    denOp,discardPrefix_pairBits,BinaryRational.denominator_encode,NaturalArray.encode]
noncomputable def denominator : List Bool → List Bool := NaturalArray.productWords ∘ denominators
noncomputable def denominator_computes : PolyComputes denominator := denominators_computes.comp NaturalArray.productWords_computes

def rowD {n : ℕ} (r : Row n) : ℕ := r.bound.den*∏ i, (r.coeff i).den
lemma denominator_row {n : ℕ} (r : Row n) : denominator (BinaryRow.encode r)=(rowD r).bits := by
  simp only [denominator,Function.comp_apply,denominators_row,NaturalArray.productWords_encode,
    List.map_cons,List.prod_cons,List.map_ofFn,List.prod_ofFn,rowD,Function.comp_def]
lemma rowD_cast {n : ℕ} (r : Row n) : (rowD r:ℚ)=(rowDenominator (rowEntries r):ℚ) := by
  simp [rowD,rowDenominator,Fintype.prod_option,rowEntries]
lemma rowNumerator_rat {J : Type*} [Fintype J] [DecidableEq J] (q : J → ℚ) (i : J) :
    (rowNumerator q i:ℚ)=(rowDenominator q:ℚ)*q i := by
  apply Rat.cast_injective (α:=ℝ)
  push_cast
  exact rowNumerator_cast q i
lemma scale_coeff {n : ℕ} (r : Row n) (i : Fin n) :
    (rowD r:ℚ)*r.coeff i=(rowNumerator (rowEntries r) (some i):ℚ) := by
  rw [rowD_cast,rowNumerator_rat]
  rfl
lemma scale_bound {n : ℕ} (r : Row n) :
    (rowD r:ℚ)*r.bound=(rowNumerator (rowEntries r) none:ℚ) := by
  rw [rowD_cast,rowNumerator_rat]
  rfl
noncomputable def scalar (x : List Bool) : List Bool := BinaryRational.encode (value (denominator x):ℚ)
noncomputable def scalar_computes : PolyComputes scalar := RatOps.nat denominator_computes
noncomputable def coeffWords (x : List Bool) : List Bool := mapWith BinaryRational.mulWords (pairBits (scalar x,extractPrefix x))
noncomputable def coeffWords_computes : PolyComputes coeffWords := by
  unfold coeffWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits (scalar input,extractPrefix input))
      (g:=mapWith BinaryRational.mulWords)
      (scalar_computes.pair extractPrefix_computes) (mapWith_computes BinaryRational.mulWords_computes))
lemma coeffWords_row {n : ℕ} (r : Row n) : coeffWords (BinaryRow.encode r)=
    rowEncode (fun i=>(rowNumerator (rowEntries r) (some i):ℚ)) := by
  rw [coeffWords,scalar,denominator_row]
  simp only [value_bits,BinaryRow.encode,extractPrefix_pairBits,
    rowEncode_eq,mapWith_ofFn,BinaryRational.mulWords_pair,scale_coeff]
noncomputable def boundWords (x : List Bool) : List Bool := BinaryRational.encode
  ((value (denominator x):ℚ)*BinaryRational.decode (discardPrefix x))
noncomputable def boundWords_computes : PolyComputes boundWords :=
  RatOps.mul (RatOps.nat denominator_computes) (RatOps.ofWords discardPrefix_computes)
lemma boundWords_row {n : ℕ} (r : Row n) : boundWords (BinaryRow.encode r)=
    BinaryRational.encode (rowNumerator (rowEntries r) none:ℚ) := by
  rw [boundWords,denominator_row]
  simp only [value_bits,BinaryRow.encode,discardPrefix_pairBits,
    BinaryRational.decode_encode,scale_bound]
noncomputable def run (x : List Bool) : List Bool := pairBits (coeffWords x,boundWords x)
noncomputable def run_computes : PolyComputes run := coeffWords_computes.pair boundWords_computes
lemma run_row {n : ℕ} (r : Row n) : run (BinaryRow.encode r)=BinaryRow.encode
    (integerRow (fun i=>rowNumerator (rowEntries r) (some i)) (rowNumerator (rowEntries r) none)) := by
  rw [run,coeffWords_row,boundWords_row]
  rfl
end BinaryClearRow
namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

def pack {n : ℕ} (rs : List (Row n)) (B : ℕ) : List Bool :=
  pairBits (List.replicate n true,pairBits (List.replicate rs.length true,
    pairBits (B.bits,BinaryRow.rowsEncode rs)))
def first : List Bool → List Bool := extractPrefix
def rest₁ : List Bool → List Bool := discardPrefix
def second : List Bool → List Bool := extractPrefix ∘ rest₁
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest₁
def bound : List Bool → List Bool := extractPrefix ∘ rest₂
def rows : List Bool → List Bool := discardPrefix ∘ rest₂
noncomputable def first_computes : PolyComputes first := extractPrefix_computes
noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def second_computes : PolyComputes second := rest₁_computes.comp extractPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def bound_computes : PolyComputes bound := rest₂_computes.comp extractPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₂_computes.comp discardPrefix_computes
lemma projections_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    first (pack rs B)=List.replicate n true ∧ second (pack rs B)=List.replicate rs.length true ∧
    bound (pack rs B)=B.bits ∧ rows (pack rs B)=BinaryRow.rowsEncode rs := by
  simp only [pack,first,second,rest₁,rest₂,bound,rows,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,and_self]
noncomputable def clearOp : List Bool → List Bool := BinaryClearRow.run ∘ discardPrefix
noncomputable def clearOp_computes : PolyComputes clearOp := discardPrefix_computes.comp BinaryClearRow.run_computes
noncomputable def clearedRows (x : List Bool) : List Bool := mapWith clearOp (pairBits ([],rows x))
noncomputable def clearedRows_computes : PolyComputes clearedRows := by
  unfold clearedRows
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],rows input)) (g:=mapWith clearOp)
      ((const_computes []).pair rows_computes) (mapWith_computes clearOp_computes))
lemma clearedRows_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    clearedRows (pack rs B)=BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (clearedMatrix rs r) (clearedBounds rs r))) := by
  simp only [clearedRows,(projections_pack rs B).2.2.2,BinaryRow.rowsEncode,mapWith_encode,List.map_map,
    Function.comp_def,clearOp,discardPrefix_pairBits,BinaryClearRow.run_row,clearedBounds]
  congr 1
  rw [List.map_ofFn,Function.comp_def]
  exact (List.ofFn_getElem_eq_map rs _).symm
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (first x,pairBits (second x,pairBits (bound x,clearedRows x)))
noncomputable def prepared_computes : PolyComputes prepared :=
  first_computes.pair (second_computes.pair (bound_computes.pair clearedRows_computes))
lemma prepared_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    prepared (pack rs B)=BinaryBoundedDecision.pack (clearedMatrix rs) (clearedBounds rs) B := by
  simp only [prepared,(projections_pack rs B).1,(projections_pack rs B).2.1,
    (projections_pack rs B).2.2.1,clearedRows_pack,BinaryBoundedDecision.pack]
noncomputable def run : List Bool → List Bool := BinaryBoundedDecision.run ∘ prepared
noncomputable def run_computes : PolyComputes run := prepared_computes.comp BinaryBoundedDecision.run_computes
lemma run_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) : run (pack rs B)=[boundedRationalDecide rs B] := by
  rw [run,Function.comp_apply,prepared_pack,BinaryBoundedDecision.run_pack]
  rfl
lemma run_correct {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    run (pack rs B)=[true] ↔
      ∃ x : Fin n → ℝ, (∀ r∈rs, r.RealHolds x) ∧ (∀ j, |x j|≤(B:ℝ)) := by
  rw [run_pack]
  simpa only [List.cons.injEq,and_true] using boundedRationalDecide_correct rs B

structure System where
  dimension : ℕ
  constraints : List (Row dimension)
  boxBound : ℕ

def System.bits (p : System) : List Bool := pack p.constraints p.boxBound
def System.answer (p : System) : Bool := boundedRationalDecide p.constraints p.boxBound
noncomputable def computation : Turing.TM2ComputableInPolyTime System.bits (fun b:Bool=>[b]) System.answer :=
  run_computes.reencode _ _ (fun p=>run_pack p.constraints p.boxBound)
end BinaryRationalDecision

open WordOperations
namespace WordList
namespace Count
noncomputable def op : List Bool → List Bool := List.cons true ∘ Fold.accum
noncomputable def op_computes : PolyComputes op := Fold.accum_computes.comp (prefix_computes true)
lemma operation_eq (ctx a w : List Bool) : Fold.operation op ctx a w=true::a := by
  simp only [Fold.operation,op,Function.comp_apply,Fold.accum,discardPrefix_pairBits]
lemma fold_op (ws : List (List Bool)) (a : List Bool) (ctx : List Bool) :
    ws.foldl (Fold.operation op ctx) a=List.replicate ws.length true++a := by
  induction ws generalizing a with
  | nil => simp only [List.foldl_nil,List.length_nil,List.replicate_zero,List.nil_append]
  | cons w ws ih =>
    simp only [List.foldl_cons,operation_eq,ih,List.length_cons]
    rw [←List.singleton_append,←List.append_assoc,←List.replicate_succ',List.replicate_succ]
noncomputable def run (x : List Bool) : List Bool := Fold.run op (4*Polynomial.X+4) (Fold.pack x [] [])
noncomputable def run_computes : PolyComputes run :=
  (Fold.pack_computes id_computes (const_computes []) (const_computes [])).comp
    (Fold.run_computes op_computes (4*Polynomial.X+4))
lemma run_encode (ws : List (List Bool)) : run (encode ws)=List.replicate ws.length true := by
  unfold run
  rw [Fold.run_encode op (4*Polynomial.X+4) [] [] ws (encode ws).length]
  · simp only [fold_op,List.append_nil]
  · intro n
    simp only [fold_op,List.append_nil,List.length_replicate]
    have ht : (ws.take n).length ≤ ws.length := by simp only [List.length_take]; omega
    exact ht.trans (length_le_encode ws)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
end Count
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
