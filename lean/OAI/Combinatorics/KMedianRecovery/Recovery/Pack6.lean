import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.GetRow2
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack5

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidGrid
open RationalMatrix WordList

def pack {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : List Bool :=
  pairBits (n.bits,pairBits (D.bits,RationalMatrix.encode A))
def dim : List Bool → List Bool := extractPrefix
def rest : List Bool → List Bool := discardPrefix
def precision : List Bool → List Bool := extractPrefix ∘ rest
def shape : List Bool → List Bool := discardPrefix ∘ rest
noncomputable def dim_computes : PolyComputes dim := extractPrefix_computes
noncomputable def precision_computes : PolyComputes precision := discardPrefix_computes.comp extractPrefix_computes
noncomputable def shape_computes : PolyComputes shape := discardPrefix_computes.comp discardPrefix_computes
lemma dim_pack {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : dim (pack D A)=n.bits := by
  simp only [dim,pack,extractPrefix_pairBits]
lemma precision_pack {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : precision (pack D A)=D.bits := by
  simp only [precision,Function.comp_apply,rest,pack,extractPrefix_pairBits,discardPrefix_pairBits]
lemma shape_pack {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : shape (pack D A)=RationalMatrix.encode A := by
  simp only [shape,Function.comp_apply,rest,pack,discardPrefix_pairBits]

def ctx : List Bool → List Bool := extractPrefix ∘ extractPrefix
def row : List Bool → List Bool := discardPrefix ∘ extractPrefix
def col : List Bool → List Bool := discardPrefix
noncomputable def ctx_computes : PolyComputes ctx := extractPrefix_computes.comp extractPrefix_computes
noncomputable def row_computes : PolyComputes row := extractPrefix_computes.comp discardPrefix_computes
noncomputable def col_computes : PolyComputes col := discardPrefix_computes

def entryInput (x : List Bool) : List Bool := pairBits (pairBits (shape (ctx x),row x),col x)
noncomputable def entryInput_computes : PolyComputes entryInput :=
  ((ctx_computes.comp shape_computes).pair row_computes).pair col_computes
def entry : List Bool → List Bool := getEntry ∘ entryInput
noncomputable def entry_computes : PolyComputes entry := entryInput_computes.comp getEntry_computes
lemma entry_pack {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    entry (pairBits (pairBits (pack D A,i.val.bits),j.val.bits))=BinaryRational.encode (A i j) := by
  simp only [entry,Function.comp_apply,entryInput,ctx,row,col,extractPrefix_pairBits,
    discardPrefix_pairBits,shape_pack,getEntry_encode]

def dimension (x : List Bool) : ℚ := value (dim (ctx x))
def scale (x : List Bool) : ℚ := value (precision (ctx x))
noncomputable def dimension_computes : PolyComputes (fun x=>BinaryRational.encode (dimension x)) :=
  RatOps.nat (ctx_computes.comp dim_computes)
noncomputable def scale_computes : PolyComputes (fun x=>BinaryRational.encode (scale x)) :=
  RatOps.nat (ctx_computes.comp precision_computes)
noncomputable def qvalue (x : List Bool) : ℚ := BinaryRational.decode (entry x)
noncomputable def qvalue_computes : PolyComputes (fun x=>BinaryRational.encode (qvalue x)) := RatOps.ofWords entry_computes
noncomputable def floorValue (x : List Bool) : ℚ := (⌊scale x*qvalue x⌋:ℤ)/scale x
noncomputable def floorValue_computes : PolyComputes (fun x=>BinaryRational.encode (floorValue x)) :=
  RatOps.div (RatOps.floor (RatOps.mul scale_computes qvalue_computes)) scale_computes
def diagonal (x : List Bool) : ℚ := dimension x/scale x
noncomputable def diagonal_computes : PolyComputes (fun x=>BinaryRational.encode (diagonal x)) :=
  RatOps.div dimension_computes scale_computes
noncomputable def entryWords (x : List Bool) : List Bool :=
  if value (row x)≤value (col x) then
    if value (col x)≤value (row x) then BinaryRational.encode (floorValue x+diagonal x)
    else BinaryRational.encode (floorValue x)
  else BinaryRational.encode (floorValue x)
noncomputable def entryWords_computes : PolyComputes entryWords := by
  have hh := (NatOps.le row_computes col_computes).cond
    ((NatOps.le col_computes row_computes).cond (RatOps.add floorValue_computes diagonal_computes)
      floorValue_computes) floorValue_computes
  unfold entryWords
  simpa only [decide_eq_true_eq] using hh
lemma entryWords_pack {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    entryWords (pairBits (pairBits (pack D A,i.val.bits),j.val.bits))=
      BinaryRational.encode (Ellipsoid.gridShape D A i j) := by
  simp only [entryWords,floorValue,qvalue,entry_pack,BinaryRational.decode_encode,diagonal,
    dimension,scale,ctx,row,col,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    dim_pack,precision_pack,value_bits,Ellipsoid.gridShape,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,Ellipsoid.gridMatrix,Ellipsoid.gridFloor,Fintype.card_fin]
  by_cases h : i=j
  · subst j
    simp only [le_refl,ite_true,Matrix.one_apply_eq,mul_one]
  · have hv : i.val≠j.val := fun hh=>h (Fin.ext hh)
    simp only [Matrix.one_apply_ne h,mul_zero,add_zero]
    split_ifs with hj hi
    · omega
    · rfl
    · rfl

noncomputable def rowInput (x : List Bool) : List Bool := pairBits (x,Indices.run (shape (extractPrefix x)))
noncomputable def rowInput_computes : PolyComputes rowInput :=
  id_computes.pair ((extractPrefix_computes.comp shape_computes).comp Indices.run_computes)
noncomputable def rowWords : List Bool → List Bool := (mapWith entryWords) ∘ rowInput
noncomputable def rowWords_computes : PolyComputes rowWords := rowInput_computes.comp (mapWith_computes entryWords_computes)
lemma rowWords_pack {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    rowWords (pairBits (pack D A,i.val.bits))=rowEncode (Ellipsoid.gridShape D A i) := by
  have hi := indices_ofFn (fun i=>rowEncode (A i))
  change Indices.run (RationalMatrix.encode A)=_ at hi
  simp only [rowWords,Function.comp_apply,rowInput,extractPrefix_pairBits,shape_pack,hi,
    mapWith_ofFn,entryWords_pack,rowEncode_eq]

noncomputable def runInput (x : List Bool) : List Bool := pairBits (x,Indices.run (shape x))
noncomputable def runInput_computes : PolyComputes runInput :=
  id_computes.pair (shape_computes.comp Indices.run_computes)
noncomputable def run : List Bool → List Bool := (mapWith rowWords) ∘ runInput
noncomputable def run_computes : PolyComputes run := runInput_computes.comp (mapWith_computes rowWords_computes)
lemma run_pack {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    run (pack D A)=RationalMatrix.encode (Ellipsoid.gridShape D A) := by
  have hi := indices_ofFn (fun i=>rowEncode (A i))
  change Indices.run (RationalMatrix.encode A)=_ at hi
  simp only [run,Function.comp_apply,runInput,shape_pack,hi,mapWith_ofFn,rowWords_pack]
  rfl
end BinaryEllipsoidGrid
namespace BinaryEllipsoidCut
noncomputable def gridInput (x : List Bool) : List Bool := pairBits (dim x,pairBits (precision x,inflateWords x))
noncomputable def gridInput_computes : PolyComputes gridInput := dim_computes.pair (precision_computes.pair inflateWords_computes)
noncomputable def shapeWords : List Bool → List Bool := BinaryEllipsoidGrid.run ∘ gridInput
noncomputable def shapeWords_computes : PolyComputes shapeWords := gridInput_computes.comp BinaryEllipsoidGrid.run_computes
lemma shapeWords_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    shapeWords (pack H a c D)=RationalMatrix.encode (Ellipsoid.rationalStepShape D H a) := by
  simp only [shapeWords,Function.comp_apply,gridInput,dim_pack,precision_pack,inflateWords_pack]
  exact BinaryEllipsoidGrid.run_pack D (Ellipsoid.rationalInflatedShape H a)
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
