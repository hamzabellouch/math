import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RealVector
import OAI.Combinatorics.KMedianRecovery.Encoding.DivNatWords
import OAI.Combinatorics.KMedianRecovery.Encoding.Encode2
import OAI.Combinatorics.KMedianRecovery.Recovery.Next

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryEllipsoidRoot

def numAbs (x : List Bool) : List Bool := (extractPrefix (extractPrefix x)).tail
def den (x : List Bool) : List Bool := discardPrefix (extractPrefix x)
def precision (x : List Bool) : List Bool := discardPrefix x
noncomputable def numAbs_computes : PolyComputes numAbs :=
  (extractPrefix_computes.comp extractPrefix_computes).comp tail_computes
noncomputable def den_computes : PolyComputes den := extractPrefix_computes.comp discardPrefix_computes
noncomputable def precision_computes : PolyComputes precision := discardPrefix_computes

def radicand (x : List Bool) : List Bool :=
  (value (numAbs x)*value (den x)*(value (precision x)*value (precision x))).bits
noncomputable def radicand_computes : PolyComputes radicand := by
  have hh := NatOps.mul (NatOps.mul numAbs_computes den_computes)
    (NatOps.mul precision_computes precision_computes)
  change PolyComputes (fun x => (value (numAbs x)*value (den x)*(value (precision x)*value (precision x))).bits)
  simpa only [value_bits] using hh
noncomputable def upper (x : List Bool) : List Bool := (value (BinarySqrt.run (radicand x))+1).bits
noncomputable def upper_computes : PolyComputes upper := by
  have hh := NatOps.add (radicand_computes.comp BinarySqrt.run_computes) (const_computes (Nat.bits 1))
  change PolyComputes (fun x => (value (BinarySqrt.run (radicand x))+1).bits)
  simpa only [value_bits,Function.comp_apply] using hh

def denom (x : List Bool) : List Bool := (value (den x)*value (precision x)).bits
noncomputable def denom_computes : PolyComputes denom := NatOps.mul den_computes precision_computes
noncomputable def rawWords (x : List Bool) : List Bool :=
  pairBits (Signed.encode (value (upper x):ℤ),denom x)
noncomputable def rawWords_computes : PolyComputes rawWords :=
  (Signed.cast_computes upper_computes).pair denom_computes
noncomputable def run : List Bool → List Bool := BinaryRational.reduce ∘ rawWords
noncomputable def run_computes : PolyComputes run := rawWords_computes.comp BinaryRational.reduce_computes
lemma run_encode (q : ℚ) (D : ℕ) : run (pairBits (BinaryRational.encode q,D.bits))=
    BinaryRational.encode (Ellipsoid.rationalRootUpper D q) := by
  simp only [run,Function.comp_apply,rawWords,upper,denom,radicand,numAbs,den,precision,
    BinaryRational.encode,extractPrefix_pairBits,discardPrefix_pairBits,Signed.encode,
    List.tail_cons,value_bits,BinarySqrt.run_bits]
  rw [BinaryRational.reduce_correct]
  change BinaryRational.encode (BinaryRational.decode (pairBits
    (Signed.encode (((Nat.sqrt (q.num.natAbs*q.den*(D*D))+1):ℕ):ℤ),
      (q.den*D).bits)))=BinaryRational.encode _
  rw [BinaryRational.decode_pair,Rat.mkRat_eq_div]
  congr 1
  simp only [Ellipsoid.rationalRootUpper,Ellipsoid.sqrtUpperFraction,pow_two,Int.cast_natCast]

noncomputable def rationalRootUpper : Turing.TM2ComputableInPolyTime
    (fun p : ℚ×ℕ => pairBits (BinaryRational.encode p.1,p.2.bits)) BinaryRational.encode
    (fun p => Ellipsoid.rationalRootUpper p.2 p.1) :=
  run_computes.reencode _ _ (fun p => run_encode p.1 p.2)
end BinaryEllipsoidRoot
open WordOperations BinaryArithmetic
open scoped Matrix
namespace WordList
noncomputable def pointwise (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  mapWith (f ∘ discardPrefix) (pairBits ([],Zip.run x))
noncomputable def pointwise_computes {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (pointwise f) := by
  unfold pointwise
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f := fun input => pairBits ([], Zip.run input))
      (g := mapWith (f ∘ discardPrefix))
      (PolyComputes.comp (f := Zip.run) (g := fun input => pairBits ([], input))
        Zip.run_computes IntegerArray.prefixEmpty_computes)
      (mapWith_computes (f := f ∘ discardPrefix)
        (PolyComputes.comp (f := discardPrefix) (g := f) discardPrefix_computes hf)))
lemma zip_ofFn {n : ℕ} {α β : Type*} (u : Fin n → α) (v : Fin n → β) :
    (List.ofFn u).zip (List.ofFn v)=List.ofFn (fun i=>(u i,v i)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_zip,List.getElem_ofFn]
lemma pointwise_ofFn {n : ℕ} (f : List Bool → List Bool) (u v : Fin n → List Bool) :
    pointwise f (pairBits (encode (List.ofFn u),encode (List.ofFn v)))=
      encode (List.ofFn (fun i=>f (pairBits (u i,v i)))) := by
  simp only [pointwise,Zip.run_encode,zip_ofFn,List.map_ofFn,mapWith_ofFn,
    Function.comp_apply,discardPrefix_pairBits]
end WordList
namespace BinaryRational

def subInput (x : List Bool) : List Bool := pairBits (extractPrefix x,negWords (discardPrefix x))
noncomputable def subInput_computes : PolyComputes subInput :=
  extractPrefix_computes.pair (discardPrefix_computes.comp negWords_computes)
def subWords : List Bool → List Bool := addWords ∘ subInput
noncomputable def subWords_computes : PolyComputes subWords := subInput_computes.comp addWords_computes
lemma subWords_pair (a b : ℚ) : subWords (pairBits (encode a,encode b))=encode (a-b) := by
  simp only [subWords,Function.comp_apply,subInput,extractPrefix_pairBits,discardPrefix_pairBits,
    negWords_encode,addWords_pair,sub_eq_add_neg]
def secondInverse : List Bool → List Bool := invWords ∘ discardPrefix
noncomputable def secondInverse_computes : PolyComputes secondInverse :=
  PolyComputes.comp (f:=discardPrefix) (g:=invWords) discardPrefix_computes invWords_computes
def divInput (x : List Bool) : List Bool := pairBits (extractPrefix x,secondInverse x)
noncomputable def divInput_computes : PolyComputes divInput :=
  extractPrefix_computes.pair secondInverse_computes
def divWords : List Bool → List Bool := mulWords ∘ divInput
noncomputable def divWords_computes : PolyComputes divWords := divInput_computes.comp mulWords_computes
lemma divWords_pair (a b : ℚ) : divWords (pairBits (encode a,encode b))=encode (a/b) := by
  simp only [divWords,Function.comp_apply,divInput,secondInverse,extractPrefix_pairBits,discardPrefix_pairBits,
    invWords_encode,mulWords_pair,div_eq_mul_inv]
def natWords (x : List Bool) : List Bool := castIntWords (Signed.encode (value x:ℤ))
noncomputable def natWords_computes : PolyComputes natWords :=
  (Signed.cast_computes id_computes).comp castIntWords_computes
lemma natWords_bits (n : ℕ) : natWords n.bits=encode (n:ℚ) := by
  simp only [natWords,value_bits,castIntWords_encode,Int.cast_natCast]
end BinaryRational
namespace RationalMatrix
open WordList
noncomputable def vectorAdd : List Bool → List Bool := pointwise BinaryRational.addWords
noncomputable def vectorAdd_computes : PolyComputes vectorAdd := pointwise_computes BinaryRational.addWords_computes
lemma vectorAdd_encode {n : ℕ} (u v : Fin n → ℚ) :
    vectorAdd (pairBits (rowEncode u,rowEncode v))=rowEncode (u+v) := by
  simp only [vectorAdd,rowEncode_eq,pointwise_ofFn,BinaryRational.addWords_pair,Pi.add_apply]
noncomputable def vectorSub : List Bool → List Bool := pointwise BinaryRational.subWords
noncomputable def vectorSub_computes : PolyComputes vectorSub := pointwise_computes BinaryRational.subWords_computes
lemma vectorSub_encode {n : ℕ} (u v : Fin n → ℚ) :
    vectorSub (pairBits (rowEncode u,rowEncode v))=rowEncode (u-v) := by
  simp only [vectorSub,rowEncode_eq,pointwise_ofFn,BinaryRational.subWords_pair,Pi.sub_apply]
noncomputable def vectorScale : List Bool → List Bool := mapWith BinaryRational.mulWords
noncomputable def vectorScale_computes : PolyComputes vectorScale := mapWith_computes BinaryRational.mulWords_computes
lemma vectorScale_encode {n : ℕ} (r : ℚ) (u : Fin n → ℚ) :
    vectorScale (pairBits (BinaryRational.encode r,rowEncode u))=rowEncode (r • u) := by
  simp only [vectorScale,rowEncode_eq,mapWith_ofFn,BinaryRational.mulWords_pair,Pi.smul_apply,smul_eq_mul]
noncomputable def matrixAdd : List Bool → List Bool := pointwise vectorAdd
noncomputable def matrixAdd_computes : PolyComputes matrixAdd := pointwise_computes vectorAdd_computes
lemma matrixAdd_encode {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    matrixAdd (pairBits (encode A,encode B))=encode (A+B) := by
  simp only [matrixAdd,encode,pointwise_ofFn,vectorAdd_encode]
  congr 1
noncomputable def matrixSub : List Bool → List Bool := pointwise vectorSub
noncomputable def matrixSub_computes : PolyComputes matrixSub := pointwise_computes vectorSub_computes
lemma matrixSub_encode {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    matrixSub (pairBits (encode A,encode B))=encode (A-B) := by
  simp only [matrixSub,encode,pointwise_ofFn,vectorSub_encode]
  congr 1
noncomputable def matrixScale : List Bool → List Bool := mapWith vectorScale
noncomputable def matrixScale_computes : PolyComputes matrixScale := mapWith_computes vectorScale_computes
lemma matrixScale_encode {n : ℕ} (r : ℚ) (A : Matrix (Fin n) (Fin n) ℚ) :
    matrixScale (pairBits (BinaryRational.encode r,encode A))=encode (r • A) := by
  simp only [matrixScale,encode,mapWith_ofFn,vectorScale_encode]
  congr 1
noncomputable def outerRow : List Bool → List Bool := vectorScale ∘ swapWords
noncomputable def outerRow_computes : PolyComputes outerRow := swapWords_computes.comp vectorScale_computes
noncomputable def outer : List Bool → List Bool := (mapWith outerRow) ∘ swapWords
noncomputable def outer_computes : PolyComputes outer := swapWords_computes.comp (mapWith_computes outerRow_computes)
lemma outer_encode {n : ℕ} (u v : Fin n → ℚ) :
    outer (pairBits (rowEncode u,rowEncode v))=encode (Matrix.vecMulVec u v) := by
  simp only [outer,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [rowEncode_eq u,mapWith_ofFn]
  simp only [outerRow,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits,
    vectorScale_encode,encode]
  rfl
noncomputable def dotRow : List Bool → List Bool := RationalArray.dotListsWords ∘ swapWords
noncomputable def dotRow_computes : PolyComputes dotRow := swapWords_computes.comp RationalArray.dotListsWords_computes
noncomputable def mulVec : List Bool → List Bool := (mapWith dotRow) ∘ swapWords
noncomputable def mulVec_computes : PolyComputes mulVec := swapWords_computes.comp (mapWith_computes dotRow_computes)
lemma mulVec_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) :
    mulVec (pairBits (encode A,rowEncode v))=rowEncode (A *ᵥ v) := by
  simp only [mulVec,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits,
    encode,mapWith_ofFn,dotRow,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits,
    dotListsWords_ofFn]
  simp only [rowEncode_eq]
  rfl
noncomputable def quadInput (x : List Bool) : List Bool := pairBits (discardPrefix x,mulVec x)
noncomputable def quadInput_computes : PolyComputes quadInput := discardPrefix_computes.pair mulVec_computes
noncomputable def quad : List Bool → List Bool := RationalArray.dotListsWords ∘ quadInput
noncomputable def quad_computes : PolyComputes quad := quadInput_computes.comp RationalArray.dotListsWords_computes
lemma quad_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) :
    quad (pairBits (encode A,rowEncode v))=BinaryRational.encode (v ⬝ᵥ (A *ᵥ v)) := by
  simp only [quad,Function.comp_apply,quadInput,discardPrefix_pairBits,mulVec_encode,dotListsWords_ofFn]
  rfl
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
