import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalInflatedShape
import OAI.Combinatorics.KMedianRecovery.Encoding.Words

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidCut
open RationalMatrix

def pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) : List Bool :=
  pairBits (n.bits,pairBits (encode H,pairBits (rowEncode a,pairBits (rowEncode c,D.bits))))
def dim : List Bool → List Bool := extractPrefix
def rest : List Bool → List Bool := discardPrefix
def shape : List Bool → List Bool := extractPrefix ∘ rest
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest
def direction : List Bool → List Bool := extractPrefix ∘ rest₂
def rest₃ : List Bool → List Bool := discardPrefix ∘ rest₂
def center : List Bool → List Bool := extractPrefix ∘ rest₃
def precision : List Bool → List Bool := discardPrefix ∘ rest₃
noncomputable def dim_computes : PolyComputes dim := extractPrefix_computes
noncomputable def rest_computes : PolyComputes rest := discardPrefix_computes
noncomputable def shape_computes : PolyComputes shape := rest_computes.comp extractPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest_computes.comp discardPrefix_computes
noncomputable def direction_computes : PolyComputes direction := rest₂_computes.comp extractPrefix_computes
noncomputable def rest₃_computes : PolyComputes rest₃ := rest₂_computes.comp discardPrefix_computes
noncomputable def center_computes : PolyComputes center := rest₃_computes.comp extractPrefix_computes
noncomputable def precision_computes : PolyComputes precision := rest₃_computes.comp discardPrefix_computes
lemma dim_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    dim (pack H a c D)=n.bits := by simp only [dim,pack,extractPrefix_pairBits]
lemma shape_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    shape (pack H a c D)=encode H := by
  simp only [shape,Function.comp_apply,rest,pack,extractPrefix_pairBits,discardPrefix_pairBits]
lemma direction_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    direction (pack H a c D)=rowEncode a := by
  simp only [direction,rest₂,Function.comp_apply,rest,pack,extractPrefix_pairBits,discardPrefix_pairBits]
lemma center_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    center (pack H a c D)=rowEncode c := by
  simp only [center,rest₃,rest₂,Function.comp_apply,rest,pack,extractPrefix_pairBits,discardPrefix_pairBits]
lemma precision_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    precision (pack H a c D)=D.bits := by
  simp only [precision,rest₃,rest₂,Function.comp_apply,rest,pack,discardPrefix_pairBits]

def haInput (x : List Bool) : List Bool := pairBits (shape x,direction x)
noncomputable def haInput_computes : PolyComputes haInput := shape_computes.pair direction_computes
noncomputable def haWords : List Bool → List Bool := mulVec ∘ haInput
noncomputable def haWords_computes : PolyComputes haWords := haInput_computes.comp mulVec_computes
noncomputable def quadWords : List Bool → List Bool := quad ∘ haInput
noncomputable def quadWords_computes : PolyComputes quadWords := haInput_computes.comp quad_computes
lemma haWords_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    haWords (pack H a c D)=rowEncode (H *ᵥ a) := by
  simp only [haWords,Function.comp_apply,haInput,shape_pack,direction_pack,mulVec_encode]
lemma quadWords_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    quadWords (pack H a c D)=BinaryRational.encode (Ellipsoid.rationalQuad H a) := by
  simp only [quadWords,Function.comp_apply,haInput,shape_pack,direction_pack,quad_encode,Ellipsoid.rationalQuad]

def dimension (x : List Bool) : ℚ := value (dim x)
noncomputable def dimension_computes : PolyComputes (fun x=>BinaryRational.encode (dimension x)) := RatOps.nat dim_computes
noncomputable def qvalue (x : List Bool) : ℚ := BinaryRational.decode (quadWords x)
noncomputable def qvalue_computes : PolyComputes (fun x=>BinaryRational.encode (qvalue x)) := RatOps.ofWords quadWords_computes

def coefA (x : List Bool) : List Bool := BinaryRational.encode (dimension x^2/(dimension x^2-1))
noncomputable def coefA_computes : PolyComputes coefA := by
  have hn := RatOps.mul dimension_computes dimension_computes
  have hh := RatOps.div hn (RatOps.sub hn (RatOps.const 1))
  change PolyComputes (fun x=>BinaryRational.encode (dimension x^2/(dimension x^2-1)))
  simpa only [pow_two] using hh
noncomputable def coefB (x : List Bool) : List Bool := BinaryRational.encode (2/((dimension x+1)*qvalue x))
noncomputable def coefB_computes : PolyComputes coefB :=
  RatOps.div (RatOps.const 2) (RatOps.mul (RatOps.add dimension_computes (RatOps.const 1)) qvalue_computes)
def coefInflate (x : List Bool) : List Bool := BinaryRational.encode (1/(1-1/(8*dimension x^2)))
noncomputable def coefInflate_computes : PolyComputes coefInflate := by
  have hn := RatOps.mul dimension_computes dimension_computes
  have hh := RatOps.div (RatOps.const 1) (RatOps.sub (RatOps.const 1)
    (RatOps.div (RatOps.const 1) (RatOps.mul (RatOps.const 8) hn)))
  change PolyComputes (fun x=>BinaryRational.encode (1/(1-1/(8*dimension x^2))))
  simpa only [pow_two] using hh

def rootPrecision (x : List Bool) : ℕ := 32*value (dim x)
noncomputable def rootPrecision_computes : PolyComputes (fun x=>(rootPrecision x).bits) := by
  have hh := NatOps.mul (const_computes (Nat.bits 32)) dim_computes
  change PolyComputes (fun x=>(32*value (dim x)).bits)
  simpa only [value_bits] using hh
noncomputable def root_computes : PolyComputes
    (fun x=>BinaryRational.encode (Ellipsoid.rationalRootUpper (rootPrecision x) (qvalue x))) :=
  RatOps.root qvalue_computes rootPrecision_computes
noncomputable def coefCenter (x : List Bool) : List Bool :=
  BinaryRational.encode (1/((dimension x+1)*Ellipsoid.rationalRootUpper (rootPrecision x) (qvalue x)))
noncomputable def coefCenter_computes : PolyComputes coefCenter :=
  RatOps.div (RatOps.const 1) (RatOps.mul (RatOps.add dimension_computes (RatOps.const 1)) root_computes)

noncomputable def scaledHaInput (x : List Bool) : List Bool := pairBits (coefCenter x,haWords x)
noncomputable def scaledHaInput_computes : PolyComputes scaledHaInput := coefCenter_computes.pair haWords_computes
noncomputable def scaledHa : List Bool → List Bool := vectorScale ∘ scaledHaInput
noncomputable def scaledHa_computes : PolyComputes scaledHa := scaledHaInput_computes.comp vectorScale_computes
noncomputable def centerInput (x : List Bool) : List Bool := pairBits (center x,scaledHa x)
noncomputable def centerInput_computes : PolyComputes centerInput := center_computes.pair scaledHa_computes
noncomputable def centerWords : List Bool → List Bool := vectorSub ∘ centerInput
noncomputable def centerWords_computes : PolyComputes centerWords := centerInput_computes.comp vectorSub_computes
lemma centerWords_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    centerWords (pack H a c D)=rowEncode (Ellipsoid.rationalStepCenter H a c) := by
  simp only [centerWords,Function.comp_apply,centerInput,center_pack,scaledHa,scaledHaInput,
    coefCenter,dimension,dim_pack,value_bits,rootPrecision,qvalue,quadWords_pack,
    BinaryRational.decode_encode,haWords_pack,vectorScale_encode,vectorSub_encode,
    Ellipsoid.rationalStepCenter,Fintype.card_fin]

noncomputable def outerInput (x : List Bool) : List Bool := pairBits (haWords x,haWords x)
noncomputable def outerInput_computes : PolyComputes outerInput := haWords_computes.pair haWords_computes
noncomputable def outerWords : List Bool → List Bool := outer ∘ outerInput
noncomputable def outerWords_computes : PolyComputes outerWords := outerInput_computes.comp outer_computes
noncomputable def scaledOuterInput (x : List Bool) : List Bool := pairBits (coefB x,outerWords x)
noncomputable def scaledOuterInput_computes : PolyComputes scaledOuterInput := coefB_computes.pair outerWords_computes
noncomputable def scaledOuter : List Bool → List Bool := matrixScale ∘ scaledOuterInput
noncomputable def scaledOuter_computes : PolyComputes scaledOuter := scaledOuterInput_computes.comp matrixScale_computes
noncomputable def differenceInput (x : List Bool) : List Bool := pairBits (shape x,scaledOuter x)
noncomputable def differenceInput_computes : PolyComputes differenceInput := shape_computes.pair scaledOuter_computes
noncomputable def difference : List Bool → List Bool := matrixSub ∘ differenceInput
noncomputable def difference_computes : PolyComputes difference := differenceInput_computes.comp matrixSub_computes
noncomputable def cutInput (x : List Bool) : List Bool := pairBits (coefA x,difference x)
noncomputable def cutInput_computes : PolyComputes cutInput := coefA_computes.pair difference_computes
noncomputable def cutWords : List Bool → List Bool := matrixScale ∘ cutInput
noncomputable def cutWords_computes : PolyComputes cutWords := cutInput_computes.comp matrixScale_computes
noncomputable def inflateInput (x : List Bool) : List Bool := pairBits (coefInflate x,cutWords x)
noncomputable def inflateInput_computes : PolyComputes inflateInput := coefInflate_computes.pair cutWords_computes
noncomputable def inflateWords : List Bool → List Bool := matrixScale ∘ inflateInput
noncomputable def inflateWords_computes : PolyComputes inflateWords := inflateInput_computes.comp matrixScale_computes
lemma inflateWords_pack {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    inflateWords (pack H a c D)=encode (Ellipsoid.rationalInflatedShape H a) := by
  simp only [inflateWords,Function.comp_apply,inflateInput,coefInflate,dimension,dim_pack,value_bits,
    cutWords,cutInput,coefA,difference,differenceInput,shape_pack,scaledOuter,scaledOuterInput,
    coefB,qvalue,quadWords_pack,BinaryRational.decode_encode,outerWords,outerInput,haWords_pack,
    outer_encode,matrixScale_encode,matrixSub_encode,Ellipsoid.rationalInflatedShape,
    Ellipsoid.rationalCutShape,Fintype.card_fin]
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
