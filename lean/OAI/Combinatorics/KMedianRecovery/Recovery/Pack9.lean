import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.BoundRow
import OAI.Combinatorics.KMedianRecovery.Encoding.Encode3

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open UnaryResources NaturalArray

def pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : List Bool :=
  pairBits (List.replicate n true,pairBits (List.replicate m true,
    pairBits (B.bits,pairBits (H.bits,BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (A r) (b r)))))))
def nword : List Bool → List Bool := extractPrefix
def rest₁ : List Bool → List Bool := discardPrefix
def mword : List Bool → List Bool := extractPrefix ∘ rest₁
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest₁
def bound : List Bool → List Bool := extractPrefix ∘ rest₂
def rest₃ : List Bool → List Bool := discardPrefix ∘ rest₂
def height : List Bool → List Bool := extractPrefix ∘ rest₃
def rows : List Bool → List Bool := discardPrefix ∘ rest₃
noncomputable def nword_computes : PolyComputes nword := extractPrefix_computes
noncomputable def rest₁_computes : PolyComputes rest₁ := discardPrefix_computes
noncomputable def mword_computes : PolyComputes mword := rest₁_computes.comp extractPrefix_computes
noncomputable def rest₂_computes : PolyComputes rest₂ := rest₁_computes.comp discardPrefix_computes
noncomputable def bound_computes : PolyComputes bound := rest₂_computes.comp extractPrefix_computes
noncomputable def rest₃_computes : PolyComputes rest₃ := rest₂_computes.comp discardPrefix_computes
noncomputable def height_computes : PolyComputes height := rest₃_computes.comp extractPrefix_computes
noncomputable def rows_computes : PolyComputes rows := rest₃_computes.comp discardPrefix_computes
lemma projections_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    nword (pack A b B H)=List.replicate n true ∧ mword (pack A b B H)=List.replicate m true ∧
    bound (pack A b B H)=B.bits ∧ height (pack A b B H)=H.bits ∧
    rows (pack A b B H)=BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (A r) (b r))) := by
  simp only [pack,nword,mword,rest₁,rest₂,rest₃,bound,height,rows,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,and_self]
noncomputable def dim : List Bool → List Bool := lengthBits ∘ nword
noncomputable def count : List Bool → List Bool := lengthBits ∘ mword
noncomputable def dim_computes : PolyComputes dim := nword_computes.comp lengthBits_computes
noncomputable def count_computes : PolyComputes count := mword_computes.comp lengthBits_computes
lemma dim_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : dim (pack A b B H)=n.bits := by
  rw [dim,Function.comp_apply,lengthBits_eq,(projections_pack A b B H).1,List.length_replicate]
lemma count_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : count (pack A b B H)=m.bits := by
  rw [count,Function.comp_apply,lengthBits_eq,(projections_pack A b B H).2.1,List.length_replicate]

def nextDim (x : List Bool) : List Bool := nword x++[true]
noncomputable def nextDim_computes : PolyComputes nextDim := nword_computes.append (const_computes [true])
lemma nextDim_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    nextDim (pack A b B H)=List.replicate (n+1) true := by
  rw [nextDim,(projections_pack A b B H).1,List.replicate_succ']
noncomputable def rowFactor (x : List Bool) : List Bool :=
  (value (count x)+2*value (dim x)+2*(value (dim x)+1)).bits
noncomputable def rowFactor_computes : PolyComputes rowFactor := by
  unfold rowFactor
  have hh := NatOps.add (NatOps.add count_computes (NatOps.mul (const_computes (2:ℕ).bits) dim_computes))
    (NatOps.mul (const_computes (2:ℕ).bits) (NatOps.add dim_computes (const_computes (1:ℕ).bits)))
  simpa only [value_bits] using hh
noncomputable def base (x : List Bool) : List Bool := (value (rowFactor x)*(value (height x)*value (height x))).bits
noncomputable def base_computes : PolyComputes base := by
  unfold base
  have hh := NatOps.mul rowFactor_computes (NatOps.mul height_computes height_computes)
  simpa only [value_bits] using hh
noncomputable def power (x : List Bool) : List Bool := exponentiate (pairBits (nextDim x,base x))
noncomputable def power_computes : PolyComputes power := (nextDim_computes.pair base_computes).comp exponentiate_computes
noncomputable def factorial : List Bool → List Bool := factorialWords ∘ nextDim
noncomputable def factorial_computes : PolyComputes factorial := nextDim_computes.comp factorialWords_computes
noncomputable def gap (x : List Bool) : List Bool := (value (factorial x)*value (power x)).bits
noncomputable def gap_computes : PolyComputes gap := NatOps.mul factorial_computes power_computes
lemma gap_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    gap (pack A b B H)=(gapDenominator m n H).bits := by
  simp only [gap,factorial,Function.comp_apply,nextDim_pack,factorialWords_replicate,power,base,
    rowFactor,count_pack,dim_pack,(projections_pack A b B H).2.2.2.1,value_bits]
  rw [exponentiate_pair,List.length_replicate,value_bits]
  simp only [gapDenominator,pow_two]
noncomputable def doubledGap (x : List Bool) : List Bool := (2*value (gap x)).bits
noncomputable def doubledGap_computes : PolyComputes doubledGap := by
  unfold doubledGap
  have hh := NatOps.mul (const_computes (2:ℕ).bits) gap_computes
  simpa only [value_bits] using hh
noncomputable def epsilon (x : List Bool) : List Bool := BinaryRational.encode (1/(value (doubledGap x):ℚ))
noncomputable def epsilon_computes : PolyComputes epsilon := RatOps.div (RatOps.const 1) (RatOps.nat doubledGap_computes)
lemma epsilon_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    epsilon (pack A b B H)=BinaryRational.encode (gapEpsilon m n H) := by
  simp only [epsilon,doubledGap,gap_pack,value_bits,gapEpsilon,Nat.cast_mul,Nat.cast_ofNat]
noncomputable def precisionArg (x : List Bool) : List Bool := (value (doubledGap x)*value (height x)).bits
noncomputable def precisionArg_computes : PolyComputes precisionArg := NatOps.mul doubledGap_computes height_computes
noncomputable def precision : List Bool → List Bool := unaryLog ∘ precisionArg
noncomputable def precision_computes : PolyComputes precision := precisionArg_computes.comp unaryLog_computes
lemma precision_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    precision (pack A b B H)=List.replicate (precisionLog m n H) true := by
  simp only [precision,Function.comp_apply,precisionArg,doubledGap,gap_pack,
    (projections_pack A b B H).2.2.2.1,value_bits,unaryLog_bits,precisionLog]
noncomputable def radius (x : List Bool) : List Bool := (value (dim x)*(value (bound x)+1)).bits
noncomputable def radius_computes : PolyComputes radius := by
  unfold radius
  have hh := NatOps.mul dim_computes (NatOps.add bound_computes (const_computes (1:ℕ).bits))
  simpa only [value_bits] using hh
lemma radius_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    radius (pack A b B H)=(n*(B+1)).bits := by
  simp only [radius,dim_pack,(projections_pack A b B H).2.2.1,value_bits]
noncomputable def radiusPrecision : List Bool → List Bool := unaryLog ∘ radius
noncomputable def radiusPrecision_computes : PolyComputes radiusPrecision := radius_computes.comp unaryLog_computes
lemma radiusPrecision_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    radiusPrecision (pack A b B H)=List.replicate (radiusLog n B) true := by
  simp only [radiusPrecision,Function.comp_apply,radius_pack,unaryLog_bits,radiusLog]
end BinaryDecision
end MetricKMedianRecovery.BitMachine

end OAI
