import OAI.Combinatorics.ContingencyTables.Rooted.RootedForestPrepareProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleRational

namespace OAI

/-! # A polynomial binary program for the actual forest exponent

The bin width and height are computed from the dimension allowance,
capacity scale and phase coefficient. All forest metadata is generated
from the cell arrays by `RootedForestPrepareProgram`.
-/

namespace ContingencyTables.RootedPenaltyEvaluateProgram

open MatchingFPRAS.TreeTyped
open scoped Classical

abbrev Parameters := (ℕ×ℕ)×(ℕ×ℕ)
abbrev Input := Parameters×(RootedDemandProgram.Input×List ℕ)

def squareDimension (z : Parameters) : ℕ := z.1.1*z.1.1
def squareDimensionRealizer : Realizer squareDimension :=
  composition (pair (composition first first) (composition first first)) multiply
lemma polynomial_squareDimension : PolynomialTime squareDimensionRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_first polynomial_first)) polynomial_multiply

def scaledSquare (z : Parameters) : ℕ := z.2.1*squareDimension z
def scaledSquareRealizer : Realizer scaledSquare :=
  composition (f := fun z : Parameters => (z.2.1,squareDimension z)) (g := fun z => z.1*z.2)
    (pair (composition second first) squareDimensionRealizer) multiply
lemma polynomial_scaledSquare : PolynomialTime scaledSquareRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_second polynomial_first) polynomial_squareDimension)
    polynomial_multiply

def width (z : Parameters) : ℕ := 16*scaledSquare z
def widthRealizer : Realizer width :=
  composition (f := fun z : Parameters => (16,scaledSquare z)) (g := fun z => z.1*z.2)
    (pair (constant 16) scaledSquareRealizer) multiply
lemma polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 16) polynomial_scaledSquare)
    polynomial_multiply

def baseHeight (z : Parameters) : ℕ := 10*scaledSquare z
def baseHeightRealizer : Realizer baseHeight :=
  composition (f := fun z : Parameters => (10,scaledSquare z)) (g := fun z => z.1*z.2)
    (pair (constant 10) scaledSquareRealizer) multiply
lemma polynomial_baseHeight : PolynomialTime baseHeightRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 10) polynomial_scaledSquare)
    polynomial_multiply

def height (z : Parameters) : ℕ := baseHeight z*(z.1.2+1)
def heightRealizer : Realizer height :=
  composition (f := fun z : Parameters => (baseHeight z,z.1.2+1)) (g := fun z => z.1*z.2)
    (pair baseHeightRealizer (composition (composition first second) successor)) multiply
lemma polynomial_height : PolynomialTime heightRealizer :=
  polynomial_composition (polynomial_pair polynomial_baseHeight
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_successor)) polynomial_multiply

def forestInput (z : Input) : RootedForestPrepareProgram.Input :=
  (((z.1.2.1,width z.1),z.2.1),z.2.2)
def forestInputRealizer : Realizer forestInput :=
  pair (pair (pair (composition (composition first second) first)
    (composition (f := fun z : Input => z.1) (g := width) first widthRealizer))
    (composition second first)) (composition second second)
lemma polynomial_forestInput : PolynomialTime forestInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_first)
    (polynomial_composition polynomial_first polynomial_width))
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_composition polynomial_second polynomial_second)

def exponentInput (z : Input) : ForestPenaltyProgram.ExponentInput :=
  ((z.1.2.2,height z.1),RootedForestPrepareProgram.prepare (forestInput z))
def exponentInputRealizer : Realizer exponentInput :=
  pair (pair (composition (composition first second) second)
    (composition (f := fun z : Input => z.1) (g := height) first heightRealizer))
    (composition (f := forestInput) (g := RootedForestPrepareProgram.prepare)
      forestInputRealizer RootedForestPrepareProgram.prepareRealizer)
lemma polynomial_exponentInput : PolynomialTime exponentInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_second) (polynomial_composition polynomial_first polynomial_height))
    (polynomial_composition polynomial_forestInput RootedForestPrepareProgram.polynomial_prepare)

def evaluate (z : Input) : ℕ := ForestPenaltyProgram.exponentCode (exponentInput z)
def evaluateRealizer : Realizer evaluate :=
  composition (f := exponentInput) (g := ForestPenaltyProgram.exponentCode)
    exponentInputRealizer ForestPenaltyProgram.exponentCodeRealizer
theorem polynomial_evaluate : PolynomialTime evaluateRealizer :=
  polynomial_composition polynomial_exponentInput ForestPenaltyProgram.polynomial_exponentCode

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

noncomputable def data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C a : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) : Input :=
  (((A.d,A.W),(C,a)),(RootedDemandProgram.data A x q,
    List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))))

lemma width_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C a : ℕ) :
    width ((A.d,A.W),(C,a))=CompanionOracleDensity.rationalBinWidth A C := by
  simp only [width,scaledSquare,squareDimension,CompanionOracleDensity.rationalBinWidth,pow_two]
  ring

lemma height_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C a : ℕ) :
    height ((A.d,A.W),(C,a))=CompanionOracleDensity.rationalHeight A C := by
  simp only [height,baseHeight,scaledSquare,squareDimension,
    CompanionOracleDensity.rationalHeight,pow_two]
  ring

theorem exponentInput_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C a : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) :
    exponentInput (data A C a x q v)=
      ((a,CompanionOracleDensity.rationalHeight A C),
        RootedPenaltyProgram.data A (rowColumn A.T) C
          (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ))
          (RootedForestCatalog.treeEquiv A) (RootedForestCatalog.freeEquiv A) v) := by
  unfold exponentInput data forestInput
  rw [width_data,height_data]
  exact congrArg (fun p => ((a,CompanionOracleDensity.rationalHeight A C),p))
    (RootedForestPrepareProgram.prepare_data A C x q v)

/-- The code evaluates the literal rational forest penalty with its
source normalization, without an affine-data or evaluator hypothesis. -/
theorem evaluate_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C a : ℕ) (hC : 0 < C)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) :
    evaluate (data A C a x q v)=
      ⌊(a:ℚ)/CompanionOracleDensity.rationalHeight A C*
        RootedPenaltyProgram.rationalPenalty A (rowColumn A.T) C
          (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) (fun f => (v f:ℚ))⌋₊ := by
  rw [evaluate,exponentInput_data]
  exact RootedPenaltyProgram.exponentCode_data A (rowColumn A.T) C a hC _ _
    (RootedForestCatalog.treeEquiv A) (RootedForestCatalog.freeEquiv A) v

end ContingencyTables.RootedPenaltyEvaluateProgram

end OAI
