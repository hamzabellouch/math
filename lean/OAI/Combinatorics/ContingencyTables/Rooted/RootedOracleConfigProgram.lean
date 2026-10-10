import OAI.Combinatorics.ContingencyTables.Rooted.RootedLabelWeightProgram
import OAI.Combinatorics.ContingencyTables.Counting.CountingOracleScheduleProgram
import OAI.Combinatorics.ContingencyTables.Machines.ScalarScheduleProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseWordProgram

namespace OAI

/-! # Computing a phase's physical oracle configuration

Numeric schedules use binary arithmetic. The supplied reserve bounds
the two materialized precision markers; no binary natural controls an
unbounded list allocation.
-/

namespace ContingencyTables.RootedOracleConfigProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingOracleScheduleProgram DensePrograms

abbrev Input := ((RootedOracleWalkProgram.State × Fraction) × ℕ) × List Bool

def fields (z : Input) : List ℕ :=
  [z.1.1.1.1.2.1.1.1,z.1.1.1.1.1,
    RootedPenaltyEvaluateProgram.height z.1.1.1.1.2.1,z.1.2]
private def consR {f : Input → ℕ} {g : Input → List ℕ}
    (F : Realizer f) (G : Realizer g) : Realizer (fun z => f z::g z) :=
  composition (f := fun z : Input => (f z,g z)) (g := fun p : ℕ × List ℕ => p.1::p.2)
    (pair F G) listCons
private lemma polynomial_consR {f : Input → ℕ} {g : Input → List ℕ}
    (F : Realizer f) (G : Realizer g) (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (consR F G) := polynomial_composition (polynomial_pair hF hG) polynomial_listCons

def fieldsRealizer : Realizer fields := by
  let stateR : Realizer (fun z : Input => z.1.1.1) := composition (composition first first) first
  let frameR : Realizer (fun z : Input => z.1.1.1.1) := composition stateR first
  let parametersR : Realizer (fun z : Input => z.1.1.1.1.2.1) :=
    composition (composition frameR second) first
  let dR : Realizer (fun z : Input => z.1.1.1.1.2.1.1.1) :=
    composition (composition parametersR first) first
  let kR : Realizer (fun z : Input => z.1.1.1.1.1) := composition frameR first
  let hR : Realizer (fun z : Input => RootedPenaltyEvaluateProgram.height z.1.1.1.1.2.1) :=
    composition (f := fun z : Input => z.1.1.1.1.2.1)
      (g := RootedPenaltyEvaluateProgram.height) parametersR RootedPenaltyEvaluateProgram.heightRealizer
  exact consR dR (consR kR (consR hR (consR (composition first second) (constant []))))
lemma polynomial_fields : PolynomialTime fieldsRealizer := by
  unfold fieldsRealizer
  apply polynomial_consR
  · tree_poly
  apply polynomial_consR
  · tree_poly
  apply polynomial_consR
  · exact polynomial_composition (by tree_poly) RootedPenaltyEvaluateProgram.polynomial_height
  exact polynomial_consR _ _ (polynomial_composition polynomial_first polynomial_second)
    (polynomial_constant [])

def dim : Expr := .input 0
def grid : Expr := .input 1
def height : Expr := .input 2
def phase : Expr := .input 3
def mixing : Expr := 2*(10000*dim^2*grid)^2
def allowance : Expr := height+dim*grid+2
def relativeDenominator : Expr := 400*(phase+1)

def scalar (e : Expr) (z : Input) : ℕ := e.eval (fields z)
def scalarRealizer (e : Expr) : Realizer (scalar e) :=
  composition (f := fields) (g := e.eval) fieldsRealizer e.realizer
lemma polynomial_scalar (e : Expr) : PolynomialTime (scalarRealizer e) :=
  polynomial_composition polynomial_fields e.polynomial

def inner (z : Input) : Fraction :=
  TreeFraction.div (z.1.1.2,natural (scalar relativeDenominator z))
def innerRealizer : Realizer inner :=
  composition (f := fun z : Input => (z.1.1.2,natural (scalar relativeDenominator z)))
    (g := TreeFraction.div)
    (pair (composition (composition first first) second)
      (composition (f := scalar relativeDenominator) (g := natural)
        (scalarRealizer relativeDenominator) naturalRealizer)) TreeFraction.divRealizer
lemma polynomial_inner : PolynomialTime innerRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_scalar relativeDenominator) polynomial_natural))
    TreeFraction.polynomial_div

def correction (z : Input) : Fraction := TreeFraction.div (inner z,(256,1))
def correctionRealizer : Realizer correction :=
  composition (f := fun z : Input => (inner z,(256,1))) (g := TreeFraction.div)
    (pair innerRealizer (constant (256,1))) TreeFraction.divRealizer
lemma polynomial_correction : PolynomialTime correctionRealizer :=
  polynomial_composition (polynomial_pair polynomial_inner (polynomial_constant _)) TreeFraction.polynomial_div

def samples (z : Input) : ℕ := CountingOracleScheduleProgram.sampleCount (z.1.2,(inner z,(1,1)))
def samplesRealizer : Realizer samples :=
  composition (f := fun z : Input => (z.1.2,(inner z,(1,1))))
    (g := CountingOracleScheduleProgram.sampleCount)
    (pair (composition first second) (pair innerRealizer (constant (1,1)))) sampleCountRealizer
lemma polynomial_samples : PolynomialTime samplesRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_pair polynomial_inner (polynomial_constant _))) polynomial_sampleCount

def timeInput (z : Input) : ℕ × ℕ := (scalar mixing z,scalar allowance z)
def timeInputRealizer : Realizer timeInput := pair (scalarRealizer mixing) (scalarRealizer allowance)
lemma polynomial_timeInput : PolynomialTime timeInputRealizer :=
  polynomial_pair (polynomial_scalar mixing) (polynomial_scalar allowance)

def ratioTime (z : Input) : ℕ := CountingOracleScheduleProgram.oracleTime (timeInput z,inner z)
def ratioTimeRealizer : Realizer ratioTime :=
  composition (f := fun z : Input => (timeInput z,inner z))
    (g := CountingOracleScheduleProgram.oracleTime) (pair timeInputRealizer innerRealizer) oracleTimeRealizer
lemma polynomial_ratioTime : PolynomialTime ratioTimeRealizer :=
  polynomial_composition (polynomial_pair polynomial_timeInput polynomial_inner) polynomial_oracleTime

def correctionTime (z : Input) : ℕ := CountingOracleScheduleProgram.oracleTime (timeInput z,correction z)
def correctionTimeRealizer : Realizer correctionTime :=
  composition (f := fun z : Input => (timeInput z,correction z))
    (g := CountingOracleScheduleProgram.oracleTime) (pair timeInputRealizer correctionRealizer) oracleTimeRealizer
lemma polynomial_correctionTime : PolynomialTime correctionTimeRealizer :=
  polynomial_composition (polynomial_pair polynomial_timeInput polynomial_correction) polynomial_oracleTime

def offsetAccuracy (z : Input) : ℕ := CountingOracleScheduleProgram.offsetAccuracy (scalar dim z,inner z)
def offsetAccuracyRealizer : Realizer offsetAccuracy :=
  composition (f := fun z : Input => (scalar dim z,inner z))
    (g := CountingOracleScheduleProgram.offsetAccuracy) (pair (scalarRealizer dim) innerRealizer)
    CountingOracleScheduleProgram.offsetAccuracyRealizer
lemma polynomial_offsetAccuracy : PolynomialTime offsetAccuracyRealizer :=
  polynomial_composition (polynomial_pair (polynomial_scalar dim) polynomial_inner)
    CountingOracleScheduleProgram.polynomial_offsetAccuracy

def normalizedNoise (z : Input) : Fraction := TreeFraction.normalize z.1.1.2
def normalizedNoiseRealizer : Realizer normalizedNoise :=
  composition (composition (composition first first) second) TreeFraction.normalizeRealizer
lemma polynomial_normalizedNoise : PolynomialTime normalizedNoiseRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) TreeFraction.polynomial_normalize

def repeats (z : Input) : ℕ := 64*((normalizedNoise z).2.bits.length+1)
def repeatsRealizer : Realizer repeats :=
  composition (f := fun z : Input => (64,(normalizedNoise z).2.bits.length+1))
    (g := fun p : ℕ × ℕ => p.1*p.2)
    (pair (constant 64) (composition
      (composition (composition (composition normalizedNoiseRealizer second) toBits) listLength)
      successor)) multiply
lemma polynomial_repeats : PolynomialTime repeatsRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 64)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_normalizedNoise polynomial_second) polynomial_toBits)
      polynomial_listLength) polynomial_successor)) polynomial_multiply

def rootDegree (z : Input) : ℕ := ceiling (TreeFraction.div ((512,1),inner z))
def rootDegreeRealizer : Realizer rootDegree :=
  composition (composition (f := fun z : Input => ((512,1),inner z)) (g := TreeFraction.div)
    (pair (constant (512,1)) innerRealizer) TreeFraction.divRealizer) ceilingRealizer
lemma polynomial_rootDegree : PolynomialTime rootDegreeRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant _) polynomial_inner) TreeFraction.polynomial_div) polynomial_ceiling

def depth (z : Input) : ℕ := Nat.clog 2 (rootDegree z)
def depthRealizer : Realizer depth := composition rootDegreeRealizer ceilLogTwoRealizer
lemma polynomial_depth : PolynomialTime depthRealizer :=
  polynomial_composition polynomial_rootDegree polynomial_ceilLogTwo

def markers (z : Input) : List Bool × List Bool := (z.2.take (rootDegree z),z.2.take (depth z))
def markersRealizer : Realizer markers :=
  pair (composition (pair second rootDegreeRealizer) takeFast)
    (composition (pair second depthRealizer) takeFast)
lemma polynomial_markers : PolynomialTime markersRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair polynomial_second polynomial_rootDegree) polynomial_takeFast)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_depth) polynomial_takeFast)

def schedule (z : Input) : RootedEstimatorLayoutProgram.Schedule :=
  ((z.1.2,samples z),((ratioTime z,correctionTime z),offsetAccuracy z))
def scheduleRealizer : Realizer schedule :=
  pair (pair (composition first second) samplesRealizer)
    (pair (pair ratioTimeRealizer correctionTimeRealizer) offsetAccuracyRealizer)
lemma polynomial_schedule : PolynomialTime scheduleRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_samples)
    (polynomial_pair (polynomial_pair polynomial_ratioTime polynomial_correctionTime) polynomial_offsetAccuracy)

def output (z : Input) : RootedLabelWeightProgram.Config :=
  (((z.1.1.1,schedule z),repeats z),markers z)
def outputRealizer : Realizer output :=
  pair (pair (pair (composition (composition first first) first) scheduleRealizer) repeatsRealizer) markersRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_schedule) polynomial_repeats) polynomial_markers

attribute [local irreducible] output

def context (z : Input) : RootedEstimatorLayoutProgram.Context := (output z).1.1
def contextRealizer : Realizer context :=
  composition (composition (f := output) (g := fun c : RootedLabelWeightProgram.Config => c.1)
    outputRealizer first) first
lemma polynomial_context : PolynomialTime contextRealizer :=
  polynomial_composition (polynomial_composition polynomial_output polynomial_first) polynomial_first
attribute [local irreducible] context

def contextWidth (z : Input) : ℕ := RootedEstimatorLayoutProgram.wordWidth (context z)
def contextWidthRealizer : Realizer contextWidth :=
  composition (f := context) (g := RootedEstimatorLayoutProgram.wordWidth)
    contextRealizer RootedEstimatorLayoutProgram.wordWidthRealizer
lemma polynomial_contextWidth : PolynomialTime contextWidthRealizer :=
  polynomial_composition polynomial_context RootedEstimatorLayoutProgram.polynomial_wordWidth
attribute [local irreducible] contextWidth

def wordWidth (z : Input) : ℕ := repeats z*contextWidth z
def wordWidthRealizer : Realizer wordWidth :=
  composition (f := fun z : Input => (repeats z,contextWidth z))
    (g := fun p : ℕ × ℕ => p.1*p.2) (pair repeatsRealizer contextWidthRealizer) multiply
theorem polynomial_wordWidth : PolynomialTime wordWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_repeats polynomial_contextWidth) polynomial_multiply

noncomputable section
open CompanionFactorialApplication GridBoundary CompanionOracleDensity
open scoped Classical
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) : Input :=
  (((RootedOracleWalkProgram.data A C 0 K z v,xi),j),reserve)

lemma fields_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    fields (data A C K j xi z v reserve)=[A.d,K,rationalHeight A C,j] := by
  have hh : 10*(C*(A.d*A.d))*(A.W+1)=10*C*A.d^2*(A.W+1) := by ring
  exact congrArg (fun h => [A.d,K,h,j]) hh

lemma inner_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    TreeFraction.val (inner (data A C K j xi z v reserve))=
      innerTolerance (TreeFraction.val xi/2) j := by
  rw [inner,TreeFraction.div_val,natural_val,scalar,fields_data]
  simp only [relativeDenominator,phase,Expr.eval,List.getD_cons_zero,List.getD_cons_succ,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  unfold innerTolerance
  dsimp only [data]
  field_simp
  ring

lemma repeats_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    repeats (data A C K j xi z v reserve)=CommonBasesFPRAS.repetitionCount (TreeFraction.val xi) := by
  simp only [repeats,normalizedNoise,data,TreeFraction.normalize_repr,TreeFraction.repr,
    CommonBasesFPRAS.repetitionCount]

end
end ContingencyTables.RootedOracleConfigProgram

end OAI
