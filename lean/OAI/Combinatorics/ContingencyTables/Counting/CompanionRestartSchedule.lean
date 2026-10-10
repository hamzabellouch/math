import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitializedRestartProgram

namespace OAI

/-! # A deterministic bit allocation for initialized restart experiments -/
namespace ContingencyTables.CompanionRestartSchedule
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram DensePrograms Polynomial

abbrev Prepared := CompanionPhaseContextProgram.Prepared
abbrev StageInput := Prepared×ℕ
abbrev Input := Prepared×List CompanionPhaseFinishProgram.Stored

def configInput (z : StageInput) : RootedOracleConfigProgram.Input :=
  CompanionPhaseContextProgram.configInput ((z.1,z.2+1),[])
def configInputRealizer : Realizer configInput :=
  composition (f := fun z : StageInput => ((z.1,z.2+1),([] : List Bool)))
    (g := CompanionPhaseContextProgram.configInput)
    (pair (pair first (composition second successor)) (constant []))
    CompanionPhaseContextProgram.configInputRealizer
lemma polynomial_configInput : PolynomialTime configInputRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_successor)) (polynomial_constant []))
    CompanionPhaseContextProgram.polynomial_configInput

def queryWidth (z : StageInput) : ℕ := RootedOracleConfigProgram.wordWidth (configInput z)
def queryWidthRealizer : Realizer queryWidth :=
  composition (f := configInput) (g := RootedOracleConfigProgram.wordWidth)
    configInputRealizer RootedOracleConfigProgram.wordWidthRealizer
lemma polynomial_queryWidth : PolynomialTime queryWidthRealizer :=
  polynomial_composition polynomial_configInput RootedOracleConfigProgram.polynomial_wordWidth

def scalar (e : Expr) (z : StageInput) : ℕ := CountingPhaseParametersProgram.scalar e z.1.2
def scalarRealizer (e : Expr) : Realizer (scalar e) :=
  composition (f := fun z : StageInput => z.1.2) (g := CountingPhaseParametersProgram.scalar e)
    (composition first second) (CountingPhaseParametersProgram.scalarRealizer e)
lemma polynomial_scalar (e : Expr) : PolynomialTime (scalarRealizer e) :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_second)
    (CountingPhaseParametersProgram.polynomial_scalar e)

def proposalWidth (z : StageInput) : ℕ := Nat.clog 2 (scalar (.input 0) z*scalar (.input 0) z)
def proposalWidthRealizer : Realizer proposalWidth :=
  composition (f := fun z : StageInput => scalar (.input 0) z*scalar (.input 0) z)
    (g := Nat.clog 2)
    (composition (f := fun z : StageInput => (scalar (.input 0) z,scalar (.input 0) z))
      (g := fun p : ℕ×ℕ => p.1*p.2) (pair (scalarRealizer (.input 0)) (scalarRealizer (.input 0))) multiply)
    ceilLogTwoRealizer
lemma polynomial_proposalWidth : PolynomialTime proposalWidthRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair (polynomial_scalar _) (polynomial_scalar _))
    polynomial_multiply) polynomial_ceilLogTwo

def precision (z : StageInput) : ℕ := CountingPhaseParametersProgram.precision z.1.2
def precisionRealizer : Realizer precision :=
  composition (f := fun z : StageInput => z.1.2) (g := CountingPhaseParametersProgram.precision)
    (composition first second) CountingPhaseParametersProgram.precisionRealizer
lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_second)
    CountingPhaseParametersProgram.polynomial_precision

 private def consR {f : StageInput→ℕ} {g : StageInput→List ℕ}
    (F : Realizer f) (G : Realizer g) : Realizer (fun z => f z::g z) :=
  composition (f := fun z : StageInput => (f z,g z))
    (g := fun p : ℕ×List ℕ => p.1::p.2) (pair F G) listCons
 private lemma polynomial_consR {f : StageInput→ℕ} {g : StageInput→List ℕ}
    (F : Realizer f) (G : Realizer g) (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (consR F G) := polynomial_composition (polynomial_pair hF hG) polynomial_listCons

def fields (z : StageInput) : List ℕ :=
  [proposalWidth z,queryWidth z,precision z,scalar (.input 3) z,scalar (.input 5) z]
def fieldsRealizer : Realizer fields :=
  consR proposalWidthRealizer (consR queryWidthRealizer (consR precisionRealizer
    (consR (scalarRealizer (.input 3)) (consR (scalarRealizer (.input 5)) (constant [])))))
lemma polynomial_fields : PolynomialTime fieldsRealizer := by
  unfold fieldsRealizer
  exact polynomial_consR _ _ polynomial_proposalWidth (polynomial_consR _ _ polynomial_queryWidth
    (polynomial_consR _ _ polynomial_precision (polynomial_consR _ _ (polynomial_scalar _)
      (polynomial_consR _ _ (polynomial_scalar _) (polynomial_constant [])))))

def expression : Expr := (.input 3)*((.input 4+1)*(1+(.input 0+((.input 1+.input 1)+.input 2))))
def stageWidth (z : StageInput) : ℕ := expression.eval (fields z)
def stageWidthRealizer : Realizer stageWidth :=
  composition (f := fields) (g := expression.eval) fieldsRealizer expression.realizer
theorem polynomial_stageWidth : PolynomialTime stageWidthRealizer :=
  polynomial_composition polynomial_fields expression.polynomial

def indices (z : Input) : List ℕ := List.range z.2.length
def indicesRealizer : Realizer indices := composition (composition second listLength) range
lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.2).trans (weight_snd z)

def indexedWidth (z : Input×ℕ) : ℕ := stageWidth (z.1.1,z.2)
def indexedWidthRealizer : Realizer indexedWidth :=
  composition (f := fun z : Input×ℕ => (z.1.1,z.2)) (g := stageWidth)
    (pair (composition first first) second) stageWidthRealizer
lemma polynomial_indexedWidth : PolynomialTime indexedWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    polynomial_second) polynomial_stageWidth

def restartWidth (z : Input) : ℕ := ((indices z).map (fun i => indexedWidth (z,i))).sum
def restartWidthRealizer : Realizer restartWidth :=
  composition (f := fun z : Input => (indices z).map (fun i => indexedWidth (z,i)))
    (g := List.sum) (composition (pair identity indicesRealizer) (mapWith indexedWidthRealizer)) listSum
theorem polynomial_restartWidth : PolynomialTime restartWidthRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_indexedWidth)) polynomial_listSum

def width (z : Input) : ℕ := CompanionRestartInitializer.width z.1+restartWidth z
def widthRealizer : Realizer width :=
  composition (f := fun z : Input => (CompanionRestartInitializer.width z.1,restartWidth z))
    (g := fun p : ℕ×ℕ => p.1+p.2)
    (pair (composition (f := fun z : Input => z.1) (g := CompanionRestartInitializer.width)
      first CompanionRestartInitializer.widthRealizer) restartWidthRealizer) add
theorem polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first CompanionRestartInitializer.polynomial_width)
    polynomial_restartWidth) polynomial_add

end ContingencyTables.CompanionRestartSchedule

end OAI
