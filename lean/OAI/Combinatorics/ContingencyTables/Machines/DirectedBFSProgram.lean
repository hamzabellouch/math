import OAI.Combinatorics.ContingencyTables.Transport.DirectedBFSCode
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialCollections
import OAI.Combinatorics.MatchingCount.Machines.TreeSum
import OAI.Combinatorics.MatchingCount.Machines.TreeFastLookup
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure

namespace OAI

/-! # Polynomial binary programs for one stored BFS round -/

namespace ContingencyTables.DirectedBFSProgram

open MatchingFPRAS.TreeTyped Polynomial DirectedBFSCode

abbrev Context := Graph×Store
abbrev Query := Context×ℕ
abbrev Candidate := Query×ℕ

def indices (g : Graph) : List ℕ := List.range g.length
def indicesRealizer : Realizer indices := composition listLength range

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange polynomial_listLength X
  intro g
  simpa only [Function.comp_apply,eval_X] using list_length_le_weight g

def pathSomeRealizer : Realizer (fun o : Option (List ℕ)=>o.isSome) :=
  (composition (pair (constant false) identity)
    (optionCases (constant false) (constant true))).congr (by
      intro o
      cases o <;> rfl)

lemma polynomial_pathSome : PolynomialTime pathSomeRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair (polynomial_constant false) polynomial_identity)
    (polynomial_optionCases (polynomial_constant false) (polynomial_constant true)))

def lookupPath (z : Store×ℕ) : Option (List ℕ) := lookup z.1 z.2
def lookupRealizer : Realizer lookupPath := getDFast none
lemma polynomial_lookup : PolynomialTime lookupRealizer := polynomial_getDFast none

def readEdge (z : (Graph×ℕ)×ℕ) : Bool := adjacent z.1.1 z.1.2 z.2
def readEdgeRealizer : Realizer readEdge :=
  composition (pair (composition first (getDFast [])) second) (getDFast false)

lemma polynomial_readEdge : PolynomialTime readEdgeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_getDFast [])) polynomial_second)
    (polynomial_getDFast false)

def candidate (z : Candidate) : Bool :=
  (lookup z.1.1.2 z.2).isSome && adjacent z.1.1.1 z.2 z.1.2

def candidateRealizer : Realizer candidate := by
  let G : Realizer (fun z : Candidate=>z.1.1.1) := composition (composition first first) first
  let P : Realizer (fun z : Candidate=>z.1.1.2) := composition (composition first first) second
  let V : Realizer (fun z : Candidate=>z.1.2) := composition first second
  let U : Realizer (fun z : Candidate=>z.2) := second
  let known : Realizer (fun z : Candidate=>(lookup z.1.1.2 z.2).isSome) :=
    composition (composition (pair P U) lookupRealizer) pathSomeRealizer
  let edge : Realizer (fun z : Candidate=>adjacent z.1.1.1 z.2 z.1.2) :=
    composition (pair (pair G U) V) readEdgeRealizer
  exact composition (pair known edge) boolAnd

lemma polynomial_candidate : PolynomialTime candidateRealizer := by
  unfold candidateRealizer
  apply polynomial_composition
  · apply polynomial_pair
    · exact polynomial_composition
        (polynomial_composition (polynomial_pair
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_second) polynomial_second) polynomial_lookup) polynomial_pathSome
    · exact polynomial_composition (polynomial_pair
        (polynomial_pair
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_first) polynomial_second)
        (polynomial_composition polynomial_first polynomial_second)) polynomial_readEdge
  · exact polynomial_boolAnd

def headOptionRealizer : Realizer (fun xs : List ℕ=>xs.head?) :=
  (listCase none (composition first some)).congr (by intro xs;cases xs <;> rfl)

lemma polynomial_headOption : PolynomialTime headOptionRealizer :=
  polynomial_congr _ (polynomial_listCase none
    (polynomial_composition polynomial_first polynomial_some))

def predecessorInput (z : Query) : Option ℕ := DirectedBFSCode.predecessor z.1.1 z.1.2 z.2

def predecessorRealizer : Realizer predecessorInput :=
  (composition (composition (pair identity
      (composition (composition first first) indicesRealizer)) (filterWith candidateRealizer))
    headOptionRealizer).congr (by
      intro z
      simp only [Function.comp_apply,id_eq,predecessorInput,DirectedBFSCode.predecessor,indices,
        List.head?_filter,candidate])

lemma polynomial_predecessor : PolynomialTime predecessorRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_pair polynomial_identity
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_indices)) (polynomial_filterWith polynomial_candidate)) polynomial_headOption)

def appendPath (z : Query×List ℕ) : Option (List ℕ) := Option.some (z.2++[z.1.2])

def appendPathRealizer : Realizer appendPath :=
  composition (composition (pair second
      (composition (pair (composition first second) (constant [])) listCons)) append) some

lemma polynomial_appendPath : PolynomialTime appendPathRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_second (polynomial_composition
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        (polynomial_constant [])) polynomial_listCons)) polynomial_append) polynomial_some

def fromPredecessor (z : Query×ℕ) : Option (List ℕ) :=
  (lookup z.1.1.2 z.2).map (fun xs=>xs++[z.1.2])

def fromPredecessorRealizer : Realizer fromPredecessor :=
  (composition (pair first
      (composition (pair (composition (composition first first) second) second) lookupRealizer))
    (optionCases (constant none) appendPathRealizer)).congr (by
      intro z
      dsimp only [Function.comp_apply,lookupPath,fromPredecessor,appendPath]
      cases h : lookup z.1.1.2 z.2 <;> rfl)

lemma polynomial_fromPredecessor : PolynomialTime fromPredecessorRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_second) polynomial_lookup))
    (polynomial_optionCases (polynomial_constant none) polynomial_appendPath))

def missing (z : Query) : Option (List ℕ) :=
  (predecessorInput z).bind (fun u=>fromPredecessor (z,u))

def missingRealizer : Realizer missing :=
  (composition (pair identity predecessorRealizer)
    (optionCases (constant none) fromPredecessorRealizer)).congr (by
      intro z
      dsimp only [Function.comp_apply,id_eq,missing]
      cases h : predecessorInput z <;> rfl)

lemma polynomial_missing : PolynomialTime missingRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_predecessor)
    (polynomial_optionCases (polynomial_constant none) polynomial_fromPredecessor))

def rowInput (z : Query) : Option (List ℕ) := roundRow z.1.1 z.1.2 z.2

def rowRealizer : Realizer rowInput :=
  (composition (pair identity
      (composition (pair (composition first second) second) lookupRealizer))
    (optionCases missingRealizer (composition second some))).congr (by
      intro z
      dsimp only [Function.comp_apply,id_eq,lookupPath,rowInput,roundRow]
      cases h : lookup z.1.2 z.2 <;> rfl)

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_composition
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second) polynomial_lookup))
    (polynomial_optionCases polynomial_missing
      (polynomial_composition polynomial_second polynomial_some)))

def roundInput (z : Context) : Store := round z.1 z.2
def roundRealizer : Realizer roundInput :=
  composition (pair identity (composition first indicesRealizer)) (mapWith rowRealizer)

theorem polynomial_round : PolynomialTime roundRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_mapWith polynomial_row)

end ContingencyTables.DirectedBFSProgram

end OAI
