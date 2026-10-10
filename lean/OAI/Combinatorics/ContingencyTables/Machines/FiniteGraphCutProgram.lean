import OAI.Combinatorics.ContingencyTables.Transport.FiniteGraphRootSemantics
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCut

namespace OAI

/-! # Executing the selected root-away cut

Deletion filters the stored adjacency rows. The endpoint and cut side
are then computed by the bounded reachability program.
-/

namespace ContingencyTables.FiniteGraphCutProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram

abbrev EdgeInput := GraphCode×(ℕ×ℕ)
abbrev KeepInput := ((ℕ×ℕ)×ℕ)×ℕ

def keep (z : KeepInput) : Bool :=
  if z.1.2=z.1.1.1 then decide (z.2≠z.1.1.2)
  else if z.1.2=z.1.1.2 then decide (z.2≠z.1.1.1) else true

def keepRealizer : Realizer keep := by
  let I : Realizer (fun z : KeepInput => z.1.2) := composition first second
  let U : Realizer (fun z : KeepInput => z.1.1.1) := composition (composition first first) first
  let V : Realizer (fun z : KeepInput => z.1.1.2) := composition (composition first first) second
  let neqU := composition (composition (pair second U) natEqual) boolNot
  let neqV := composition (composition (pair second V) natEqual) boolNot
  exact (choose (composition (pair I U) natEqual) neqV
    (choose (composition (pair I V) natEqual) neqU (constant true))).congr (by
      intro z
      simp [keep])

lemma polynomial_keep : PolynomialTime keepRealizer := by
  unfold keepRealizer
  have hi : PolynomialTime (composition (first (A := (ℕ×ℕ)×ℕ) (B := ℕ)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hu : PolynomialTime (composition
      (composition (first (A := (ℕ×ℕ)×ℕ) (B := ℕ)) first) first) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first
  have hv : PolynomialTime (composition
      (composition (first (A := (ℕ×ℕ)×ℕ) (B := ℕ)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  exact polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair hi hu) polynomial_natEqual)
    (polynomial_composition (polynomial_composition (polynomial_pair polynomial_second hv)
      polynomial_natEqual) polynomial_boolNot)
    (polynomial_choose (polynomial_composition (polynomial_pair hi hv) polynomial_natEqual)
      (polynomial_composition (polynomial_composition (polynomial_pair polynomial_second hu)
        polynomial_natEqual) polynomial_boolNot) (polynomial_constant true)))

def deleteRow (z : EdgeInput×ℕ) : List ℕ :=
  (z.1.1.getD z.2 []).filter (fun a => keep ((z.1.2,z.2),a))

def deleteRowRealizer : Realizer deleteRow :=
  composition (f := fun z : EdgeInput×ℕ =>
      ((z.1.2,z.2),z.1.1.getD z.2 []))
    (g := fun z : ((ℕ×ℕ)×ℕ)×List ℕ => z.2.filter (fun a => keep (z.1,a)))
    (pair (pair (composition first second) second)
      (composition (pair (composition first first) second) (getDFast [])))
    (filterWith keepRealizer)

lemma polynomial_deleteRow : PolynomialTime deleteRowRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast []))) (polynomial_filterWith polynomial_keep)

def deleteGraph (z : EdgeInput) : GraphCode :=
  (indices z.1).map (fun i => deleteRow (z,i))

def deleteGraphRealizer : Realizer deleteGraph :=
  composition (pair identity (composition first indicesRealizer)) (mapWith deleteRowRealizer)

theorem polynomial_deleteGraph : PolynomialTime deleteGraphRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_mapWith polynomial_deleteRow)

def reachableCode (z : Input×ℕ) : Bool := decide (z.2∈reached z.1)

def reachableCodeRealizer : Realizer reachableCode :=
  composition (pair (composition first reachedRealizer) second) membership

lemma polynomial_reachableCode : PolynomialTime reachableCodeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_reached) polynomial_second)
    polynomial_membership

abbrev CutInput := EdgeInput×ℕ

def awayCode (z : CutInput) : ℕ :=
  if reachableCode ((deleteGraph z.1,z.1.2.1),z.2) then z.1.2.2 else z.1.2.1

def awayTestRealizer : Realizer (fun z : CutInput =>
    reachableCode ((deleteGraph z.1,z.1.2.1),z.2)) :=
  composition (pair (pair (composition first deleteGraphRealizer)
    (composition (composition first second) first)) second) reachableCodeRealizer

lemma polynomial_awayTest : PolynomialTime awayTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_deleteGraph)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_first)) polynomial_second) polynomial_reachableCode

def awayCodeRealizer : Realizer awayCode :=
  choose awayTestRealizer (composition (composition first second) second)
    (composition (composition first second) first)

lemma polynomial_awayCode : PolynomialTime awayCodeRealizer :=
  polynomial_choose polynomial_awayTest
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_first)

def cutCode (z : CutInput×ℕ) : Bool :=
  reachableCode ((deleteGraph z.1.1,awayCode z.1),z.2)

def cutCodeRealizer : Realizer cutCode :=
  composition (pair (pair
    (composition (composition first first) deleteGraphRealizer)
    (composition first awayCodeRealizer)) second) reachableCodeRealizer

theorem polynomial_cutCode : PolynomialTime cutCodeRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_deleteGraph)
    (polynomial_composition polynomial_first polynomial_awayCode)) polynomial_second)
    polynomial_reachableCode

def canonicalCutCode (z : EdgeInput×ℕ) : Bool :=
  cutCode ((z.1,rootCode (z.1.1,z.1.2.1)),z.2)

def canonicalCutCodeRealizer : Realizer canonicalCutCode :=
  composition (pair (pair first
    (composition (pair (composition first first)
      (composition (composition first second) first)) rootCodeRealizer)) second)
    cutCodeRealizer

theorem polynomial_canonicalCutCode : PolynomialTime canonicalCutCodeRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_first)) polynomial_rootCode)) polynomial_second) polynomial_cutCode

end ContingencyTables.FiniteGraphCutProgram

end OAI
