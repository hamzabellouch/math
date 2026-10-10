import OAI.Combinatorics.ContingencyTables.Machines.WeightedArgmaxProgram
import OAI.Combinatorics.ContingencyTables.Machines.FiniteGraphCutProgram

namespace OAI

/-! # Choosing the heaviest edge between distinct forest components

The filter runs the actual finite component-search program. The maximum
scan receives only eligible stored edges and retains their binary weights.
-/

namespace ContingencyTables.ForestEdgeChoiceProgram

open MatchingFPRAS.TreeTyped WeightedArgmaxProgram FiniteGraphRootProgram
open FiniteGraphCutProgram
open scoped Classical

abbrev Input := GraphCode×List Edge
abbrev TestInput := Input×Edge

def query (z : TestInput) : FiniteGraphRootProgram.Input×ℕ :=
  ((z.1.1,z.2.1.1),z.2.1.2)
def queryRealizer : Realizer query :=
  pair (pair (composition first first) (composition (composition second first) first))
    (composition (composition second first) second)
lemma polynomial_query : PolynomialTime queryRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_first))
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_second)

def eligible (z : TestInput) : Bool := !reachableCode (query z)
def eligibleRealizer : Realizer eligible :=
  composition (composition (f := query) (g := reachableCode) queryRealizer
    reachableCodeRealizer) boolNot
lemma polynomial_eligible : PolynomialTime eligibleRealizer :=
  polynomial_composition (polynomial_composition polynomial_query polynomial_reachableCode)
    polynomial_boolNot

def filtered (z : Input) : List Edge := z.2.filter (fun e=>eligible (z,e))
def filteredRealizer : Realizer filtered :=
  composition (pair identity second) (filterWith eligibleRealizer)
lemma polynomial_filtered : PolynomialTime filteredRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_second)
    (polynomial_filterWith polynomial_eligible)

def choice (z : Input) : Option Edge := WeightedArgmaxProgram.best (filtered z)
def choiceRealizer : Realizer choice :=
  composition (f := filtered) (g := WeightedArgmaxProgram.best)
    filteredRealizer WeightedArgmaxProgram.bestRealizer
lemma polynomial_choice : PolynomialTime choiceRealizer :=
  polynomial_composition polynomial_filtered WeightedArgmaxProgram.polynomial_best

lemma eligible_code {n : ℕ} (T : SimpleGraph (Fin n)) [DecidableRel T.Adj]
    (es : List Edge) (u v : Fin n) (w : ℕ) :
    eligible ((graphCode T,es),((u.val,v.val),w))=true ↔ ¬T.Reachable u v := by
  simp only [eligible,query,reachableCode,Bool.not_eq_true',decide_eq_false_iff_not,
    reached_mem_iff]

lemma choice_mem {z : Input} {e : Edge} (he : choice z=some e) :
    e∈z.2 ∧ eligible (z,e)=true :=
  List.mem_filter.mp (WeightedArgmaxProgram.best_mem he)

lemma choice_max {z : Input} {e a : Edge} (he : choice z=some e)
    (ha : a∈z.2) (hel : eligible (z,a)=true) : a.2≤e.2 :=
  WeightedArgmaxProgram.best_max he (List.mem_filter.mpr ⟨ha,hel⟩)

lemma choice_none {z : Input} (he : choice z=none) :
    ∀ e∈z.2,eligible (z,e)=false := by
  have hn : filtered z=[] := (WeightedArgmaxProgram.best_none _).mp he
  intro e he
  cases h : eligible (z,e) with
  | false=>rfl
  | true=>
    have hm : e∈filtered z := List.mem_filter.mpr ⟨he,h⟩
    rw [hn] at hm
    exact (List.not_mem_nil hm).elim

end ContingencyTables.ForestEdgeChoiceProgram

end OAI
