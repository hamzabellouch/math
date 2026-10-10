import OAI.Combinatorics.ContingencyTables.Rooted.RootedComponentSemantics
import OAI.Combinatorics.ContingencyTables.Transport.FiniteGraphRootSemantics

namespace OAI

/-! # Computing every root label before summing its signed demand

The input contains an adjacency list and one positive/negative demand
pair per vertex. The polynomial program computes the root labels itself.
-/

namespace ContingencyTables.RootedComponentCode

open MatchingFPRAS.TreeTyped Polynomial
open RootedCompletion RootedComponentProgram FiniteGraphRootProgram
open scoped BigOperators Classical

abbrev Input := GraphCode×List (ℕ×ℕ)

def entry (z : Input×ℕ) : Record :=
  (rootCode (z.1.1,z.2),z.1.2.getD z.2 (0,0))

def entryRealizer : Realizer entry :=
  pair (composition (pair (composition first first) second) rootCodeRealizer)
    (composition (pair (composition first second) second) (getDFast (0,0)))

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_rootCode)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast (0,0)))

def labels (z : Input) : List Record :=
  (List.range z.2.length).map (fun i => entry (z,i))

def indicesRealizer : Realizer (fun z : Input => List.range z.2.length) :=
  composition (composition second listLength) range

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.2).trans (weight_snd z)

def labelsRealizer : Realizer labels :=
  composition (pair identity indicesRealizer) (mapWith entryRealizer)

lemma polynomial_labels : PolynomialTime labelsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_entry)

def count (z : Input) : ℕ := total (labels z)
def countRealizer : Realizer count := composition labelsRealizer totalRealizer

theorem polynomial_count : PolynomialTime countRealizer :=
  polynomial_composition polynomial_labels polynomial_total

lemma labels_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p q : Fin n → ℕ) :
    labels (FiniteGraphRootProgram.graphCode G,List.ofFn (fun i => (p i,q i)))=
      records (FiniteGraphRoots.root G) p q := by
  apply List.ext_getElem
  · simp only [labels,List.length_map,List.length_range,List.length_ofFn,records]
  · intro i hi hj
    have hin : i<n := by
      simpa only [records,List.length_ofFn] using hj
    simp only [labels,List.getElem_map,List.getElem_range,entry,records,List.getElem_ofFn]
    rw [FiniteGraphRootProgram.rootCode_eq G ⟨i,hin⟩]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hin,dite_true,Option.getD_some]

theorem count_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p q : Fin n → ℕ) :
    count (FiniteGraphRootProgram.graphCode G,List.ofFn (fun i => (p i,q i)))=
      ∑ a,(∑ i,if FiniteGraphRoots.root G i=a then (p i:ℤ)-q i else 0).natAbs := by
  rw [count,labels_graph,total_records]

open CompanionFactorialApplication

/-- The binary root computation produces the actual penalty metadata
for the canonical row-then-column root convention. -/
theorem count_instance {m n : ℕ} (A : Instance (Fin m) (Fin n)) (z : View A → ℕ) :
    count (FiniteGraphRootProgram.graphCode (A.T.comap finSumFinEquiv.symm),
      List.ofFn (fun i : Fin (m+n) =>
        (positiveDemand A z (finSumFinEquiv.symm i),
          negativeDemand A z (finSumFinEquiv.symm i))))=
      RootedPenaltyProgram.rootCount A (rowColumn A.T)
        (ForestScaledPenalty.rowCounts A z) (ForestScaledPenalty.columnCounts A z) := by
  rw [count,labels_graph]
  have hh := total_records_rootCount A (rowColumn A.T)
    (ForestScaledPenalty.rowCounts A z) (ForestScaledPenalty.columnCounts A z)
    finSumFinEquiv.symm
    (fun i => positiveDemand A z (finSumFinEquiv.symm i))
    (fun i => negativeDemand A z (finSumFinEquiv.symm i))
    (fun i => naturalDemand_eq A z (finSumFinEquiv.symm i))
  simpa only [rowColumn_root,Equiv.apply_symm_apply,Equiv.symm_apply_apply] using hh

end ContingencyTables.RootedComponentCode

end OAI
