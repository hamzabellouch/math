import OAI.Combinatorics.ContingencyTables.Sampling.GreedyTableComplexity
import OAI.Combinatorics.ContingencyTables.AlgorithmStatements
import OAI.Combinatorics.MatchingCount.Tapes.Parse
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts

namespace OAI

/-! # Parsing the public margins and printing the greedy matrix

All operations are existing binary list programs. The bounded take and
drop operations also terminate polynomially on malformed headers.
-/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS TreeTyped LiteralCodec LiteralParse
open scoped BigOperators

/-- The first two natural numbers give the lengths of the two margins. -/
def marginLists (ns : List ℕ) : List ℕ × List ℕ :=
  let m := ns.headD 0
  let n := ns.tail.headD 0
  let rest := ns.tail.tail
  (rest.take m,(rest.drop m).take n)

def marginListsRealizer : Realizer marginLists := by
  let M : Realizer (fun ns : List ℕ => ns.headD 0) := head 0
  let N : Realizer (fun ns : List ℕ => ns.tail.headD 0) := composition tail (head 0)
  let D : Realizer (fun ns : List ℕ => ns.tail.tail) := composition tail tail
  exact (pair (composition (pair D M) takeFast)
    (composition (pair (composition (pair D M) dropFast) N) takeFast)).congr (fun _ => rfl)

lemma polynomial_marginLists : PolynomialTime marginListsRealizer := by
  have hM : PolynomialTime (head (A := ℕ) 0) := polynomial_head 0
  have hN : PolynomialTime (composition (tail (A := ℕ)) (head 0)) :=
    polynomial_composition polynomial_tail (polynomial_head 0)
  have hD : PolynomialTime (composition (tail (A := ℕ)) tail) :=
    polynomial_composition polynomial_tail polynomial_tail
  unfold marginListsRealizer
  exact polynomial_congr _ (polynomial_pair
    (polynomial_composition (polynomial_pair hD hM) polynomial_takeFast)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair hD hM) polynomial_dropFast) hN)
      polynomial_takeFast))

def printMatrix (rows : List (List ℕ)) : List Symbol :=
  rows.flatMap (fun row => row.flatMap encodeNat)

def printMatrixRealizer : Realizer printMatrix :=
  flatMapPoly (flatMapPoly natWordRealizer)

lemma polynomial_printMatrix : PolynomialTime printMatrixRealizer :=
  polynomial_flatMapPoly (polynomial_flatMapPoly polynomial_natWord)

def publicGreedy (as : List Symbol) : List Symbol :=
  let margins := marginLists (parse as)
  printMatrix (listMatrix margins.1 margins.2)

def publicGreedyRealizer : Realizer publicGreedy :=
  (composition (composition (composition parseRealizer marginListsRealizer)
    tableRealizer) printMatrixRealizer).congr (fun _ => rfl)

/-- One fixed program parses dimensions, computes all greedy cells and
prints the public binary matrix representation in polynomial bit time. -/
theorem polynomial_publicGreedy : PolynomialTime publicGreedyRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_parse polynomial_marginLists)
      polynomial_table) polynomial_printMatrix)

lemma natWords_fold (ns tail : List ℕ) :
    (ns.flatMap encodeNat).foldr (fun a ns => numStep (a,ns)) tail=ns++tail := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.flatMap_cons,List.foldr_append,ih,encodeNat_fold,List.cons_append]

lemma parse_natWords (ns : List ℕ) : parse (ns.flatMap encodeNat)=ns := by
  simpa only [parse,List.append_nil] using natWords_fold ns []

lemma encodeMargins_natWords {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Algorithms.encodeMargins r c=
      (m::n::(List.ofFn r++List.ofFn c)).flatMap encodeNat := by
  simp only [Algorithms.encodeMargins,List.flatMap_cons,List.flatMap_append]
  simp only [List.ofFn_comp',List.flatMap_def,List.append_assoc]

lemma marginLists_spec (m n : ℕ) (rs cs tail : List ℕ)
    (hr : rs.length=m) (hc : cs.length=n) :
    marginLists (m::n::(rs++cs++tail))=(rs,cs) := by
  simp only [marginLists,List.headD_cons,List.tail_cons]
  rw [←hr,←hc]
  simp only [List.append_assoc,List.take_left,List.drop_left]

lemma printMatrix_ofFn {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    printMatrix (List.ofFn (fun i => List.ofFn (X i)))=Algorithms.encodeMatrix X := by
  simp only [printMatrix,Algorithms.encodeMatrix,List.flatMap_def,List.ofFn_comp',List.map_map,
    Function.comp_def]

/-- The actual parser/program/printer computes the mathematically proved
initializer on the exact public input encoding. -/
theorem publicGreedy_spec {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    publicGreedy (Algorithms.encodeMargins r c)=Algorithms.encodeMatrix (matrix r c) := by
  unfold publicGreedy
  rw [encodeMargins_natWords,parse_natWords]
  have hm := marginLists_spec m n (List.ofFn r) (List.ofFn c) []
    (List.length_ofFn) (List.length_ofFn)
  simp only [List.append_nil] at hm
  rw [hm]
  dsimp only
  rw [listMatrix_ofFn,printMatrix_ofFn]

/-- Extra encoded parameters after the margins do not change initialization. -/
lemma publicGreedy_suffix {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (ns : List ℕ) :
    publicGreedy (Algorithms.encodeMargins r c++ns.flatMap encodeNat)=
      Algorithms.encodeMatrix (matrix r c) := by
  unfold publicGreedy
  rw [encodeMargins_natWords,←List.flatMap_append,parse_natWords]
  have hm := marginLists_spec m n (List.ofFn r) (List.ofFn c) ns
    List.length_ofFn List.length_ofFn
  simp only [List.append_assoc] at hm
  simp only [List.cons_append,List.append_assoc]
  rw [hm]
  dsimp only
  rw [listMatrix_ofFn,printMatrix_ofFn]

lemma publicGreedy_sampling {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (k : ℕ) :
    publicGreedy (Algorithms.encodeSamplingInput r c k)=Algorithms.encodeMatrix (matrix r c) := by
  simpa only [Algorithms.encodeSamplingInput,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    using publicGreedy_suffix r c [k]

end ContingencyTables.GreedyFeasibleTable

end OAI
