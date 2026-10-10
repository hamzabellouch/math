import OAI.Combinatorics.ContingencyTables.Sampling.GreedyPublicProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseMatrixLayoutProgram
import OAI.Combinatorics.ContingencyTables.Transport.NetworkVertexCode

namespace OAI

/-! # Parsing the public cell-bounded counting input

Dimensions only delimit bounded list slices. The matrix layout uses the
lengths of the parsed margin lists, so malformed headers do not create
unbounded numeric loops. Positive rational parameters use their natural
numerator and denominator, exactly as in the public tape encoding.
-/

namespace ContingencyTables.CountingInputParser
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralParse
open MatchingFPRAS.TreeFraction DensePrograms

abbrev Input := NetworkVertexCode.Input × (Fraction × Fraction)

def offset (ns : List ℕ) : ℕ := 2+ns.headD 0+ns.tail.headD 0

def offsetRealizer : Realizer offset :=
  composition (pair (composition (pair (constant 2) (head 0)) add)
    (composition tail (head 0))) add
lemma polynomial_offset : PolynomialTime offsetRealizer := by
  unfold offsetRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 2) (polynomial_head 0))
      polynomial_add)
    (polynomial_composition polynomial_tail (polynomial_head 0))) polynomial_add

def rest (ns : List ℕ) : List ℕ := ns.drop (offset ns)
def restRealizer : Realizer rest := composition (pair identity offsetRealizer) dropFast
lemma polynomial_rest : PolynomialTime restRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_offset) polynomial_dropFast

def cells (ns : List ℕ) : ℕ :=
  (GreedyFeasibleTable.marginLists ns).1.length*(GreedyFeasibleTable.marginLists ns).2.length
def cellsRealizer : Realizer cells :=
  composition (pair (composition (composition GreedyFeasibleTable.marginListsRealizer first) listLength)
    (composition (composition GreedyFeasibleTable.marginListsRealizer second) listLength)) multiply
lemma polynomial_cells : PolynomialTime cellsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition GreedyFeasibleTable.polynomial_marginLists
      polynomial_first) polynomial_listLength)
    (polynomial_composition (polynomial_composition GreedyFeasibleTable.polynomial_marginLists
      polynomial_second) polynomial_listLength)) polynomial_multiply

def capacityFrame (ns : List ℕ) : GridFlatData :=
  ((0::(GreedyFeasibleTable.marginLists ns).1,0::(GreedyFeasibleTable.marginLists ns).2),
    (rest ns).take (cells ns))
def capacityFrameRealizer : Realizer capacityFrame :=
  pair (pair
    (composition (f := fun ns : List ℕ => (0,(GreedyFeasibleTable.marginLists ns).1))
      (g := fun z : ℕ×List ℕ => z.1::z.2)
      (pair (constant 0) (composition GreedyFeasibleTable.marginListsRealizer first)) listCons)
    (composition (f := fun ns : List ℕ => (0,(GreedyFeasibleTable.marginLists ns).2))
      (g := fun z : ℕ×List ℕ => z.1::z.2)
      (pair (constant 0) (composition GreedyFeasibleTable.marginListsRealizer second)) listCons))
    (composition (pair restRealizer cellsRealizer) takeFast)
lemma polynomial_capacityFrame : PolynomialTime capacityFrameRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant (0:ℕ))
      (polynomial_composition GreedyFeasibleTable.polynomial_marginLists polynomial_first)) polynomial_listCons)
    (polynomial_composition (polynomial_pair (polynomial_constant (0:ℕ))
      (polynomial_composition GreedyFeasibleTable.polynomial_marginLists polynomial_second)) polynomial_listCons))
    (polynomial_composition (polynomial_pair polynomial_rest polynomial_cells) polynomial_takeFast)

def parameters (ns : List ℕ) : List ℕ := (rest ns).drop (cells ns)
def parametersRealizer : Realizer parameters :=
  composition (pair restRealizer cellsRealizer) dropFast
lemma polynomial_parameters : PolynomialTime parametersRealizer :=
  polynomial_composition (polynomial_pair polynomial_rest polynomial_cells) polynomial_dropFast

def fractionPair (ns : List ℕ) : Fraction × Fraction :=
  ((ns.headD 0,ns.tail.headD 1),(ns.tail.tail.headD 0,ns.tail.tail.tail.headD 1))
def fractionPairRealizer : Realizer fractionPair :=
  pair (pair (head 0) (composition tail (head 1)))
    (pair (composition (composition tail tail) (head 0))
      (composition (composition (composition tail tail) tail) (head 1)))
lemma polynomial_fractionPair : PolynomialTime fractionPairRealizer := by
  unfold fractionPairRealizer
  exact polynomial_pair (polynomial_pair (polynomial_head 0)
    (polynomial_composition polynomial_tail (polynomial_head 1)))
    (polynomial_pair (polynomial_composition (polynomial_composition polynomial_tail polynomial_tail)
      (polynomial_head 0))
      (polynomial_composition (polynomial_composition (polynomial_composition polynomial_tail polynomial_tail)
        polynomial_tail) (polynomial_head 1)))

def decode (ns : List ℕ) : Input :=
  ((GreedyFeasibleTable.marginLists ns,unflattenGrid (capacityFrame ns)),fractionPair (parameters ns))
def decodeRealizer : Realizer decode :=
  pair (pair GreedyFeasibleTable.marginListsRealizer
    (composition (f := capacityFrame) (g := unflattenGrid) capacityFrameRealizer unflattenGridRealizer))
    (composition (f := parameters) (g := fractionPair) parametersRealizer fractionPairRealizer)
lemma polynomial_decode : PolynomialTime decodeRealizer :=
  polynomial_pair (polynomial_pair GreedyFeasibleTable.polynomial_marginLists
    (polynomial_composition polynomial_capacityFrame polynomial_unflattenGrid))
    (polynomial_composition polynomial_parameters polynomial_fractionPair)

def parseInput (as : List Symbol) : Input := decode (parse as)
def publicRealizer : Realizer parseInput :=
  composition (f := parse) (g := decode) parseRealizer decodeRealizer
lemma polynomial_public : PolynomialTime publicRealizer :=
  polynomial_composition polynomial_parse polynomial_decode

lemma decode_blocks (rs cs flat tail : List ℕ) (hf : flat.length=rs.length*cs.length) :
    decode (rs.length::cs.length::(rs++cs++flat++tail))=
      (( (rs,cs),unflattenGrid ((0::rs,0::cs),flat)),fractionPair tail) := by
  have hm := GreedyFeasibleTable.marginLists_spec rs.length cs.length rs cs (flat++tail) rfl rfl
  have hr : rest (rs.length::cs.length::(rs++cs++flat++tail))=flat++tail := by
    simp only [rest,offset,List.headD_cons,List.tail_cons]
    rw [show 2+rs.length+cs.length=(rs.length+cs.length)+1+1 by omega]
    simp only [List.drop_succ_cons,List.append_assoc]
    rw [←List.drop_drop,List.drop_left,List.drop_left]
  have hc : cells (rs.length::cs.length::(rs++cs++flat++tail))=flat.length := by
    unfold cells
    rw [show rs++cs++flat++tail=rs++cs++(flat++tail) by simp only [List.append_assoc],hm]
    exact hf.symm
  simp only [decode,capacityFrame,parameters]
  rw [show rs++cs++flat++tail=rs++cs++(flat++tail) by simp only [List.append_assoc],hm]
  rw [←show rs++cs++flat++tail=rs++cs++(flat++tail) by simp only [List.append_assoc]]
  rw [hr,hc,List.take_left,List.drop_left]

lemma encodeMatrix_words {m n : ℕ} (b : Fin m→Fin n→ℕ) :
    Algorithms.encodeMatrix b=
      (List.ofFn (fun i => List.ofFn (b i))).flatten.flatMap encodeNat := by
  rw [←GreedyFeasibleTable.printMatrix_ofFn]
  unfold GreedyFeasibleTable.printMatrix
  generalize List.ofFn (fun i => List.ofFn (b i))=rows
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.flatMap_cons,List.flatten_cons,List.flatMap_append,ih]

lemma parse_public {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    parse (Algorithms.encodeCountingInput r c b epsilon delta)=
      m::n::(List.ofFn r++List.ofFn c++
        (List.ofFn (fun i => List.ofFn (b i))).flatten++
          [epsilon.num.natAbs,epsilon.den,delta.num.natAbs,delta.den]) := by
  unfold Algorithms.encodeCountingInput parse
  rw [GreedyFeasibleTable.encodeMargins_natWords,encodeMatrix_words]
  simp only [List.foldr_append,encodeRat_fold]
  rw [GreedyFeasibleTable.natWords_fold,GreedyFeasibleTable.natWords_fold]
  simp only [List.cons_append,List.append_assoc]

lemma public_spec {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    parseInput (Algorithms.encodeCountingInput r c b epsilon delta)=
      (NetworkVertexCode.data r c b,(TreeFraction.repr epsilon,TreeFraction.repr delta)) := by
  unfold parseInput
  rw [parse_public]
  have hf : (List.ofFn (fun i => List.ofFn (b i))).flatten.length=
      (List.ofFn r).length*(List.ofFn c).length := by
    simp only [List.length_flatten,List.map_ofFn,Function.comp_def,List.length_ofFn,
      List.sum_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hh := decode_blocks (List.ofFn r) (List.ofFn c)
    (List.ofFn (fun i => List.ofFn (b i))).flatten
    [epsilon.num.natAbs,epsilon.den,delta.num.natAbs,delta.den] hf
  simp only [List.length_ofFn] at hh
  rw [hh]
  change (( (List.ofFn r,List.ofFn c),_),_)=( ( (List.ofFn r,List.ofFn c),_),_)
  congr 2
  let f : Fin (m*n)→ℕ := fun k => b (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have he : (List.ofFn (fun i => List.ofFn (b i))).flatten=List.ofFn f := by
    simpa only [f,Equiv.symm_apply_apply,matrixCode] using flatten_matrixCode f
  rw [he]
  simpa only [marginCode,f,Equiv.symm_apply_apply,matrixCode,ResidualGraphProgram.natCode,Option.elim_none,Option.elim_some]
    using unflattenGrid_code (fun i : Option (Fin m) => i.elim 0 r)
      (fun j : Option (Fin n) => j.elim 0 c) f

end ContingencyTables.CountingInputParser

end OAI
