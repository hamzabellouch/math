import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeListMore
import OAI.Combinatorics.MatchingCount.Tapes.Parse

namespace OAI

namespace MatchingFPRAS.LiteralInput
open TreeTyped TreeFunction Polynomial LiteralParse

abbrev PairState := (Bool×ℕ)×List (ℕ×ℕ)
def pairStep (x : ℕ×PairState) : PairState :=
  if x.2.1.1 then ((false,0),(x.1,x.2.1.2)::x.2.2) else ((true,x.1),x.2.2)
def pairStepRealizer : Realizer pairStep :=
  (choose second.fst.fst
    (pair (constant (false,0)) (composition (pair (pair first second.fst.snd) second.snd) listCons))
    (pair (pair (constant true) first) second.snd)).congr (by
      intro x;simp only [Function.comp_apply,pairStep])
lemma polynomial_pairStep : PolynomialTime pairStepRealizer := by
  unfold pairStepRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst,Realizer.snd]
  tree_cost
lemma pairStep_weight (n : ℕ) (s : PairState) : weight (pairStep (n,s)) ≤ weight s+weight n+4 := by
  rcases s with ⟨⟨b,m⟩,es⟩
  cases b
  · change weight ((true,n),es) ≤ weight ((false,m),es)+weight n+4
    simp only [weight_prod]
    change 1+(1+3+weight n)+weight es ≤ 1+(1+1+weight m)+weight es+weight n+4
    omega
  · change weight ((false,0),(n,m)::es) ≤ weight ((true,m),es)+weight n+4
    simp only [weight_prod,weight_cons]
    change 1+(1+1+1)+(1+(1+weight n+weight m)+weight es) ≤
      1+(1+3+weight m)+weight es+weight n+4
    omega
lemma pairFold_weight (ns : List ℕ) (s : PairState) :
    weight (ns.foldl (fun s n=>pairStep (n,s)) s) ≤ weight s+5*weight ns := by
  induction ns generalizing s with
  | nil => simp
  | cons n ns ih =>
    have h := ih (pairStep (n,s))
    have h' := pairStep_weight n s
    simp only [List.foldl_cons,weight_cons]
    omega
lemma polynomial_pairFold : PolynomialTime (fold pairStepRealizer) := by
  apply polynomial_fold polynomial_pairStep (6*X)
  intro as s pre post he
  have h := pairFold_weight pre s
  have hw : weight pre ≤ weight as := by
    have ha := weight_append pre post
    have hp := weight_pos post
    rw [he]
    omega
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega

def pairs (ns : List ℕ) : List (ℕ×ℕ) := (ns.foldl (fun s n=>pairStep (n,s)) ((false,0),[])).2
def pairsRealizer : Realizer pairs :=
  (composition
    (composition (pair identity (constant (((false,0),[]) : PairState))) (fold pairStepRealizer)) second).congr (fun _=>rfl)
lemma polynomial_pairs : PolynomialTime pairsRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant _))
    polynomial_pairFold) polynomial_second)
lemma pair_pair (i j : ℕ) (es : List (ℕ×ℕ)) :
    pairStep (i,pairStep (j,((false,0),es)))=((false,0),(i,j)::es) := rfl
lemma pairs_reverse (es : List (ℕ×ℕ)) (acc : List (ℕ×ℕ)) :
    ((es.flatMap (fun e=>[e.1,e.2])).reverse.foldl (fun s n=>pairStep (n,s)) ((false,0),acc))=
      ((false,0),es++acc) := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.singleton_append,List.foldl_append,ih,List.foldl_cons,List.foldl_nil,pair_pair]
    rfl

abbrev Parsed := ℕ×(List (ℕ×ℕ)×(TreeFraction.Fraction×TreeFraction.Fraction))
def ratTail (ns : List ℕ) : TreeFraction.Fraction×TreeFraction.Fraction :=
  ((ns.tail.tail.tail.headD 0,ns.tail.tail.headD 0),(ns.tail.headD 0,ns.headD 0))
def ratTailRealizer : Realizer ratTail :=
  pair (pair (composition (composition (composition tail tail) tail) (head 0))
    (composition (composition tail tail) (head 0)))
    (pair (composition tail (head 0)) (head 0))
lemma polynomial_ratTail : PolynomialTime ratTailRealizer := by
  unfold ratTailRealizer
  exact TreeTyped.polynomial_pair
    (TreeTyped.polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition polynomial_tail polynomial_tail)
        polynomial_tail) (polynomial_head _))
      (polynomial_composition (polynomial_composition polynomial_tail polynomial_tail) (polynomial_head _)))
    (TreeTyped.polynomial_pair (polynomial_composition polynomial_tail (polynomial_head _)) (polynomial_head _))

def fromNumbers (ns : List ℕ) : Parsed :=
  (ns.headD 0,(pairs ns.tail.tail.reverse.tail.tail.tail.tail,ratTail ns.tail.tail.reverse))
def reversedTailRealizer : Realizer (fun ns : List ℕ=>ns.tail.tail.reverse) :=
  composition (composition tail tail) reverse
def fromNumbersRealizer : Realizer fromNumbers :=
  (pair (head 0) (pair
    (composition (composition (composition (composition (composition reversedTailRealizer tail) tail) tail) tail) pairsRealizer)
    (composition reversedTailRealizer ratTailRealizer))).congr (fun _=>rfl)
lemma polynomial_reversedTail : PolynomialTime reversedTailRealizer :=
  polynomial_composition (polynomial_composition polynomial_tail polynomial_tail) polynomial_reverse
lemma polynomial_fromNumbers : PolynomialTime fromNumbersRealizer := by
  unfold fromNumbersRealizer
  apply polynomial_congr
  apply polynomial_pair (polynomial_head _)
  apply polynomial_pair
  · exact polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_reversedTail polynomial_tail) polynomial_tail)
        polynomial_tail) polynomial_tail) polynomial_pairs
  · exact polynomial_composition polynomial_reversedTail polynomial_ratTail

def parseInput (as : List Symbol) : Parsed := fromNumbers (LiteralParse.parse as)
def parseInputRealizer : Realizer parseInput := composition LiteralParse.parseRealizer fromNumbersRealizer
lemma polynomial_parseInput : PolynomialTime parseInputRealizer :=
  polynomial_composition LiteralParse.polynomial_parse polynomial_fromNumbers

def edgeNumbers (G : GraphInput) : List (ℕ×ℕ) :=
  ((G.edges.map toLex.toEmbedding).sort (·≤·)).map (fun e=>((ofLex e).1.val,(ofLex e).2.val))
lemma edges_fold (es : List (ℕ×ℕ)) (ns : List ℕ) :
    (es.flatMap (fun e=>encodeNat e.1++encodeNat e.2)).foldr (fun a ns=>numStep (a,ns)) ns=
      es.flatMap (fun e=>[e.1,e.2])++ns := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.foldr_append,ih,encodeNat_fold]
    rfl
lemma parse_source (G : GraphInput) (ε δ : ℚ) : LiteralParse.parse (encodeInput G ε δ)=
    G.n::G.edges.card::(edgeNumbers G).flatMap (fun e=>[e.1,e.2])++[ε.num.natAbs,ε.den,δ.num.natAbs,δ.den] := by
  unfold encodeInput LiteralParse.parse
  simp only [List.foldr_append,encodeNat_fold,encodeRat_fold]
  rw [show (((G.edges.map toLex.toEmbedding).sort (·≤·)).flatMap fun e=>encodeNat (ofLex e).1.val++encodeNat (ofLex e).2.val)=
    (edgeNumbers G).flatMap (fun e=>encodeNat e.1++encodeNat e.2) by simp only [edgeNumbers,List.flatMap_map]]
  rw [edges_fold]
  rfl
lemma parseInput_source (G : GraphInput) (ε δ : ℚ) :
    parseInput (encodeInput G ε δ)=(G.n,(edgeNumbers G,(TreeFraction.repr ε,TreeFraction.repr δ))) := by
  rw [parseInput,parse_source]
  unfold fromNumbers
  simp only [List.cons_append,List.headD_cons,List.tail_cons,
    List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append]
  unfold ratTail
  simp only [List.headD_cons,List.tail_cons]
  unfold pairs
  rw [pairs_reverse]
  simp only [List.append_nil]
  rfl
end MatchingFPRAS.LiteralInput

end OAI
