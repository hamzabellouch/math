import OAI.Combinatorics.ContingencyTables.Rooted.ForestJoinProgram
import OAI.Combinatorics.ContingencyTables.Rooted.LargeEdgeCatalogProgram

namespace OAI

/-! # Polynomial execution of the component-greedy forest loop

The immutable weighted edge catalog is scanned after every insertion.
There are at most the square of the stored vertex count many iterations;
all adjacency rows stay inside that fixed vertex range.
-/

namespace ContingencyTables.ForestGreedyProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram WeightedArgmaxProgram

abbrev State := ForestEdgeChoiceProgram.Input

private def insert (z : State×Edge) : GraphCode := ForestJoinProgram.join (z.1.1,z.2.1)
private def insertRealizer : Realizer insert :=
  composition (f := fun z : State×Edge=>(z.1.1,z.2.1)) (g := ForestJoinProgram.join)
    (pair (composition first first) (composition second first)) ForestJoinProgram.joinRealizer
private lemma polynomial_insert : PolynomialTime insertRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_second polynomial_first)) ForestJoinProgram.polynomial_join

def update (s : State) : GraphCode :=
  (ForestEdgeChoiceProgram.choice s).elim s.1 (fun e=>insert (s,e))
def updateRealizer : Realizer update :=
  composition (f := fun s : State=>(s,ForestEdgeChoiceProgram.choice s))
    (g := fun z : State×Option Edge=>z.2.elim z.1.1 (fun e=>insert (z.1,e)))
    (pair identity ForestEdgeChoiceProgram.choiceRealizer) (optionCases first insertRealizer)
lemma polynomial_update : PolynomialTime updateRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity ForestEdgeChoiceProgram.polynomial_choice)
    (polynomial_optionCases polynomial_first polynomial_insert)

def advance (z : ℕ×State) : State := (update z.2,z.2.2)
def advanceRealizer : Realizer advance :=
  pair (composition (f := fun z : ℕ×State=>z.2) (g := update) second updateRealizer)
    (composition second second)
lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_update)
    (polynomial_composition polynomial_second polynomial_second)

lemma update_length (s : State) : (update s).length=s.1.length := by
  unfold update
  cases h : ForestEdgeChoiceProgram.choice s with
  | none=>rfl
  | some e=>exact ForestJoinProgram.join_length _

lemma update_weight (s : State) :
    weight (update s)≤ max (weight s.1)
      (s.1.length*(4*s.1.length^2+2*s.1.length+2)+1) := by
  unfold update
  cases h : ForestEdgeChoiceProgram.choice s with
  | none=>exact le_max_left _ _
  | some e=>exact (ForestJoinProgram.join_weight _).trans (le_max_right _ _)

lemma fold_edges (xs : List ℕ) (s : State) :
    (xs.foldl (fun s a=>advance (a,s)) s).2=s.2 := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>exact ih (advance (a,s))

lemma fold_length (xs : List ℕ) (s : State) :
    (xs.foldl (fun s a=>advance (a,s)) s).1.length=s.1.length := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>
    exact (ih (advance (a,s))).trans (update_length s)

lemma fold_weight (xs : List ℕ) (s : State) :
    weight (xs.foldl (fun s a=>advance (a,s)) s).1≤ max (weight s.1)
      (s.1.length*(4*s.1.length^2+2*s.1.length+2)+1) := by
  induction xs generalizing s with
  | nil=>exact le_max_left _ _
  | cons a xs ih=>
    have h := ih (advance (a,s))
    simp only [advance,update_length] at h
    exact h.trans (max_le (update_weight s) (le_max_right _ _))

lemma polynomial_loop : PolynomialTime (fold advanceRealizer) := by
  apply polynomial_fold polynomial_advance (30*(X+1)^3)
  intro xs s pre post he
  let S := weight (xs,s)
  let out := pre.foldl (fun s a=>advance (a,s)) s
  have hs : weight s≤S := weight_snd (xs,s)
  have hg : weight s.1≤S := (weight_fst s).trans hs
  have hec : weight s.2≤S := (weight_snd s).trans hs
  have hn : s.1.length≤S := (list_length_le_weight s.1).trans hg
  have hb : s.1.length*(4*s.1.length^2+2*s.1.length+2)+1≤4*S^3+2*S^2+2*S+1 := by
    have hpow := Nat.pow_le_pow_left hn 2
    have hmul := Nat.mul_le_mul hn (show 4*s.1.length^2+2*s.1.length+2≤4*S^2+2*S+2 by omega)
    nlinarith
  have ho : weight out.1≤4*S^3+2*S^2+3*S+1 :=
    (fold_weight pre s).trans (max_le (by omega) (by omega))
  have heq : out.2=s.2 := fold_edges pre s
  have hw : weight out=1+weight out.1+weight out.2 := by
    change weight (out.1,out.2)=_
    exact weight_prod _ _
  simp only [eval_mul,eval_ofNat,eval_add,eval_pow,eval_X,eval_one]
  change weight out≤30*(S+1)^3
  rw [hw,heq]
  nlinarith

def slots (s : State) : List ℕ := List.range (s.1.length*s.1.length)
def slotsRealizer : Realizer slots :=
  composition (f := fun s : State=>s.1.length*s.1.length) (g := List.range)
    (composition (f := fun s : State=>(s.1.length,s.1.length))
      (g := fun z : ℕ×ℕ=>z.1*z.2)
      (pair (composition first listLength) (composition first listLength)) multiply) range
lemma polynomial_slots : PolynomialTime slotsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_listLength)
      (polynomial_composition polynomial_first polynomial_listLength)) polynomial_multiply) (X^2)
  intro s
  have h : s.1.length≤weight s := (list_length_le_weight s.1).trans (weight_fst s)
  simpa only [Function.comp_apply,eval_pow,eval_mul,eval_X,pow_two] using Nat.mul_self_le_mul_self h

def execute (s : State) : State := (slots s).foldl (fun s a=>advance (a,s)) s
def executeRealizer : Realizer execute :=
  composition (f := fun s : State=>(slots s,s))
    (g := fun z : List ℕ×State=>z.1.foldl (fun s a=>advance (a,s)) z.2)
    (pair slotsRealizer identity) (fold advanceRealizer)
lemma polynomial_execute : PolynomialTime executeRealizer :=
  polynomial_composition (polynomial_pair polynomial_slots polynomial_identity) polynomial_loop

def emptyGraph (z : LargeEdgeCatalogProgram.Input) : GraphCode :=
  (List.range (LargeEdgeCatalogProgram.vertexCount z)).map (fun _=>[])
def emptyGraphRealizer : Realizer emptyGraph :=
  composition (composition LargeEdgeCatalogProgram.vertexCountRealizer range) (map (constant []))
lemma polynomial_emptyGraph : PolynomialTime emptyGraphRealizer := by
  apply polynomial_composition
  · apply polynomial_boundedRange LargeEdgeCatalogProgram.polynomial_vertexCount (2*X)
    intro z
    have hr : z.1.1.1.length≤weight z := (list_length_le_weight z.1.1.1).trans
      ((weight_fst z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))
    have hc : z.1.1.2.length≤weight z := (list_length_le_weight z.1.1.2).trans
      ((weight_snd z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))
    simp only [LargeEdgeCatalogProgram.vertexCount,eval_mul,eval_ofNat,eval_X]
    omega
  · exact polynomial_map (polynomial_constant [])

def prepare (z : LargeEdgeCatalogProgram.Input) : State :=
  (emptyGraph z,LargeEdgeCatalogProgram.catalog z)
def prepareRealizer : Realizer prepare :=
  pair emptyGraphRealizer LargeEdgeCatalogProgram.catalogRealizer
lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair polynomial_emptyGraph LargeEdgeCatalogProgram.polynomial_catalog

def forest (z : LargeEdgeCatalogProgram.Input) : GraphCode := (execute (prepare z)).1
def forestRealizer : Realizer forest :=
  composition (composition (f:=prepare) (g:=execute) prepareRealizer executeRealizer) first
lemma polynomial_forest : PolynomialTime forestRealizer :=
  polynomial_composition (polynomial_composition polynomial_prepare polynomial_execute) polynomial_first

end ContingencyTables.ForestGreedyProgram

end OAI
