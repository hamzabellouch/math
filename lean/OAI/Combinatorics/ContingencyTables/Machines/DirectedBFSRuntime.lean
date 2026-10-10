import OAI.Combinatorics.ContingencyTables.Transport.DirectedBFSBounds
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialGrid

namespace OAI

/-! # Polynomial binary execution of the entire materialized BFS -/

namespace ContingencyTables.DirectedBFSRuntime

open MatchingFPRAS.TreeTyped Polynomial DirectedBFSCode DirectedBFSBounds DirectedBFSProgram

def advance (z : ℕ×Context) : Context := (z.2.1,round z.2.1 z.2.2)
def advanceRealizer : Realizer advance :=
  pair (composition second first) (composition second roundRealizer)

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition polynomial_second polynomial_round)

lemma fold_eq (steps : List ℕ) (g : Graph) (P : Store) :
    steps.foldl (fun s i=>advance (i,s)) (g,P)=
      (g,steps.foldl (fun P _=>round g P) P) := by
  induction steps generalizing P with
  | nil => rfl
  | cons i steps ih => exact ih (round g P)

theorem polynomial_fold : PolynomialTime (MatchingFPRAS.TreeTyped.fold advanceRealizer) := by
  apply MatchingFPRAS.TreeTyped.polynomial_fold polynomial_advance (20*(X+1)^3)
  intro steps s pre post he
  let S := weight (steps,s)
  have hsw : weight s≤ S := weight_snd (steps,s)
  have hgw : weight s.1≤ S := (weight_fst s).trans hsw
  have hpw : weight s.2≤ S := (weight_snd s).trans hsw
  have hn : s.1.length≤ S := (list_length_le_weight s.1).trans hgw
  have hpn : s.2.length≤ S := (list_length_le_weight s.2).trans hpw
  have hpre : pre.length≤ S := by
    have hl : pre.length≤ steps.length := by rw [he,List.length_append]; omega
    exact hl.trans ((list_length_le_weight steps).trans (weight_fst (steps,s)))
  have hb : Bounded s.2 (S+5) := by
    intro o ho
    exact (weight_mem ho).trans (hpw.trans (by omega))
  let out := pre.foldl (fun P _=>round s.1 P) s.2
  have ho : Bounded out (S+5+pre.length*(4*s.1.length+2)) :=
    fold_bounded s.1 s.2 (S+5) (by omega) hb pre
  have hol : out.length≤ S := (fold_length_le s.1 s.2 pre).trans
    (max_le hpn hn)
  have hob : S+5+pre.length*(4*s.1.length+2)≤4*S^2+3*S+5 := by
    have hm := Nat.mul_le_mul hpre (show 4*s.1.length+2≤4*S+2 by omega)
    nlinarith
  have hwo := store_weight out _ ho
  have hwm := Nat.mul_le_mul hol (Nat.add_le_add_right hob 1)
  have hwout : weight out≤4*S^3+3*S^2+6*S+1 := by nlinarith
  change weight (pre.foldl (fun s i=>advance (i,s)) s)≤_
  have hf := fold_eq pre s.1 s.2
  rw [Prod.eta] at hf
  rw [hf,weight_prod]
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change 1+weight s.1+weight out≤20*(S+1)^3
  nlinarith

def initialRow (z : ℕ×ℕ) : Option (List ℕ) :=
  if z.2=z.1 then Option.some [z.1] else none

def initialRowRealizer : Realizer initialRow :=
  (choose (composition (pair second first) natEqual)
    (composition (composition (pair first (constant [])) listCons) some)
    (constant none)).congr (by
      intro z
      simp only [Function.comp_apply,initialRow,decide_eq_true_eq])

lemma polynomial_initialRow : PolynomialTime initialRowRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_natEqual)
    (polynomial_composition (polynomial_composition
      (polynomial_pair polynomial_first (polynomial_constant [])) polynomial_listCons) polynomial_some)
    (polynomial_constant none))

def initialInput (z : Graph×ℕ) : Store := initial z.1 z.2
def initialRealizer : Realizer initialInput :=
  composition (pair second (composition first indicesRealizer)) (mapWith initialRowRealizer)

lemma polynomial_initial : PolynomialTime initialRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_mapWith polynomial_initialRow)

def prepare (z : Graph×ℕ) : List ℕ×Context :=
  (indices z.1,(z.1,initial z.1 z.2))
def prepareRealizer : Realizer prepare :=
  pair (composition (f := fun z : Graph×ℕ=>z.1) (g := indices) first indicesRealizer)
    (pair first initialRealizer)

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_indices)
    (polynomial_pair polynomial_first polynomial_initial)

def runInput (z : Graph×ℕ) : Store := run z.1 z.2
def runRealizer : Realizer runInput :=
  (composition (composition prepareRealizer (MatchingFPRAS.TreeTyped.fold advanceRealizer))
    second).congr (by
      intro z
      change ((indices z.1).foldl (fun s i=>advance (i,s)) (z.1,initial z.1 z.2)).2 = _
      rw [fold_eq]
      rfl)

theorem polynomial_run : PolynomialTime runRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_composition polynomial_prepare polynomial_fold) polynomial_second)

def searchInput (z : (Graph×ℕ)×ℕ) : Option (List ℕ) := search z.1.1 z.1.2 z.2
def searchRealizer : Realizer searchInput :=
  composition (pair (composition first runRealizer) second) lookupRealizer

theorem polynomial_search : PolynomialTime searchRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_run) polynomial_second) polynomial_lookup

end ContingencyTables.DirectedBFSRuntime

end OAI
