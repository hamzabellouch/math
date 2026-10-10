import OAI.Computability.Scheduling.ProgramRoutines

namespace OAI

universe u1 u2

section

namespace ThreeMachine.StackCompiler
open ThreeMachine.Structure ThreeMachine.Algorithm
namespace Uniform

variable {I : Type u1} {α : I → Type} [∀ i, Coding (α i)]

def natLT : Uniform (fun (_ : I) (x : ℕ × ℕ) => decide (x.1 < x.2)) :=
  (swap.comp ((Realizer.le.uniform I).comp (Realizer.not.uniform I))).congr (fun _ x => by
    by_cases h : x.1 < x.2
    · have hn : ¬ x.2 ≤ x.1 := by omega
      simp [Function.comp_apply,h,hn]
    · have hn : x.2 ≤ x.1 := by omega
      simp [Function.comp_apply,h,hn])

def finCons (k : ℕ) : Uniform (fun i (x : α i × (Fin k → α i)) => (Fin.cons x.1 x.2 : Fin (k+1) → α i)) :=
  reinterpret _ (fun _ _ => by simp only [enc_function,List.ofFn_cons]; rfl)

def finEmpty : Uniform (fun i (_ : List (α i)) => (Fin.elim0 : Fin 0 → α i)) where
  transform := fun _ => .nil
  charge := _
  routine := Routine.nil
  correct _ _ := by simp only [enc_function,List.ofFn_zero]; rfl

def assignments : (k : ℕ) → Uniform (fun i (xs : List (α i)) => Structure.assignments xs k)
  | 0 => finEmpty.comp singleton
  | k+1 =>
    ((id.pair (assignments k)).comp ((snd.pair fst).comp (swap.comp (finCons k)).map).flatMap).congr
      (fun _ _ => rfl)

def tripleSet : Uniform (fun n (x : Universe n × (Fin n × (Fin n × Fin n))) =>
    ({x.2.1,x.2.2.1,x.2.2.2} : Finset (Fin n))) := by
  let P : Uniform (fun n (x : Fin n × (Fin n × (Fin n × Fin n))) =>
      decide (x.1 = x.2.1 ∨ x.1 = x.2.2.1 ∨ x.1 = x.2.2.2)) :=
    ((fst.pair (snd.comp fst)).comp finEq).orD
      (((fst.pair (snd.comp (snd.comp fst))).comp finEq).orD
        ((fst.pair (snd.comp (snd.comp snd))).comp finEq))
  exact (((fst.comp universeSet).pair snd).comp P.setFilter).congr (fun _ x => by
    ext a; simp only [Function.comp_apply,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq,
      Finset.mem_insert,Finset.mem_singleton])

def triples : Uniform (fun n (_ : Universe n) =>
    (Structure.tripleList (List.finRange n)).map Subtype.val) := by
  let E := (universeList.pair (universeList.pair universeList |>.comp product)).comp product
  let A := (E.pair id).comp (swap.comp tripleSet).map
  let P : Uniform (fun n (x : Finset (Fin n) × Unit) => decide (x.1.card = 3)) :=
    (((fst.comp setCard).pair (constant 3)).comp (Realizer.eqNat.uniform ℕ))
  exact ((A.pair unit).comp P.filter).congr (fun n _ => by
    dsimp only [Function.comp_apply]
    simp only [Structure.tripleList,List.product,List.map_flatMap,List.map_map,List.map_filterMap]
    rw [← List.filterMap_eq_filter]
    congr 1
    funext Z
    by_cases h : Z.card = 3 <;> simp [Option.guard,h])

def predecessorCount : Uniform (fun n (x : Universe n × (Matrix n × Fin n)) =>
    Structure.predecessorCount (matrixRel x.2.1) x.2.2) :=
  ((((fst.comp universeSet).pair snd).comp
    (((snd.comp fst).pair (fst.pair (snd.comp snd))).comp matrixGet).setFilter).comp setCard).congr
      (fun _ _ => rfl)

def predecessors : Uniform (fun n (x : Universe n × Matrix n) =>
    Structure.predecessorCount (matrixRel x.2)) :=
  ((fst.pair id).comp (((snd.comp fst).pair ((snd.comp snd).pair fst)).comp predecessorCount).vectorMap)

def rankFromCounts : Uniform (fun n (x : Universe n × ((Fin n → ℕ) × Fin n)) =>
    (Finset.univ.filter (fun y => x.2.1 y < x.2.1 x.2.2 ∨
      x.2.1 y = x.2.1 x.2.2 ∧ y < x.2.2)).card+1) := by
  let A := (((snd.comp fst).pair fst).comp functionGet :
    Uniform (fun n (x : Fin n × ((Fin n → ℕ) × Fin n)) => x.2.1 x.1))
  let B := (((snd.comp fst).pair (snd.comp snd)).comp functionGet :
    Uniform (fun n (x : Fin n × ((Fin n → ℕ) × Fin n)) => x.2.1 x.2.2))
  let C := ((A.pair B).comp natLT)
  let D := ((A.pair B).comp (Realizer.eqNat.uniform ℕ))
  let E := (((fst.comp finVal).pair ((snd.comp snd).comp finVal)).comp natLT :
    Uniform (fun n (x : Fin n × ((Fin n → ℕ) × Fin n)) => decide (x.1 < x.2.2)))
  exact ((((fst.comp universeSet).pair snd).comp (C.orD (D.andD E)).setFilter).comp setCard).comp
    (Realizer.succ.uniform ℕ) |>.congr (fun _ _ => by
      simp only [Function.comp_apply,decide_eq_true_eq,Fin.lt_def])

def rank : Uniform (fun n (x : Universe n × Matrix n) => Structure.jobRank (matrixRel x.2)) :=
  ((fst.pair (fst.pair predecessors)).comp
    (((snd.comp fst).pair ((snd.comp snd).pair fst)).comp rankFromCounts).vectorMap).congr (fun _ _ => by
      funext y
      simp only [Function.comp_apply,Structure.jobRank,Structure.rankOfKey,Structure.jobKey,
        Prod.Lex.toLex_lt_toLex])

def reverseRank : Uniform (fun n (x : Universe n × (Fin n → ℕ)) => fun v => n+1-x.2 v) :=
  ((fst.pair (((fst.comp universeNumber).comp (Realizer.succ.uniform ℕ)).pair snd)).comp
    (((snd.comp fst).pair (((snd.comp snd).pair fst).comp functionGet)).comp
      (Realizer.sub.uniform ℕ)).vectorMap)

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Structure ThreeMachine.Algorithm

def coneSet {n : ℕ} (M : Matrix n) (frame : Bool) (kind : Fin 5) (Z : Finset (Fin n)) : Finset (Fin n) :=
  let R := fun x y => if frame then matrixRel M y x else matrixRel M x y
  match kind.val with
  | 0 => Z
  | 1 => Finset.univ.filter (fun x => ∃ y ∈ Z, R x y)
  | 2 => Finset.univ.filter (fun x => ∃ y ∈ Z, R y x)
  | 3 => (Finset.univ.filter (fun x => ∃ y ∈ Z, R x y)) ∪ Z
  | _ => (Finset.univ.filter (fun x => ∃ y ∈ Z, R y x)) ∪ Z

theorem atomicCone (n : ℕ) (M : Matrix n) (frame : Bool) (kind : Fin 5)
    (Z : {s : Finset (Fin n) // s.card = 3}) :
    Atomic.finsetEval (matrixRel M) (Structure.jobRank (matrixRel M))
      (Structure.reverseJobRank (matrixRel M)) (.cone frame kind Z) = coneSet M frame kind Z.val := by
  fin_cases kind <;> ext x <;> simp [Atomic.finsetEval,coneSet]

theorem map_finRange_nat {β : Type u2} (f : ℕ → β) (k : ℕ) :
    (List.finRange k).map (fun i => f i.val) = (List.range k).map f := by
  rw [← finRange_val k,List.map_map]
  rfl

theorem atomicThreshold {n : ℕ} (M : Matrix n) (frame upper : Bool) :
    (List.finRange (Fintype.card (Fin n)+2)).map (fun k =>
      Atomic.finsetEval (matrixRel M) (Structure.jobRank (matrixRel M))
        (Structure.reverseJobRank (matrixRel M)) (.threshold frame upper k)) =
    (List.range (n+2)).map (fun k => Finset.univ.filter (fun v => if upper then
      (if frame then Structure.reverseJobRank (matrixRel M) else Structure.jobRank (matrixRel M)) v ≤ k
      else k ≤ (if frame then Structure.reverseJobRank (matrixRel M) else Structure.jobRank (matrixRel M)) v)) := by
  let f : ℕ → Finset (Fin n) := fun k => Finset.univ.filter (fun v => if upper then
      (if frame then Structure.reverseJobRank (matrixRel M) else Structure.jobRank (matrixRel M)) v ≤ k
      else k ≤ (if frame then Structure.reverseJobRank (matrixRel M) else Structure.jobRank (matrixRel M)) v)
  change (List.finRange (Fintype.card (Fin n)+2)).map (fun k => f k.val) = (List.range (n+2)).map f
  rw [map_finRange_nat,Fintype.card_fin]

namespace Uniform

def thresholdSets (upper : Bool) : Uniform (fun n (x : Universe n × (Fin n → ℕ)) =>
    (List.range (n+2)).map (fun k => Finset.univ.filter
      (fun v => if upper then x.2 v ≤ k else k ≤ x.2 v))) := by
  let N : Uniform (fun n (_ : Universe n × (Fin n → ℕ)) => List.range (n+2)) := (((fst.comp universeNumber).pair (constant 2)).comp (Realizer.add.uniform ℕ)).comp
    (Realizer.range.uniform ℕ)
  let A := (((snd.comp snd).pair fst).comp functionGet :
    Uniform (fun n (x : Fin n × (ℕ × (Fin n → ℕ))) => x.2.2 x.1))
  let B := (snd.comp fst : Uniform (fun n (x : Fin n × (ℕ × (Fin n → ℕ))) => x.2.1))
  let P : Uniform (fun n (x : Fin n × (ℕ × (Fin n → ℕ))) =>
      decide (if upper then x.2.2 x.1 ≤ x.2.1 else x.2.1 ≤ x.2.2 x.1)) := by
    cases upper
    · exact (B.pair A).comp (Realizer.le.uniform ℕ)
    · exact (A.pair B).comp (Realizer.le.uniform ℕ)
  let F := ((((snd.comp fst).comp universeSet).pair (fst.pair (snd.comp snd))).comp P.setFilter :
    Uniform (fun n (x : ℕ × (Universe n × (Fin n → ℕ))) => Finset.univ.filter
      (fun v => decide (if upper then x.2.2 v ≤ x.1 else x.1 ≤ x.2.2 v) = true)))
  exact ((N.pair id).comp F.map).congr (fun _ _ => by
    simp only [Function.comp_apply,decide_eq_true_eq])

def matrixGetFrame (frame : Bool) : Uniform (fun n (x : Matrix n × (Fin n × Fin n)) =>
    decide (if frame then matrixRel x.1 x.2.2 x.2.1 else matrixRel x.1 x.2.1 x.2.2)) := by
  cases frame
  · exact matrixGet.congr (fun _ x => by simp [matrixRel])
  · exact ((fst.pair (snd.comp swap)).comp matrixGet).congr (fun _ x => by
      simp [Function.comp_apply,matrixRel])

def conePred (frame : Bool) : Uniform (fun n (x : Universe n × (Matrix n × Finset (Fin n))) =>
    Finset.univ.filter (fun v => ∃ y ∈ x.2.2,
      if frame then matrixRel x.2.1 y v else matrixRel x.2.1 v y)) := by
  let A := (((snd.comp fst).pair ((snd.comp snd).pair fst)).comp (matrixGetFrame frame) :
    Uniform (fun n (x : Fin n × (Matrix n × Fin n)) =>
      decide (if frame then matrixRel x.2.1 x.1 x.2.2 else matrixRel x.2.1 x.2.2 x.1)))
  let P := (((snd.comp snd).pair ((snd.comp fst).pair fst)).comp A.setAny)
  exact (((fst.comp universeSet).pair snd).comp P.setFilter).congr (fun _ _ => by
    simp only [Function.comp_apply,decide_eq_true_eq])

def cone (frame : Bool) (kind : Fin 5) : Uniform (fun n (x : Universe n × (Matrix n × Finset (Fin n))) =>
    coneSet x.2.1 frame kind x.2.2) := by
  let D : Uniform (fun n (x : Universe n × (Matrix n × Finset (Fin n))) =>
      Finset.univ.filter (fun v => ∃ y ∈ x.2.2,
        if frame then matrixRel x.2.1 v y else matrixRel x.2.1 y v)) :=
    (conePred (!frame)).congr (fun _ x => by cases frame <;> rfl)
  match hk : kind.val with
  | 0 => exact (snd.comp snd).congr (fun _ _ => by simp only [Function.comp_apply,coneSet,hk])
  | 1 => exact (conePred frame).congr (fun _ _ => by simp only [coneSet,hk])
  | 2 => exact D.congr (fun _ _ => by simp only [coneSet,hk])
  | 3 =>
    exact (fst.pair ((conePred frame).pair (snd.comp snd)) |>.comp setUnion).congr
      (fun _ _ => by simp only [Function.comp_apply,coneSet,hk])
  | k+4 =>
    exact (fst.pair (D.pair (snd.comp snd)) |>.comp setUnion).congr
      (fun _ _ => by simp only [Function.comp_apply,coneSet,hk])

def cones (frame : Bool) : (ks : List (Fin 5)) →
    Uniform (fun n (x : Universe n × Matrix n) => ks.flatMap (fun k =>
      ((Structure.tripleList (List.finRange n)).map Subtype.val).map (coneSet x.2 frame k)))
  | [] => nil
  | k :: ks =>
    let F := ((((snd.comp fst).pair ((snd.comp snd).pair fst))).comp (cone frame k))
    (((((fst.comp triples).pair id).comp F.map).pair (cones frame ks)).comp append).congr
      (fun _ _ => rfl)

def ranks (frame : Bool) : Uniform (fun n (x : Universe n × Matrix n) =>
    if frame then Structure.reverseJobRank (matrixRel x.2) else Structure.jobRank (matrixRel x.2)) := by
  cases frame
  · exact rank
  · exact (fst.pair rank).comp reverseRank

def thresholds (frame : Bool) : Uniform (fun n (x : Universe n × Matrix n) =>
    [Bool.false,true].flatMap (fun upper => (List.range (n+2)).map
      (fun k => Finset.univ.filter (fun v => if upper then
        (if frame then Structure.reverseJobRank (matrixRel x.2) else Structure.jobRank (matrixRel x.2)) v ≤ k
        else k ≤ (if frame then Structure.reverseJobRank (matrixRel x.2) else Structure.jobRank (matrixRel x.2)) v)))) :=
  ((fst.pair (ranks frame)).comp ((thresholdSets Bool.false).pair (thresholdSets true) |>.comp append)).congr
    (fun _ _ => by simp only [Function.comp_apply,List.flatMap_cons,List.flatMap_nil,List.append_nil])

def atomSets : Uniform (fun n (x : Universe n × Matrix n) =>
    (Atomic.alphabet (List.finRange n)).map
      (Atomic.finsetEval (matrixRel x.2) (Structure.jobRank (matrixRel x.2)) (Structure.reverseJobRank (matrixRel x.2)))) := by
  let C : Uniform (fun n (_ : Universe n × Matrix n) => [∅, (Finset.univ : Finset (Fin n))]) := (((fst.comp setEmpty).pair (((fst.comp universeSet).pair nil).comp cons)).comp cons)
  let T := ((thresholds Bool.false).pair (thresholds true)).comp append
  let D := ((cones Bool.false (List.finRange 5)).pair (cones true (List.finRange 5))).comp append
  exact ((C.pair T).comp append |>.pair D |>.comp append).congr (fun n x => by
    simp only [Function.comp_apply,Atomic.alphabet,List.map_append,List.map_cons,List.map_nil,
      List.map_flatMap,List.map_map,List.flatMap_cons,List.flatMap_nil,List.append_nil,Function.comp_def]
    simp only [atomicCone,atomicThreshold]
    rfl)

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.Structure

theorem assignments_map {A B : Type} (g : A → B) (xs : List A) (k : ℕ) :
    assignments (xs.map g) k = (assignments xs k).map (fun f => g ∘ f) := by
  induction k with
  | zero => simp only [assignments,List.map_singleton]; congr 1; funext i; exact Fin.elim0 i
  | succ k ih =>
    simp only [assignments,ih,List.flatMap_map,List.map_flatMap,List.map_map]
    apply List.flatMap_congr
    intro a ha
    apply List.map_congr_left
    intro f hf
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem Formula.map_evalFinset {J A B : Type} [Fintype J] [DecidableEq J]
    (g : A → B) (atoms : B → Finset J) (p : Formula A) :
    (p.map g).evalFinset atoms = p.evalFinset (atoms ∘ g) := by
  induction p with
  | leaf a b => rfl
  | conj p q ihp ihq | disj p q ihp ihq => simp only [map,evalFinset,ihp,ihq]

theorem Atomic.filter_eval {J : Type} [Fintype J] [DecidableEq J]
    (r : J → J → Prop) [DecidableRel r] (rank reverseRank : J → ℕ) (a : Atomic J) :
    Finset.univ.filter (eval r rank reverseRank a) = finsetEval r rank reverseRank a := by
  apply Finset.coe_injective
  rw [coe_finsetEval]
  ext x
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x))

theorem effectiveFamily_eq_finset {J : Type} [Fintype J] [DecidableEq J]
    (r : J → J → Prop) [DecidableRel r] (rank reverseRank : J → ℕ) (jobs : List J) (K : ℕ) :
    effectiveFamily r rank reverseRank jobs K =
      (assignments ((Atomic.alphabet jobs).map (Atomic.finsetEval r rank reverseRank)) K).flatMap
        (fun f => (Formula.templates K).map (Formula.evalFinset f)) := by
  simp only [effectiveFamily,Atomic.filter_eval,assignments_map,List.flatMap_map]
  apply List.flatMap_congr
  intro f hf
  apply List.map_congr_left
  intro s hs
  exact Formula.map_evalFinset f _ s

end ThreeMachine.Structure

namespace ThreeMachine.StackCompiler
open ThreeMachine.Structure ThreeMachine.Algorithm
namespace Uniform

def evalTemplate {K : ℕ} : (p : Formula (Fin K)) →
    Uniform (fun n (x : Universe n × (Fin K → Finset (Fin n))) => p.evalFinset x.2)
  | .leaf a b =>
    let A := (snd.pair (constant a)).comp (functionGetAny (fun _ : ℕ => K))
    if hb : b then
      ((fst.pair A).comp setCompl).congr (fun _ _ => by simp [Formula.evalFinset,hb,Function.comp_apply])
    else A.congr (fun _ _ => by simp [Formula.evalFinset,hb,Function.comp_apply])
  | .conj p q => ((evalTemplate p).pair (evalTemplate q)).comp setInter
  | .disj p q => (fst.pair ((evalTemplate p).pair (evalTemplate q))).comp setUnion

def evalTemplates {K : ℕ} : (ps : List (Formula (Fin K))) →
    Uniform (fun n (x : Universe n × (Fin K → Finset (Fin n))) => ps.map (Formula.evalFinset x.2))
  | [] => nil
  | p :: ps => ((evalTemplate p).pair (evalTemplates ps)).comp cons

def family (K : ℕ) : Uniform (fun n (x : Universe n × Matrix n) =>
    effectiveFamily (matrixRel x.2) (Structure.jobRank (matrixRel x.2))
      (Structure.reverseJobRank (matrixRel x.2)) (List.finRange n) K) :=
  ((((atomSets.comp (assignments K)).pair fst).comp (swap.comp (evalTemplates (Formula.templates K))).flatMap)).congr
    (fun _ _ => (effectiveFamily_eq_finset _ _ _ _ _).symm)

def fullSolveK (K : ℕ) : Uniform (fun n (x : Universe n × Matrix n) =>
    Algorithm.lookup (Algorithm.layers (matrixRel x.2)
      (effectiveFamily (matrixRel x.2) (Structure.jobRank (matrixRel x.2))
        (Structure.reverseJobRank (matrixRel x.2)) (List.finRange n) K)
      ((Structure.tripleList (List.finRange n)).map Subtype.val) n) Finset.univ) := by
  let A : Uniform (fun n (x : Universe n × Matrix n) =>
      Algorithm.layers (matrixRel x.2) (effectiveFamily (matrixRel x.2) (Structure.jobRank (matrixRel x.2))
        (Structure.reverseJobRank (matrixRel x.2)) (List.finRange n) K)
        ((Structure.tripleList (List.finRange n)).map Subtype.val) n) :=
    (((fst.comp universeNumber).pair (fst.pair (snd.pair ((family K).pair (fst.comp triples))))).comp layers)
  exact ((A.pair (fst.comp universeSet)).comp (lookupA setEq)).congr (fun _ _ => rfl)

def fullSolve : Uniform (fun n (x : Universe n × Matrix n) => Algorithm.fullSolve (matrixRel x.2)) :=
  fullSolveK 10000

end Uniform
end ThreeMachine.StackCompiler

end

end OAI
