import OAI.Computability.Scheduling.ListRoutines

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

instance (n : ℕ) : Coding (Algorithm.State (Fin n)) :=
  ⟨fun s => enc (s.left,(s.middle,s.right))⟩
instance (n : ℕ) : Coding (Algorithm.Block (Fin n)) :=
  ⟨fun s => enc (s.length,s.time)⟩

abbrev Matrix (n : ℕ) := Fin n → Fin n → Bool

def matrixRel {n : ℕ} (M : Matrix n) (x y : Fin n) : Prop := M x y = true

instance {n : ℕ} (M : Matrix n) : DecidableRel (matrixRel M) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

namespace Uniform

def universeNumber : Uniform (fun n (_ : Universe n) => n) :=
  (universeList.comp length).congr (fun _ _ => List.length_finRange)

def stateParts : Uniform (fun n (s : Algorithm.State (Fin n)) => (s.left,(s.middle,s.right))) :=
  reinterpret _ (fun _ _ => rfl)

def stateMake : Uniform (fun n (x : Finset (Fin n) × (Finset (Fin n) × Finset (Fin n))) =>
    (⟨x.1,x.2.1,x.2.2⟩ : Algorithm.State (Fin n))) :=
  reinterpret _ (fun _ _ => rfl)

def stateLeft : Uniform (fun n (s : Algorithm.State (Fin n)) => s.left) := stateParts.comp fst

def stateMiddle : Uniform (fun n (s : Algorithm.State (Fin n)) => s.middle) := stateParts.comp (snd.comp fst)

def stateRight : Uniform (fun n (s : Algorithm.State (Fin n)) => s.right) := stateParts.comp (snd.comp snd)

def stateEq : Uniform (fun n (x : Algorithm.State (Fin n) × Algorithm.State (Fin n)) =>
    decide (x.1 = x.2)) :=
  (((((fst.comp stateLeft).pair (snd.comp stateLeft)).comp setEq).pair
    (((((fst.comp stateMiddle).pair (snd.comp stateMiddle)).comp setEq).pair
      (((fst.comp stateRight).pair (snd.comp stateRight)).comp setEq)).comp (Realizer.and.uniform ℕ))).comp
    (Realizer.and.uniform ℕ)).congr (fun _ x => by
      rcases x with ⟨⟨a,b,c⟩,⟨d,e,f⟩⟩
      apply Bool.eq_iff_iff.mpr
      simp)

def blockParts : Uniform (fun n (s : Algorithm.Block (Fin n)) => (s.length,s.time)) :=
  reinterpret _ (fun _ _ => rfl)

def blockMake : Uniform (fun n (x : ℕ × (Fin n → ℕ)) => (⟨x.1,x.2⟩ : Algorithm.Block (Fin n))) :=
  reinterpret _ (fun _ _ => rfl)

def blockLength : Uniform (fun n (s : Algorithm.Block (Fin n)) => s.length) := blockParts.comp fst

def blockTime : Uniform (fun n (s : Algorithm.Block (Fin n)) => s.time) := blockParts.comp snd

def matrixGet : Uniform (fun n (x : Matrix n × (Fin n × Fin n)) => x.1 x.2.1 x.2.2) :=
  ((((fst.pair (snd.comp fst)).comp functionGet).pair (snd.comp snd)).comp functionGet)

def setAll {γ : ℕ → Type u1} [∀ n, Coding (γ n)]
    {p : ∀ n, Fin n × γ n → Bool} (P : Uniform p) :
    Uniform (fun n (x : Finset (Fin n) × γ n) => decide (∀ a ∈ x.1, p n (a,x.2) = true)) :=
  (setList.onFst.comp P.all).congr (fun _ x => by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.all_eq_true,Finset.mem_sort,decide_eq_true_eq])

def setAny {γ : ℕ → Type u2} [∀ n, Coding (γ n)]
    {p : ∀ n, Fin n × γ n → Bool} (P : Uniform p) :
    Uniform (fun n (x : Finset (Fin n) × γ n) => decide (∃ a ∈ x.1, p n (a,x.2) = true)) :=
  (setList.onFst.comp P.any).congr (fun _ x => by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.any_eq_true,Finset.mem_sort,decide_eq_true_eq])

variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]

def andD {p q : ∀ i, α i → Prop} [∀ i, DecidablePred (p i)] [∀ i, DecidablePred (q i)]
    (P : Uniform (fun i x => decide (p i x))) (Q : Uniform (fun i x => decide (q i x))) :
    Uniform (fun i x => decide (p i x ∧ q i x)) :=
  ((P.pair Q).comp (Realizer.and.uniform I)).congr (fun _ _ => by simp)

def orD {p q : ∀ i, α i → Prop} [∀ i, DecidablePred (p i)] [∀ i, DecidablePred (q i)]
    (P : Uniform (fun i x => decide (p i x))) (Q : Uniform (fun i x => decide (q i x))) :
    Uniform (fun i x => decide (p i x ∨ q i x)) :=
  ((P.pair Q).comp (Realizer.or.uniform I)).congr (fun _ _ => by simp)

def notD {p : ∀ i, α i → Prop} [∀ i, DecidablePred (p i)]
    (P : Uniform (fun i x => decide (p i x))) :
    Uniform (fun i x => decide (¬p i x)) :=
  (P.comp (Realizer.not.uniform I)).congr (fun _ _ => by simp)

def noEdges : Uniform (fun n (x : Matrix n × (Finset (Fin n) × Finset (Fin n))) =>
    decide (∀ a ∈ x.2.1, ∀ b ∈ x.2.2, ¬matrixRel x.1 a b)) := by
  let E : Uniform (fun n (x : Fin n × (Matrix n × Fin n)) => !x.2.1 x.2.2 x.1) :=
    (((snd.comp fst).pair ((snd.comp snd).pair fst)).comp matrixGet).comp (Realizer.not.uniform ℕ)
  let F : Uniform (fun n (x : Fin n × (Matrix n × Finset (Fin n))) =>
      decide (∀ b ∈ x.2.2, ¬matrixRel x.2.1 x.1 b)) :=
    (((snd.comp snd).pair ((snd.comp fst).pair fst)).comp E.setAll).congr (fun _ _ => by
      simp only [Function.comp_apply,Bool.not_eq_true,matrixRel,Bool.not_eq_true'])
  exact (((snd.comp fst).pair (fst.pair (snd.comp snd))).comp F.setAll).congr (fun _ _ => by
    simp only [Function.comp_apply,decide_eq_true_eq])

def stateCandidate : Uniform (fun n (x : Universe n ×
    (Finset (Fin n) × (Finset (Fin n) × Finset (Fin n)))) =>
      Algorithm.State.candidate x.2.1 x.2.2.1 x.2.2.2) := by
  let L := (((snd.comp fst).pair (snd.comp (snd.comp fst))).comp setInter :
    Uniform (fun n (x : Universe n × (Finset (Fin n) × (Finset (Fin n) × Finset (Fin n)))) => x.2.1 ∩ x.2.2.1))
  let Z := (snd.comp (snd.comp snd) :
    Uniform (fun n (x : Universe n × (Finset (Fin n) × (Finset (Fin n) × Finset (Fin n)))) => x.2.2.2))
  exact (L.pair (Z.pair (((snd.comp fst).pair ((fst.pair (L.pair Z)).comp setUnion)).comp setDiff))).comp stateMake

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm
namespace Uniform

def stateUpto : Uniform (fun n (x : Universe n × Algorithm.State (Fin n)) => x.2.upto) :=
  (fst.pair ((snd.comp stateLeft).pair (snd.comp stateMiddle))).comp setUnion

abbrev CompatInput (n : ℕ) := Universe n × (Matrix n × (Finset (Fin n) × Algorithm.State (Fin n)))
def scU : Uniform (fun n (x : CompatInput n) => x.1) := fst
def scM : Uniform (fun n (x : CompatInput n) => x.2.1) := snd.comp fst
def scW : Uniform (fun n (x : CompatInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def scS : Uniform (fun n (x : CompatInput n) => x.2.2.2) := snd.comp (snd.comp snd)
def scL := scS.comp stateLeft
def scZ := scS.comp stateMiddle
def scR := scS.comp stateRight
def scLZ := (scU.pair (scL.pair scZ)).comp setUnion
def scLZR := (scU.pair (scLZ.pair scR)).comp setUnion
def scA := (scLZR.pair scW).comp setEq
def scB := (scL.pair scZ).comp setDisjoint
def scC := (scL.pair scR).comp setDisjoint
def scD := (scZ.pair scR).comp setDisjoint
def scE := ((scZ.comp setCard).pair (constant 3)).comp (Realizer.eqNat.uniform ℕ)
def scF := (scM.pair (scZ.pair scZ)).comp noEdges
def scH := (scM.pair (scZ.pair scL)).comp noEdges
def scI := (scM.pair (scR.pair scL)).comp noEdges
def scJ := (scM.pair (scR.pair scZ)).comp noEdges
def scIJ := scI.andD scJ
def scHIJ := scH.andD scIJ
def scFHIJ := scF.andD scHIJ
def scEFHIJ := scE.andD scFHIJ
def scDEFHIJ := scD.andD scEFHIJ
def scCDEFHIJ := scC.andD scDEFHIJ
def scBCDEFHIJ := scB.andD scCDEFHIJ
def scAll := scA.andD scBCDEFHIJ
def stateCompatible : Uniform (fun n (x : Universe n ×
     (Matrix n × (Finset (Fin n) × Algorithm.State (Fin n)))) =>
      decide (x.2.2.2.Compatible (matrixRel x.2.1) x.2.2.1)) :=
  scAll.congr (fun _ _ => by apply decide_eq_decide.mpr; rfl)

def blockEmpty : Uniform (fun n (_ : Universe n) => (Algorithm.Block.empty : Algorithm.Block (Fin n))) :=
  (zero.pair ((id.pair unit).comp zero.vectorMap)).comp blockMake

def blockTriple : Uniform (fun n (_ : Universe n) => (Algorithm.Block.triple : Algorithm.Block (Fin n))) :=
  ((constant 1).pair ((id.pair unit).comp (constant 1).vectorMap)).comp blockMake

def blockAppend : Uniform (fun n (x : Universe n ×
    (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) =>
      Algorithm.Block.append x.2.1 x.2.2.1 x.2.2.2) := by
  let F : Uniform (fun n (x : Fin n ×
      (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) =>
      if x.1 ∈ x.2.1 then x.2.2.1.time x.1 else x.2.2.1.length+x.2.2.2.time x.1) := by
    let S := (snd.comp (snd.comp fst) : Uniform (fun n (x : Fin n ×
      (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.2.2.1))
    let T := (snd.comp (snd.comp snd) : Uniform (fun n (x : Fin n ×
      (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.2.2.2))
    exact (((fst.pair (snd.comp fst)).comp setMem).ite
      (((S.comp blockTime).pair fst).comp functionGet)
      (((S.comp blockLength).pair (((T.comp blockTime).pair fst).comp functionGet)).comp
        (Realizer.add.uniform ℕ))).congr (fun _ _ => by simp)
  exact ((((snd.comp (snd.comp fst)).comp blockLength).pair
      ((snd.comp (snd.comp snd)).comp blockLength)).comp (Realizer.add.uniform ℕ)).pair
      F.vectorMap |>.comp blockMake

def stateAdvance : Uniform (fun n (x : Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) =>
      x.2.1.advance x.2.2.1 x.2.2.2) := by
  let U := (fst : Uniform (fun n (x : Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.1))
  let V := (snd.comp fst : Uniform (fun n (x : Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.2.1))
  let S := (snd.comp (snd.comp fst) : Uniform (fun n (x : Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.2.2.1))
  let T := (snd.comp (snd.comp snd) : Uniform (fun n (x : Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))) => x.2.2.2))
  let B := (U.pair ((V.comp stateLeft).pair (S.pair (U.comp blockTriple)))).comp blockAppend
  exact (U.pair (((U.pair V).comp stateUpto).pair (B.pair T))).comp blockAppend

variable {I : Type u5} {α β γ : I → Type}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

def lookupA [∀ i, DecidableEq (α i)]
    (E : Uniform (fun i (x : α i × α i) => decide (x.1 = x.2))) :
    Uniform (fun i (x : List (α i × β i) × α i) => Algorithm.lookup x.1 x.2) :=
  (lookup E).congr (fun _ x => by
    induction x.1 with
    | nil => rfl
    | cons a xs ih => simp only [lookupList,Algorithm.lookup]; split <;> simp_all)

def firstResultA {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => Algorithm.firstResult (fun a => f i (a,x.2)) x.1) :=
  R.firstResult.congr (fun _ x => by
    induction x.1 with
    | nil => rfl
    | cons a xs ih => simp only [List.filterMap_cons,Algorithm.firstResult]; cases f _ (a,x.2) <;> simp_all)

def tableOfA {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => Algorithm.tableOf x.1 (fun a => f i (a,x.2))) :=
  R.tableOf

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm
abbrev Table (n : ℕ) := List (Finset (Fin n) × Algorithm.Block (Fin n))
abbrev Marks (n : ℕ) := List (Algorithm.State (Fin n) × Algorithm.Block (Fin n))
namespace Uniform

variable {I : Type u6} {α : I → Type u7} {β : I → Type u8}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)]

def singleton : Uniform (fun i (a : α i) => [a]) := (id.pair nil).comp cons

def product : Uniform (fun i (x : List (α i) × List (β i)) => x.1.product x.2) :=
  ((snd.pair fst).comp swap.map).flatMap.congr (fun _ _ => rfl)

def states : Uniform (fun n (x : Universe n × (Matrix n ×
    (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n))))) =>
      Algorithm.states (matrixRel x.2.1) x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  let C : Uniform (fun n (x : (Finset (Fin n) × Finset (Fin n)) ×
      (Universe n × Finset (Fin n))) => Algorithm.State.candidate x.2.2 x.1.1 x.1.2) :=
    ((snd.comp fst).pair ((snd.comp snd).pair ((fst.comp fst).pair (fst.comp snd)))).comp stateCandidate
  let F := (snd.comp (snd.comp fst) : Uniform (fun n (x : Universe n × (Matrix n ×
    (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n))))) => x.2.2.1))
  let Z := (snd.comp (snd.comp (snd.comp fst)) : Uniform (fun n (x : Universe n × (Matrix n ×
    (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n))))) => x.2.2.2.1))
  let W := (snd.comp (snd.comp (snd.comp snd)) : Uniform (fun n (x : Universe n × (Matrix n ×
    (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n))))) => x.2.2.2.2))
  let S := (((F.pair Z).comp product).pair (fst.pair W)).comp C.map
  let P : Uniform (fun n (x : Algorithm.State (Fin n) ×
      (Universe n × (Matrix n × Finset (Fin n)))) =>
      decide (x.1.Compatible (matrixRel x.2.2.1) x.2.2.2)) :=
    ((snd.comp fst).pair ((snd.comp (snd.comp fst)).pair ((snd.comp (snd.comp snd)).pair fst))).comp stateCompatible
  exact ((S.pair (fst.pair ((snd.comp fst).pair W))).comp P.filter).congr (fun _ x => by
    simp only [Function.comp_apply,Algorithm.states,List.product,List.map_flatMap,List.map_map]
    rfl)

def advanceLast : Uniform (fun n (x : Algorithm.Block (Fin n) ×
    (Universe n × (Algorithm.State (Fin n) × Algorithm.Block (Fin n)))) =>
      x.2.2.1.advance x.2.2.2 x.1) :=
  ((snd.comp fst).pair ((snd.comp (snd.comp fst)).pair ((snd.comp (snd.comp snd)).pair fst))).comp stateAdvance

def tryAdvance : Uniform (fun n (x : Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))) =>
      Algorithm.tryAdvance x.2.1 x.2.2.1 x.2.2.2) := by
  let U := (fst : Uniform (fun n (x : Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))) => x.1))
  let T := (snd.comp fst : Uniform (fun n (x : Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))) => x.2.1))
  let A := (snd.comp (snd.comp fst) : Uniform (fun n (x : Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))) => x.2.2.1))
  let V := (snd.comp (snd.comp snd) : Uniform (fun n (x : Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))) => x.2.2.2))
  let W := (U.pair (A.comp fst)).comp stateUpto
  let L := V.comp stateLeft
  let P := (W.pair L).comp setSubset
  let O := (T.pair ((L.pair W).comp setDiff)).comp (lookupA setEq)
  exact (P.ite ((O.pair (U.pair A)).comp advanceLast.optionMap) none).congr (fun _ _ => by
    simp only [Function.comp_apply,Algorithm.tryAdvance,decide_eq_true_eq])

def expandBody : Uniform (fun n (x : Algorithm.State (Fin n) ×
    (Universe n × (Table n × Marks n))) =>
      match Algorithm.lookup x.2.2.2 x.1 with
      | Option.some s => Option.some s
      | Option.none => Algorithm.firstResult (fun u => Algorithm.tryAdvance x.2.2.1 u x.1) x.2.2.2) := by
  let A : Uniform (fun n (x : (Algorithm.State (Fin n) × Algorithm.Block (Fin n)) ×
      (Universe n × (Table n × Algorithm.State (Fin n)))) =>
      Algorithm.tryAdvance x.2.2.1 x.1 x.2.2.2) :=
    ((snd.comp fst).pair ((snd.comp (snd.comp fst)).pair (fst.pair (snd.comp (snd.comp snd))))).comp tryAdvance
  let O := (((snd.comp (snd.comp snd)).pair fst).comp (lookupA stateEq) :
    Uniform (fun n (x : Algorithm.State (Fin n) × (Universe n × (Table n × Marks n))) =>
      Algorithm.lookup x.2.2.2 x.1))
  let B := ((snd.comp (snd.comp snd)).pair
      ((snd.comp fst).pair ((snd.comp (snd.comp fst)).pair fst))).comp A.firstResultA
  exact ((O.pair B).comp optionOrElse).congr (fun _ x => by
    simp only [Function.comp_apply]; cases Algorithm.lookup x.2.2.2 x.1 <;> rfl)

def expand : Uniform (fun n (x : Universe n ×
    (Table n × (List (Algorithm.State (Fin n)) × Marks n))) =>
      Algorithm.expand x.2.1 x.2.2.1 x.2.2.2) :=
  ((snd.comp (snd.comp fst)).pair
    (fst.pair ((snd.comp fst).pair (snd.comp (snd.comp snd))))).comp expandBody.tableOfA |>.congr
      (fun _ x => by
        simp only [Function.comp_apply,Algorithm.expand]
        congr 1
        funext v
        cases Algorithm.lookup x.2.2.2 v <;> rfl)

def initialMarks : Uniform (fun n (x : Table n × List (Algorithm.State (Fin n))) =>
    Algorithm.tableOf x.2 (fun v => Algorithm.lookup x.1 v.left)) :=
  (swap.comp ((snd.pair (fst.comp stateLeft)).comp (lookupA setEq)).tableOfA)

def markings : Uniform (fun n (x : ℕ ×
    (Universe n × (Table n × List (Algorithm.State (Fin n))))) =>
      Algorithm.markings x.2.2.1 x.2.2.2 x.1) := by
  let F : Uniform (fun n (x : (Universe n × (Table n × List (Algorithm.State (Fin n)))) × Marks n) =>
      (x.1,Algorithm.expand x.1.2.1 x.1.2.2 x.2)) :=
    fst.pair ((((fst.comp fst).pair ((fst.comp (snd.comp fst)).pair
      ((fst.comp (snd.comp snd)).pair snd)))).comp expand)
  exact (((fst.pair (snd.pair (snd.comp (snd.comp initialMarks)))).comp F.iterate).comp snd).congr
    (fun n x => by
      dsimp only [Function.comp_apply]
      have h : ∀ k, (fun p => (p.1,Algorithm.expand p.1.2.1 p.1.2.2 p.2))^[k]
          (x.2,Algorithm.tableOf x.2.2.2 (fun v => Algorithm.lookup x.2.2.1 v.left)) =
          (x.2,Algorithm.markings x.2.2.1 x.2.2.2 k) := by
        intro k; induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl
      rw [h])

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm
namespace Uniform

def finishing : Uniform (fun n (x : (Algorithm.State (Fin n) × Algorithm.Block (Fin n)) ×
    (Universe n × Table n)) =>
      (Algorithm.lookup x.2.2 x.1.1.right).map (x.1.1.finish x.1.2)) :=
  ((((snd.comp snd).pair ((fst.comp fst).comp stateRight)).comp (lookupA setEq)).pair
    ((snd.comp fst).pair fst)).comp advanceLast.optionMap

def solve : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) =>
      Algorithm.solve (matrixRel x.2.1) x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := by
  let U := (fst : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.1))
  let M := (snd.comp fst : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.2.1))
  let T := (snd.comp (snd.comp fst) : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.2.2.1))
  let F := (snd.comp (snd.comp (snd.comp fst)) : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.2.2.2.1))
  let Z := (snd.comp (snd.comp (snd.comp (snd.comp fst))) : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.2.2.2.2.1))
  let W := (snd.comp (snd.comp (snd.comp (snd.comp snd))) : Uniform (fun n (x : Universe n × (Matrix n ×
    (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))) => x.2.2.2.2.2))
  let S := (U.pair (M.pair (F.pair (Z.pair W)))).comp states
  let Marks := ((U.comp universeNumber).pair (U.pair (T.pair S))).comp markings
  let Out := (Marks.pair (U.pair T)).comp finishing.firstResultA
  exact ((W.comp setIsEmpty).ite (U.comp (blockEmpty.comp some)) Out).congr (fun _ _ => by
    simp only [Function.comp_apply,Algorithm.solve,decide_eq_true_eq,Fintype.card_fin])

def initialTable : Uniform (fun n (_ : Universe n) => ([(∅,Algorithm.Block.empty)] : Table n)) :=
  (setEmpty.pair blockEmpty).comp singleton

def layerStep : Uniform (fun n (x : (Universe n × (Matrix n ×
    (List (Finset (Fin n)) × List (Finset (Fin n))))) × Table n) =>
      (x.1,Algorithm.tableOf x.1.2.2.1
        (Algorithm.solve (matrixRel x.1.2.1) x.2 x.1.2.2.1 x.1.2.2.2))) := by
  let B : Uniform (fun n (x : Finset (Fin n) ×
      ((Universe n × (Matrix n × (List (Finset (Fin n)) × List (Finset (Fin n))))) × Table n)) =>
      Algorithm.solve (matrixRel x.2.1.2.1) x.2.2 x.2.1.2.2.1 x.2.1.2.2.2 x.1) :=
    ((snd.comp (fst.comp fst)).pair ((snd.comp (fst.comp (snd.comp fst))).pair
      ((snd.comp snd).pair ((snd.comp (fst.comp (snd.comp (snd.comp fst)))).pair
        ((snd.comp (fst.comp (snd.comp (snd.comp snd)))).pair fst))))).comp solve
  exact fst.pair (((fst.comp (snd.comp (snd.comp fst))).pair id).comp B.tableOfA)

def layers : Uniform (fun n (x : ℕ × (Universe n × (Matrix n ×
    (List (Finset (Fin n)) × List (Finset (Fin n)))))) =>
      Algorithm.layers (matrixRel x.2.2.1) x.2.2.2.1 x.2.2.2.2 x.1) :=
  (((fst.pair (snd.pair ((snd.comp fst).comp initialTable))).comp layerStep.iterate).comp snd).congr
    (fun n x => by
      dsimp only [Function.comp_apply]
      have h : ∀ k, (fun p => (p.1,Algorithm.tableOf p.1.2.2.1
          (Algorithm.solve (matrixRel p.1.2.1) p.2 p.1.2.2.1 p.1.2.2.2)))^[k]
          (x.2,[(∅,Algorithm.Block.empty)]) =
          (x.2,Algorithm.layers (matrixRel x.2.2.1) x.2.2.2.1 x.2.2.2.2 k) := by
        intro k; induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl
      rw [h])

end Uniform
end ThreeMachine.StackCompiler

end

end OAI
