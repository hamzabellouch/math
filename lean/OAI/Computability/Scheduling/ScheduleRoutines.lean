import OAI.Computability.Scheduling.FamilyRoutines

namespace OAI

universe u1 u2 u3 u4

section

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

instance {n : ℕ} (G : Instance n) : DecidableRel G.edge := fun a b =>
  inferInstanceAs (Decidable ((a,b) ∈ G.edges))

instance (n : ℕ) : Coding (Instance n) := ⟨fun G => enc G.edges⟩

@[simp] theorem enc_instance {n : ℕ} (G : Instance n) : enc G = enc G.edges := rfl

theorem enc_map_eq {α : Type u1} {β : Type u2} [Coding α] [Coding β] (f : α → β)
    (h : ∀ a, enc (f a) = enc a) (xs : List α) : enc (xs.map f) = enc xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,enc_cons,h,ih]

namespace Uniform

variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]

def matrixMapAny (d : I → ℕ) {p : ∀ i, (Fin (d i) × Fin (d i)) × α i → Bool}
    (P : Uniform p) : Uniform (fun i (x : Universe (d i) × α i) =>
      (fun a b => p i ((a,b),x.2) : Matrix (d i))) := by
  let A : Uniform (fun i (x : Fin (d i) × (Fin (d i) × α i)) => p i ((x.2.1,x.1),x.2.2)) :=
    (((snd.comp fst).pair fst).pair (snd.comp snd)).comp P
  let B : Uniform (fun i (x : Fin (d i) × (Universe (d i) × α i)) =>
      fun b => p i ((x.1,b),x.2.2)) :=
    (((snd.comp fst).pair (fst.pair (snd.comp snd))).comp (A.vectorMapAny d))
  exact ((fst.pair id).comp (B.vectorMapAny d)).congr (fun _ _ => rfl)

def instanceEdges : Uniform (fun n (G : Instance n) => G.edges) :=
  reinterpret _ (fun _ _ => rfl)

def edgePairEq : Uniform (fun n (x : (Fin n × Fin n) × (Fin n × Fin n)) => decide (x.1 = x.2)) :=
  (((fst.comp fst).pair (snd.comp fst)).comp finEq).andD
    (((fst.comp snd).pair (snd.comp snd)).comp finEq) |>.congr (fun _ x => by
      apply decide_eq_decide.mpr
      change (x.1.1 = x.2.1 ∧ x.1.2 = x.2.2) ↔ x.1 = x.2
      exact Prod.ext_iff.symm)

def edgeAt : Uniform (fun n (x : (Fin n × Fin n) × Instance n) => decide (x.2.edge x.1.1 x.1.2)) :=
  ((((snd.comp instanceEdges).pair fst).comp edgePairEq.any)).congr (fun _ x => by
    simp only [Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    simp only [List.any_eq_true,decide_eq_true_eq]
    change (∃ y ∈ x.2.edges, y = x.1) ↔ x.1 ∈ x.2.edges
    exact exists_eq_right)

def edgeMatrix : Uniform (fun n (x : Universe n × Instance n) =>
    (fun a b => decide (x.2.edge a b) : Matrix n)) := matrixMapAny (fun n : ℕ => n) edgeAt

def matrixRows : Uniform (fun n (M : Matrix n) => (List.ofFn M).map List.ofFn) :=
  reinterpret _ (fun _ M => by
    rw [enc_map_eq List.ofFn (fun _ => rfl)]
    rfl)

def readMatrix {n : ℕ} (M : Matrix n) (a b : ℕ) : Bool :=
  (((List.ofFn M).map List.ofFn).getD a []).getD b Bool.false

def matrixReadNat : Uniform (fun n (x : Matrix n × (ℕ × ℕ)) => readMatrix x.1 x.2.1 x.2.2) := by
  let A := ((((fst.comp matrixRows).pair (snd.comp fst)).pair nil).comp getElemD :
    Uniform (fun n (x : Matrix n × (ℕ × ℕ)) => ((List.ofFn x.1).map List.ofFn).getD x.2.1 []))
  exact (((A.pair (snd.comp snd)).pair false).comp getElemD)

theorem readMatrix_eq {n : ℕ} (M : Matrix n) (a b : ℕ) :
    readMatrix M a b = if ha : a < n then if hb : b < n then M ⟨a,ha⟩ ⟨b,hb⟩ else Bool.false else Bool.false := by
  simp only [readMatrix,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_ofFn]
  split_ifs <;> simp_all

def paddedMatrix : Uniform (fun (i : ℕ × ℕ) (x : Universe i.2 × Matrix i.1) =>
    (fun a b => decide (paddedOrder (matrixRel x.2) i.2 a b) : Matrix i.2)) := by
  let P : Uniform (fun (i : ℕ × ℕ) (x : (Fin i.2 × Fin i.2) × Matrix i.1) =>
      readMatrix x.2 x.1.1.val x.1.2.val) :=
    (snd.pair (((fst.comp fst).comp (finValue Prod.snd)).pair
      ((fst.comp snd).comp (finValue Prod.snd)))).comp (matrixReadNat.reindex Prod.fst)
  exact (matrixMapAny Prod.snd P).congr (fun i x => by
    funext a b
    rw [readMatrix_eq]
    by_cases ha : a.val < i.1 <;> by_cases hb : b.val < i.1
    · simp only [dite_eq_left ha,dite_eq_left hb]
      apply Bool.eq_iff_iff.mpr
      change (x.2 ⟨a.val,ha⟩ ⟨b.val,hb⟩ = true) ↔
        (decide (paddedOrder (matrixRel x.2) i.2 a b) = true)
      rw [decide_eq_true_eq]
      change (matrixRel x.2 ⟨a.val,ha⟩ ⟨b.val,hb⟩) ↔ paddedOrder (matrixRel x.2) i.2 a b
      constructor
      · intro h; exact ⟨⟨a.val,ha⟩,⟨b.val,hb⟩,rfl,rfl,h⟩
      · rintro ⟨u,v,hu,hv,h⟩
        have eu : u = ⟨a.val,ha⟩ := Fin.ext hu.symm
        have ev : v = ⟨b.val,hb⟩ := Fin.ext hv.symm
        simpa only [eu,ev] using h
    · simp only [dite_eq_left ha,dite_eq_right hb]
      have h : ¬paddedOrder (matrixRel x.2) i.2 a b := by
        rintro ⟨u,v,hu,hv,hr⟩; exact hb (hv.symm ▸ v.isLt)
      simp only [h,decide_false]
    · simp only [dite_eq_right ha]
      have h : ¬paddedOrder (matrixRel x.2) i.2 a b := by
        rintro ⟨u,v,hu,hv,hr⟩; exact ha (hu.symm ▸ u.isLt)
      simp only [h,decide_false]
    · simp only [dite_eq_right ha]
      have h : ¬paddedOrder (matrixRel x.2) i.2 a b := by
        rintro ⟨u,v,hu,hv,hr⟩; exact ha (hu.symm ▸ u.isLt)
      simp only [h,decide_false])

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

def nextMatrix {n : ℕ} (E M : Matrix n) : Matrix n :=
  fun a b => M a b || (List.finRange n).any (fun z => M a z && E z b)

def closureMatrix {n : ℕ} (G : Instance n) (k : ℕ) : Matrix n :=
  fun a b => decide ((a,b) ∈ Algorithm.closureTable G k)

theorem closureMatrix_zero {n : ℕ} (G : Instance n) :
    closureMatrix G 0 = fun a b => decide (G.edge a b) := by
  funext a b
  simp only [closureMatrix,Algorithm.closureTable_zero,List.mem_toFinset,Instance.edge]
  rfl

theorem nextMatrix_closure {n : ℕ} (G : Instance n) (k : ℕ) :
    nextMatrix (closureMatrix G 0) (closureMatrix G k) = closureMatrix G (k+1) := by
  funext a b
  apply Bool.eq_iff_iff.mpr
  simp only [nextMatrix,closureMatrix,Bool.or_eq_true,Bool.and_eq_true,List.any_eq_true,
    decide_eq_true_eq,List.mem_finRange]
  simp only [Algorithm.closureTable_succ,Algorithm.closureTable_zero,
    Algorithm.closureStep,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]

namespace Uniform

def nextMatrixCell : Uniform (fun n (x : (Fin n × Fin n) × (Universe n × (Matrix n × Matrix n))) =>
    ThreeMachine.StackCompiler.nextMatrix x.2.2.1 x.2.2.2 x.1.1 x.1.2) := by
  let P : Uniform (fun n (x : Fin n × ((Fin n × Fin n) × (Matrix n × Matrix n))) =>
      x.2.2.2 x.2.1.1 x.1 && x.2.2.1 x.1 x.2.1.2) :=
    (((((snd.comp (snd.comp snd)).pair (((snd.comp (fst.comp fst)).pair fst))).comp matrixGet).pair
      (((snd.comp (snd.comp fst)).pair (fst.pair (snd.comp (fst.comp snd)))).comp matrixGet)).comp
      (Realizer.and.uniform ℕ))
  let A := (((snd.comp (snd.comp snd)).pair fst).comp matrixGet :
    Uniform (fun n (x : (Fin n × Fin n) × (Universe n × (Matrix n × Matrix n))) =>
      x.2.2.2 x.1.1 x.1.2))
  let B := ((((snd.comp fst).comp universeList).pair (fst.pair (snd.comp snd))).comp P.any)
  exact ((A.pair B).comp (Realizer.or.uniform ℕ)).congr (fun _ _ => rfl)

def nextMatrix : Uniform (fun n (x : Universe n × (Matrix n × Matrix n)) =>
    ThreeMachine.StackCompiler.nextMatrix x.2.1 x.2.2) :=
  (fst.pair id).comp (matrixMapAny (fun n => n) nextMatrixCell)

def closureMatrixStep : Uniform (fun n (x : (Universe n × Matrix n) × Matrix n) =>
    (x.1,ThreeMachine.StackCompiler.nextMatrix x.1.2 x.2)) :=
  fst.pair ((((fst.comp fst).pair ((fst.comp snd).pair snd))).comp nextMatrix)

def reachMatrix : Uniform (fun n (x : Universe n × Instance n) => closureMatrix x.2 n) := by
  let A := fst.pair edgeMatrix
  let B := ((fst.comp universeNumber).pair (A.pair edgeMatrix)).comp closureMatrixStep.iterate |>.comp snd
  exact B.congr (fun n x => by
    dsimp only [Function.comp_apply]
    have h : ∀ k, (fun p : (Universe n × Matrix n) × Matrix n =>
        (p.1,ThreeMachine.StackCompiler.nextMatrix p.1.2 p.2))^[k]
        ((x.1,fun a b => decide (x.2.edge a b)),fun a b => decide (x.2.edge a b)) =
        ((x.1,fun a b => decide (x.2.edge a b)),closureMatrix x.2 k) := by
      intro k
      induction k with
      | zero => rw [Function.iterate_zero_apply,closureMatrix_zero]
      | succ k ih =>
        rw [Function.iterate_succ_apply',ih]
        simp only [← closureMatrix_zero,nextMatrix_closure]
    rw [h])

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

namespace Realizer

def triple : Realizer (fun n : ℕ => 3*n) :=
  (((id.pair id).comp add).pair id |>.comp add).congr (fun n => by
    simp only [Function.comp_apply,id_eq]
    omega)

end Realizer

def scheduleMatrix {n : ℕ} (M : Matrix n) (T : ℕ) : Option (Fin n → ℕ) :=
  if hn : n ≤ 3*T then
    (Algorithm.fullSolve (paddedOrder (matrixRel M) (3*T))).map
      (fun s x => s.time (Fin.castLE hn x))
  else none

theorem scheduleMatrix_closure {n : ℕ} (G : Instance n) (T : ℕ) :
    scheduleMatrix (closureMatrix G n) T = Algorithm.scheduleAt G T := by
  have h : matrixRel (closureMatrix G n) = Algorithm.reachable G := by
    funext a b
    simp only [matrixRel,closureMatrix,decide_eq_true_eq,Algorithm.reachable]
  simp only [scheduleMatrix,Algorithm.scheduleAt,h]

namespace Uniform

def restrictTime : Uniform (fun (i : ℕ × ℕ) (x : Universe i.1 × (Fin i.2 → ℕ)) =>
    (fun v : Fin i.1 => (List.ofFn x.2).getD v.val 0)) := by
  let A : Uniform (fun (i : ℕ × ℕ) (x : Fin i.1 × (Fin i.2 → ℕ)) =>
      (List.ofFn x.2).getD x.1.val 0) :=
    ((((snd.comp (functionListAny Prod.snd)).pair (fst.comp (finValue Prod.fst))).pair zero).comp getElemD)
  exact A.vectorMapAny Prod.fst

def paddedSolve : Uniform (fun (i : ℕ × ℕ) (x : Cardinal i.2 × Matrix i.1) =>
    Algorithm.fullSolve (paddedOrder (matrixRel x.2) (3*i.2))) := by
  let U : Uniform (fun (i : ℕ × ℕ) (_ : Cardinal i.2 × Matrix i.1) =>
      (Universe.mk () : Universe (3*i.2))) := (fst.comp (cardinalMap Prod.snd Realizer.triple)).comp
    (makeUniverseAny (fun i : ℕ × ℕ => 3*i.2))
  let A := (U.pair snd).comp (paddedMatrix.reindex (fun i : ℕ × ℕ => (i.1,3*i.2)))
  exact ((U.pair A).comp (fullSolve.reindex (fun i : ℕ × ℕ => 3*i.2))).congr (fun i x => by
    have h : matrixRel (fun a b : Fin (3*i.2) => decide (paddedOrder (matrixRel x.2) (3*i.2) a b)) =
        paddedOrder (matrixRel x.2) (3*i.2) := by
      funext a b
      exact propext (by simp only [matrixRel,decide_eq_true_eq])
    simp only [Function.comp_apply,h])

def scheduleMatrixFixed : Uniform (fun (i : ℕ × ℕ)
    (x : Universe i.1 × (Cardinal i.2 × Matrix i.1)) =>
      ThreeMachine.StackCompiler.scheduleMatrix x.2.2 i.2) := by
  let P : Uniform (fun (i : ℕ × ℕ) (_ : Universe i.1 × (Cardinal i.2 × Matrix i.1)) =>
      decide (i.1 ≤ 3*i.2)) :=
    (((fst.comp (universeNumber.reindex Prod.fst)).pair
      ((snd.comp fst).comp (cardinalValue Prod.snd) |>.comp (Realizer.triple.uniform (ℕ × ℕ)))).comp
      (Realizer.le.uniform (ℕ × ℕ)))
  let R : Uniform (fun (i : ℕ × ℕ) (x : Algorithm.Block (Fin (3*i.2)) × Universe i.1) =>
      (fun v : Fin i.1 => (List.ofFn x.1.time).getD v.val 0)) :=
    (snd.pair (fst.comp (blockTime.reindex (fun i : ℕ × ℕ => 3*i.2)))).comp
      (restrictTime.reindex (fun i : ℕ × ℕ => (i.1,3*i.2)))
  let A := (((snd.comp paddedSolve).pair fst).comp R.optionMap)
  exact ((P.pair id).comp (A.choose none)).congr (fun i x => by
    simp only [Function.comp_apply,ThreeMachine.StackCompiler.scheduleMatrix]
    by_cases h : i.1 ≤ 3*i.2
    · simp only [decide_eq_true_eq,ite_eq_left h,dite_eq_left h]
      apply congrArg (fun f => Option.map f _)
      funext b
      funext v
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left (lt_of_lt_of_le v.isLt h),
        Option.getD_some]
      rfl
    · simp only [decide_eq_true_eq,ite_eq_right h,dite_eq_right h])

def scheduleMatrix : Uniform (fun n (x : Universe n × (ℕ × Matrix n)) =>
    ThreeMachine.StackCompiler.scheduleMatrix x.2.2 x.2.1) :=
  scheduleMatrixFixed.recode _ (fun n x =>
    ⟨(n,x.2.1),(x.1,(Cardinal.mk (),x.2.2)),rfl,rfl⟩)

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

def bestMatrix {n : ℕ} (M : Matrix n) : ℕ → Option (ℕ × (Fin n → ℕ))
  | 0 => none
  | k+1 => match bestMatrix M k with
    | some a => some a
    | none => (scheduleMatrix M (k+1)).map (fun t => (k+1,t))

theorem bestMatrix_closure {n : ℕ} (G : Instance n) (k : ℕ) :
    bestMatrix (closureMatrix G n) k = Algorithm.best G k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [bestMatrix,Algorithm.best,ih,scheduleMatrix_closure]
      cases Algorithm.best G k <;> rfl

def bestMatrixStep {n : ℕ}
    (x : (Universe n × Matrix n) × (ℕ × Option (ℕ × (Fin n → ℕ)))) :=
  (x.1,(x.2.1+1,match x.2.2 with
    | some a => some a
    | none => (scheduleMatrix x.1.2 (x.2.1+1)).map (fun t => (x.2.1+1,t))))

theorem bestMatrix_iterate {n : ℕ} (U : Universe n) (M : Matrix n) (k : ℕ) :
    bestMatrixStep^[k] ((U,M),(0,none)) = ((U,M),(k,bestMatrix M k)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl

def answerMatrix {n : ℕ} (M : Matrix n) : Option ℕ → Option (List ℕ)
  | some T => (scheduleMatrix M T).map List.ofFn
  | none => (bestMatrix M n).map (fun a => List.ofFn a.2)

theorem answerMatrix_closure {n : ℕ} (G : Instance n) (d : Option ℕ) :
    encodeAnswer (answerMatrix (closureMatrix G n) d) = Algorithm.output G d := by
  cases d <;> simp only [answerMatrix,Algorithm.output,scheduleMatrix_closure,bestMatrix_closure,slots]
  all_goals rfl

namespace Uniform

def bestMatrixStep : Uniform (fun n => @ThreeMachine.StackCompiler.bestMatrixStep n) := by
  let K := ((snd.comp fst).comp (Realizer.succ.uniform ℕ) :
    Uniform (fun n (x : (Universe n × Matrix n) × (ℕ × Option (ℕ × (Fin n → ℕ)))) => x.2.1+1))
  let A := ((((fst.comp fst).pair (K.pair (fst.comp snd))).comp scheduleMatrix).pair K).comp
    swap.optionMap
  let R := ((((snd.comp snd).comp optionIsSome).pair id).comp ((snd.comp snd).choose A))
  exact (fst.pair (K.pair R)).congr (fun n x => by
    simp only [Function.comp_apply,ThreeMachine.StackCompiler.bestMatrixStep]
    cases x.2.2 <;> rfl)

def bestMatrix : Uniform (fun n (x : Universe n × Matrix n) =>
    ThreeMachine.StackCompiler.bestMatrix x.2 n) :=
  ((((fst.comp universeNumber).pair (id.pair (zero.pair none))).comp bestMatrixStep.iterate).comp
    (snd.comp snd)).congr (fun n x => by
      rcases x with ⟨U,M⟩
      simp only [Function.comp_apply,bestMatrix_iterate])

def answerMatrix : Uniform (fun n (x : Universe n × (Matrix n × Option ℕ)) =>
    ThreeMachine.StackCompiler.answerMatrix x.2.1 x.2.2) := by
  let T := ((((snd.comp snd).pair zero).comp getD) :
    Uniform (fun n (x : Universe n × (Matrix n × Option ℕ)) => x.2.2.getD 0))
  let A : Uniform (fun n (x : Universe n × (Matrix n × Option ℕ)) =>
      (ThreeMachine.StackCompiler.scheduleMatrix x.2.1 (x.2.2.getD 0)).map List.ofFn) :=
    ((fst.pair (T.pair (snd.comp fst))).comp scheduleMatrix).comp functionList.mapOption
  let B : Uniform (fun n (x : Universe n × (Matrix n × Option ℕ)) =>
      (ThreeMachine.StackCompiler.bestMatrix x.2.1 n).map (fun a => List.ofFn a.2)) :=
    ((fst.pair (snd.comp fst)).comp bestMatrix).comp (snd.comp functionList).mapOption
  exact ((((snd.comp snd).comp optionIsSome).pair id).comp (A.choose B)).congr (fun n x => by
    dsimp only [Function.comp_apply]
    cases x.2.2 <;> rfl)

def unaryAnswer : Uniform (fun n (x : Universe n × (Instance n × Option ℕ)) =>
    ThreeMachine.StackCompiler.answerMatrix (closureMatrix x.2.1 n) x.2.2) :=
  (fst.pair ((((fst.pair (snd.comp fst)).comp reachMatrix).pair (snd.comp snd)))).comp answerMatrix

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.Algorithm
open Structure

namespace Block

def Bounded {J : Type} (s : Block J) : Prop := ∀ x, s.time x ≤ s.length

theorem bounded_empty {J : Type} : (empty : Block J).Bounded := fun _ => le_rfl

theorem bounded_triple {J : Type} : (triple : Block J).Bounded := fun _ => le_rfl

theorem Bounded.append {J : Type} [DecidableEq J] {s t : Block J}
    (hs : s.Bounded) (ht : t.Bounded) (W : Finset J) : (append W s t).Bounded := by
  intro x
  change (if x ∈ W then s.time x else s.length+t.time x) ≤ s.length+t.length
  split_ifs
  · exact (hs x).trans (Nat.le_add_right _ _)
  · exact Nat.add_le_add_left (ht x) _

theorem Valid.length_le {n : ℕ} {r : Fin n → Fin n → Prop} {W : Finset (Fin n)}
    {s : Block (Fin n)} (hs : s.Valid r W) : s.length ≤ n := by
  obtain ⟨b,hbl,_⟩ := hs
  have h := b.size
  rw [Set.ncard_coe_finset,hbl] at h
  have hc := Finset.card_le_univ W
  simp only [Fintype.card_fin] at hc
  omega

end Block

namespace State
variable {J : Type} [DecidableEq J]

theorem bounded_advance (u : State J) {s t : Block J} (hs : s.Bounded) (ht : t.Bounded) :
    (u.advance s t).Bounded := (hs.append Block.bounded_triple u.left).append ht u.upto

theorem bounded_finish (u : State J) {s t : Block J} (hs : s.Bounded) (ht : t.Bounded) :
    (u.finish s t).Bounded := u.bounded_advance hs ht

end State

section Bounded
variable {J : Type} [Fintype J] [DecidableEq J] (r : J → J → Prop) [DecidableRel r]

def TableBounded (tab : List (Finset J × Block J)) : Prop :=
  ∀ W s, (W,s) ∈ tab → s.Bounded

def MarksBounded (marks : List (State J × Block J)) : Prop :=
  ∀ u s, (u,s) ∈ marks → s.Bounded

omit [Fintype J] in
theorem tryAdvance_bounded {tab : List (Finset J × Block J)} (htab : TableBounded tab)
    (u : State J) (v : State J) {b s : Block J} (hb : b.Bounded)
    (h : tryAdvance tab (u,b) v = some s) : s.Bounded := by
  simp only [tryAdvance] at h
  split_ifs at h
  · cases hg : lookup tab (v.left \ u.upto) with
    | none => simp [hg] at h
    | some t =>
      have he : u.advance b t = s := Option.some.inj (by simpa [hg] using h)
      exact he ▸ u.bounded_advance hb (htab _ _ (lookup_mem hg))

omit [Fintype J] [DecidableRel r] in
theorem markings_bounded {tab : List (Finset J × Block J)} {sts : List (State J)}
    (htab : TableBounded tab) (k : ℕ) : MarksBounded (markings tab sts k) := by
  induction k with
  | zero =>
    intro u s h
    obtain ⟨_,hs⟩ := (mem_tableOf sts _ u s).mp h
    exact htab _ _ (lookup_mem hs)
  | succ k ih =>
    intro v s h
    obtain ⟨_,hs⟩ := (mem_tableOf sts _ v s).mp h
    cases he : lookup (markings tab sts k) v with
    | some b =>
      have hb : b = s := Option.some.inj (by simpa only [he] using hs)
      exact hb ▸ ih v b (lookup_mem he)
    | none =>
      obtain ⟨⟨u,b⟩,hu,hh⟩ := firstResult_some (by simpa only [he] using hs)
      exact tryAdvance_bounded htab u v (ih u b hu) hh

theorem solve_bounded {tab : List (Finset J × Block J)} (htab : TableBounded tab)
    (family triples : List (Finset J)) {W : Finset J} {s : Block J}
    (h : solve r tab family triples W = some s) : s.Bounded := by
  simp only [solve] at h
  split_ifs at h
  · cases Option.some.inj h
    exact Block.bounded_empty
  · obtain ⟨⟨u,b⟩,hu,hs⟩ := firstResult_some h
    have hg := markings_bounded htab (Fintype.card J) u b hu
    cases ht : lookup tab u.right with
    | none => simp [ht] at hs
    | some t =>
      have he : u.finish b t = s := Option.some.inj (by simpa [ht] using hs)
      exact he ▸ u.bounded_finish hg (htab _ _ (lookup_mem ht))

theorem layers_bounded (family triples : List (Finset J)) (k : ℕ) :
    TableBounded (layers r family triples k) := by
  induction k with
  | zero =>
    intro W s h
    have he : (W,s) = (∅,Block.empty) := by simpa only [layers,List.mem_singleton] using h
    cases he
    exact Block.bounded_empty
  | succ k ih =>
    intro W s h
    exact solve_bounded r ih family triples ((mem_tableOf family _ W s).mp h).2

end Bounded

end ThreeMachine.Algorithm

end

end OAI
