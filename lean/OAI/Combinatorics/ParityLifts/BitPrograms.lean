import OAI.Combinatorics.ParityLifts.GraphPrograms

namespace OAI

namespace ParityWL.Complexity

noncomputable def PolyProgram.idxOf (α : Type) [TreeCodec α] [BEq α] [LawfulBEq α] [DecidableEq α] :
    PolyProgram (List α × α) ℕ (fun x => x.1.idxOf x.2) :=
  (PolyProgram.equal α).findIndexWith.congr (by intro x; exact findIndex_idxOf x.1 x.2)

def PolyProgram.names : PolyProgram BitFormula (List Name) Complexity.names :=
  ((PolyProgram.fst Name Bool).map.map.comp (PolyProgram.flatten Name)).congr (by intro F; rfl)

noncomputable def PolyProgram.lookupBits : PolyProgram ((List Name × List Bool) × Name) Bool
    (fun x => Complexity.lookupBits x.1.1 x.1.2 x.2) := by
  let V : PolyProgram ((List Name × List Bool) × Name) (List Name × Name) (fun x => (x.1.1,x.2)) :=
    .expr (.pair TExpr.input.left.left TExpr.input.right) (by intro x; rfl)
  let B : PolyProgram ((List Name × List Bool) × Name) (List Bool) (fun x => x.1.2) :=
    .expr TExpr.input.left.right (by intro x; rfl)
  exact (((V.comp (PolyProgram.idxOf Name)).pair B).comp (PolyProgram.getD Bool false)).congr (by intro x; rfl)

noncomputable def PolyProgram.literalTest : PolyProgram ((Name × Bool) × (List Name × List Bool)) Bool
    (fun x => decide (Complexity.lookupBits x.2.1 x.2.2 x.1.1=x.1.2)) := by
  let V : PolyProgram ((Name × Bool) × (List Name × List Bool)) ((List Name × List Bool) × Name)
      (fun x => (x.2,x.1.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left.left) (by intro x; rfl)
  let S : PolyProgram ((Name × Bool) × (List Name × List Bool)) Bool (fun x => x.1.2) :=
    .expr TExpr.input.left.right (by intro x; rfl)
  exact ((V.comp PolyProgram.lookupBits).pair S).comp (PolyProgram.equal Bool)

noncomputable def PolyProgram.checkFormula : PolyProgram (List Bool × BitFormula) Bool
    (fun x => x.2.all (fun C => C.any (fun l => decide (Complexity.lookupBits (Complexity.names x.2) x.1 l.1=l.2)))) := by
  let pair := ((PolyProgram.snd (List Bool) BitFormula).comp PolyProgram.names).pair
    (PolyProgram.fst (List Bool) BitFormula)
  let lit := PolyProgram.literalTest.mapWith.comp (PolyProgram.id Bool).any
  let cls := lit.mapWith.comp (PolyProgram.id Bool).all
  refine (((PolyProgram.snd (List Bool) BitFormula).pair pair).comp cls).congr ?_
  intro x
  simp only [Function.comp_def,List.all_map,List.any_map]
  rfl

noncomputable def PolyProgram.satisfyingWith : PolyProgram (List (List Bool) × BitFormula) (List (List Bool))
    (fun x => x.1.filter (fun bs => x.2.all (fun C => C.any
      (fun l => Complexity.lookupBits (Complexity.names x.2) bs l.1 == l.2)))) := by
  refine PolyProgram.checkFormula.filterWith.congr ?_
  intro x
  rfl

abbrev KeyInput (t : ℕ) := (Fin t → BitFormula) × (ℕ × (Fin t × (Fin t × List Bool)))

def PolyProgram.groupAt (t : ℕ) : PolyProgram ((Fin t → BitFormula) × Fin t) BitFormula
    (fun x => x.1 x.2) :=
  ((PolyProgram.snd (Fin t → BitFormula) (Fin t)).pair
    (PolyProgram.fst (Fin t → BitFormula) (Fin t))).comp (PolyProgram.evalFin t BitFormula)

noncomputable def PolyProgram.pairKey (t : ℕ) : PolyProgram (KeyInput t) (List Bool)
    (fun x => Complexity.pairKey x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  let Q := PolyProgram.fst (Fin t → BitFormula) (ℕ × (Fin t × (Fin t × List Bool)))
  let I : PolyProgram (KeyInput t) (Fin t × Fin t) (fun x => (x.2.2.1,x.2.2.2.1)) :=
    .expr (.pair TExpr.input.right.right.left TExpr.input.right.right.right.left) (by intro x; rfl)
  let lo := ((Q.pair (I.comp (PolyProgram.finite2 (min : Fin t → Fin t → Fin t)))).comp
    (PolyProgram.groupAt t)).comp PolyProgram.names
  let hi := ((Q.pair (I.comp (PolyProgram.finite2 (max : Fin t → Fin t → Fin t)))).comp
    (PolyProgram.groupAt t)).comp PolyProgram.names
  let own := ((Q.pair (I.comp (PolyProgram.fst (Fin t) (Fin t)))).comp
    (PolyProgram.groupAt t)).comp PolyProgram.names
  let bs : PolyProgram (KeyInput t) (List Bool) (fun x => x.2.2.2.2) :=
    .expr TExpr.input.right.right.right.right (by intro x; rfl)
  let va : PolyProgram (Name × (List Name × (List Name × List Bool))) Name Prod.fst :=
    PolyProgram.fst Name (List Name × (List Name × List Bool))
  let hs : PolyProgram (Name × (List Name × (List Name × List Bool))) (List Name) (fun x => x.2.1) :=
    .expr TExpr.input.right.left (by intro x; rfl)
  let os : PolyProgram (Name × (List Name × (List Name × List Bool))) (List Name × List Bool)
      (fun x => x.2.2) := .expr TExpr.input.right.right (by intro x; rfl)
  let L := ((va.pair hs).comp (PolyProgram.mem Name)).ite
    ((os.pair va).comp PolyProgram.lookupBits) (PolyProgram.const false)
  let first := (lo.pair (hi.pair (own.pair bs))).comp L.mapWith
  let D : PolyProgram (KeyInput t) ℕ (fun x => x.2.1) :=
    .expr TExpr.input.right.left (by intro x; rfl)
  let pad := (((D.pair (lo.comp (PolyProgram.length Name))).comp PolyProgram.natSub).comp PolyProgram.ticks)
  refine ((first.pair pad).comp (PolyProgram.append Bool)).congr ?_
  intro x
  simp only [Function.comp_def, Complexity.pairKey, decide_eq_true_eq]

abbrev TableInput (t : ℕ) := (Fin t → BitFormula) × (ℕ × List (List Bool))

def choiceWithWords {t : ℕ} (x : TableInput t) : ChoiceData t :=
  (fun i => (x.2.2.filter (fun bs => (x.1 i).all (fun C => C.any
      (fun l => Complexity.lookupBits (Complexity.names (x.1 i)) bs l.1 == l.2)))).map
        (fun bs j => x.2.2.idxOf (Complexity.pairKey x.1 x.2.1 i j bs)),
    fun _ _ => x.2.2.length)

lemma choiceWithWords_words {t : ℕ} (Q : Fin t → BitFormula) (d : ℕ) :
    Complexity.choiceWithWords (Q,d,words d) = bitChoiceData Q d := rfl

noncomputable def PolyProgram.rowKeyWith (t : ℕ) :
    PolyProgram (List Bool × (Fin t × TableInput t)) (Fin t → ℕ)
      (fun x j => x.2.2.2.2.idxOf (Complexity.pairKey x.2.2.1 x.2.2.2.1 x.2.1 j x.1)) := by
  let P : PolyProgram (Fin t × (List Bool × (Fin t × TableInput t))) (KeyInput t)
      (fun x => (x.2.2.2.1,(x.2.2.2.2.1,(x.2.2.1,(x.1,x.2.1)))) ) :=
    .expr (.pair TExpr.input.right.right.right.left
      (.pair TExpr.input.right.right.right.right.left (.pair TExpr.input.right.right.left
        (.pair TExpr.input.left TExpr.input.right.left)))) (by intro x; rfl)
  let W : PolyProgram (Fin t × (List Bool × (Fin t × TableInput t))) (List (List Bool))
      (fun x => x.2.2.2.2.2) :=
    .expr TExpr.input.right.right.right.right.right (by intro x; rfl)
  exact ((W.pair (P.comp (PolyProgram.pairKey t))).comp (PolyProgram.idxOf (List Bool))).tabulate

noncomputable def PolyProgram.domainWith (t : ℕ) :
    PolyProgram (Fin t × TableInput t) (List (Fin t → ℕ))
      (fun x => (Complexity.choiceWithWords x.2).1 x.1) := by
  let Q : PolyProgram (Fin t × TableInput t) ((Fin t → BitFormula) × Fin t)
      (fun x => (x.2.1,x.1)) :=
    .expr (.pair TExpr.input.right.left TExpr.input.left) (by intro x; rfl)
  let W : PolyProgram (Fin t × TableInput t) (List (List Bool)) (fun x => x.2.2.2) :=
    .expr TExpr.input.right.right.right (by intro x; rfl)
  let D := (W.pair (Q.comp (PolyProgram.groupAt t))).comp PolyProgram.satisfyingWith
  exact ((D.pair (PolyProgram.id (Fin t × TableInput t))).comp (PolyProgram.rowKeyWith t).mapWith).congr
    (by intro x; rfl)

noncomputable def PolyProgram.choiceWithWords (t : ℕ) : PolyProgram (TableInput t) (ChoiceData t)
    Complexity.choiceWithWords := by
  let Q := (PolyProgram.domainWith t).tabulate
  let W : PolyProgram (TableInput t) (List (List Bool)) (fun x => x.2.2) :=
    .expr TExpr.input.right.right (by intro x; rfl)
  let B := W.comp (PolyProgram.length (List Bool))
  let constPair : PolyProgram (Fin t × (Fin t × ℕ)) ℕ (fun x => x.2.2) :=
    .expr TExpr.input.right.right (by intro x; rfl)
  let C := constPair.tabulate.tabulate
  exact (Q.pair (B.comp C)).congr (by intro x; rfl)

end ParityWL.Complexity

end OAI
