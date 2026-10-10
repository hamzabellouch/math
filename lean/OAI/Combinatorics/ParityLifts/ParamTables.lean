import OAI.Combinatorics.ParityLifts.UniformTables

namespace OAI

namespace ParityWL.Complexity

abbrev RawKeyInput := List BitFormula × (ℕ × (ℕ × (ℕ × List Bool)))

def PolyProgram.rawGroupAt : PolyProgram (List BitFormula × ℕ) BitFormula
    (fun x => x.1[x.2]?.getD []) :=
  ((PolyProgram.snd (List BitFormula) ℕ).pair (PolyProgram.fst (List BitFormula) ℕ)).comp
    (PolyProgram.getD BitFormula [])

noncomputable def PolyProgram.natMax : PolyProgram (ℕ × ℕ) ℕ (fun x => max x.1 x.2) :=
  (PolyProgram.natLe.ite (PolyProgram.snd ℕ ℕ) (PolyProgram.fst ℕ ℕ)).congr
    (by intro x; simp only [decide_eq_true_eq,max_def])
noncomputable def PolyProgram.rawPairKey : PolyProgram RawKeyInput (List Bool)
    (fun x => Complexity.rawPairKey x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  let Q := PolyProgram.fst (List BitFormula) (ℕ × (ℕ × (ℕ × List Bool)))
  let I : PolyProgram RawKeyInput (ℕ × ℕ) (fun x => (x.2.2.1,x.2.2.2.1)) :=
    .expr (.pair TExpr.input.right.right.left TExpr.input.right.right.right.left) (by intro x; rfl)
  let lo := ((Q.pair (I.comp PolyProgram.natMin)).comp
    PolyProgram.rawGroupAt).comp PolyProgram.names
  let hi := ((Q.pair (I.comp PolyProgram.natMax)).comp
    PolyProgram.rawGroupAt).comp PolyProgram.names
  let own := ((Q.pair (I.comp (PolyProgram.fst ℕ ℕ))).comp
    PolyProgram.rawGroupAt).comp PolyProgram.names
  let bs : PolyProgram RawKeyInput (List Bool) (fun x => x.2.2.2.2) :=
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
  let D : PolyProgram RawKeyInput ℕ (fun x => x.2.1) :=
    .expr TExpr.input.right.left (by intro x; rfl)
  let pad := (((D.pair (lo.comp (PolyProgram.length Name))).comp PolyProgram.natSub).comp PolyProgram.ticks)
  refine ((first.pair pad).comp (PolyProgram.append Bool)).congr ?_
  intro x
  simp only [Function.comp_def, Complexity.rawPairKey, decide_eq_true_eq]


noncomputable def PolyProgram.rawRowKey :
    PolyProgram (List Bool × (ℕ × RawTableInput)) (List ℕ)
      (fun x => Complexity.rawRowKey x.2.2 x.2.1 x.1) := by
  let P : PolyProgram (ℕ × (List Bool × (ℕ × RawTableInput))) RawKeyInput
      (fun x => (x.2.2.2.1,(x.2.2.2.2.1,(x.2.2.1,(x.1,x.2.1))))) :=
    .expr (.pair TExpr.input.right.right.right.left
      (.pair TExpr.input.right.right.right.right.left (.pair TExpr.input.right.right.left
        (.pair TExpr.input.left TExpr.input.right.left)))) (by intro x; rfl)
  let W : PolyProgram (ℕ × (List Bool × (ℕ × RawTableInput))) (List (List Bool))
      (fun x => x.2.2.2.2.2) :=
    .expr TExpr.input.right.right.right.right.right (by intro x; rfl)
  let Q := (W.pair (P.comp PolyProgram.rawPairKey)).comp (PolyProgram.idxOf (List Bool))
  let gs : PolyProgram (List Bool × (ℕ × RawTableInput)) (List BitFormula) (fun x => x.2.2.1) :=
    .expr TExpr.input.right.right.left (by intro x; rfl)
  let rng := gs.comp (PolyProgram.length BitFormula) |>.comp PolyProgram.range
  exact ((rng.pair (PolyProgram.id _)).comp Q.mapWith).congr (by intro x; rfl)

noncomputable def PolyProgram.rawDomain :
    PolyProgram (ℕ × RawTableInput) (List (List ℕ))
      (fun x => Complexity.rawDomain x.2 x.1) := by
  let Q : PolyProgram (ℕ × RawTableInput) (List BitFormula × ℕ)
      (fun x => (x.2.1,x.1)) :=
    .expr (.pair TExpr.input.right.left TExpr.input.left) (by intro x; rfl)
  let W : PolyProgram (ℕ × RawTableInput) (List (List Bool)) (fun x => x.2.2.2) :=
    .expr TExpr.input.right.right.right (by intro x; rfl)
  let D := (W.pair (Q.comp PolyProgram.rawGroupAt)).comp PolyProgram.satisfyingWith
  exact ((D.pair (PolyProgram.id (ℕ × RawTableInput))).comp PolyProgram.rawRowKey.mapWith).congr
    (by intro x; rfl)

noncomputable def PolyProgram.rawChoiceWithWords : PolyProgram RawTableInput RawChoiceData
    Complexity.rawChoiceWithWords := by
  let gs := (PolyProgram.fst (List BitFormula) (ℕ × List (List Bool))).comp
    (PolyProgram.length BitFormula) |>.comp PolyProgram.range
  let Q := (gs.pair (PolyProgram.id _)).comp PolyProgram.rawDomain.mapWith
  let W : PolyProgram RawTableInput (List (List Bool)) (fun x => x.2.2) :=
    .expr TExpr.input.right.right (by intro x; rfl)
  let B := W.comp (PolyProgram.length (List Bool))
  let row := (gs.pair B).comp (PolyProgram.snd ℕ ℕ).mapWith
  exact (Q.pair ((gs.pair row).comp (PolyProgram.snd ℕ (List ℕ)).mapWith)).congr
    (by intro x; rfl)

def PolyProgram.runtimeChunkWidth : PolyProgram (ℕ × BitFormula) ℕ
    (fun x => Complexity.chunkWidth x.1 x.2) := by
  let n := (PolyProgram.snd ℕ BitFormula).comp (PolyProgram.length BitClause)
  let t := PolyProgram.fst ℕ BitFormula
  let num := (((n.pair t).comp PolyProgram.natAdd).pair (PolyProgram.const 1)).comp PolyProgram.natSub
  exact (num.pair t).comp PolyProgram.natDiv

noncomputable def PolyProgram.rawGroups : PolyProgram (ℕ × BitFormula) (List BitFormula)
    (fun x => Complexity.rawGroups x.1 x.2) := by
  let i := PolyProgram.fst ℕ (ℕ × BitFormula)
  let w := (PolyProgram.snd ℕ (ℕ × BitFormula)).comp PolyProgram.runtimeChunkWidth
  let F : PolyProgram (ℕ × (ℕ × BitFormula)) BitFormula (fun x => x.2.2) :=
    .expr TExpr.input.right.right (by intro x; rfl)
  let row := (w.pair (((i.pair w).comp PolyProgram.natMul).pair F |>.comp
    (PolyProgram.drop BitClause))).comp (PolyProgram.take BitClause)
  exact ((((PolyProgram.fst ℕ BitFormula).comp PolyProgram.range).pair (PolyProgram.id _)).comp
    row.mapWith).congr (by intro x; rfl)

noncomputable def PolyProgram.rawLeafPrepare : PolyProgram (ℕ × BitFormula) (List BitFormula × ℕ)
    (fun x => (Complexity.rawGroups x.1 x.2,Complexity.leafWords x.1 x.2)) :=
  PolyProgram.rawGroups.pair (((PolyProgram.const 3).pair PolyProgram.runtimeChunkWidth).comp PolyProgram.natMul)

end ParityWL.Complexity

end OAI
