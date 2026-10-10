import OAI.Combinatorics.ParityLifts.UniformGraphs

namespace OAI

namespace ParityWL.Complexity

noncomputable def PolyProgram.runtimeGoodFlower (α : Type) [TreeCodec α] [DecidableEq α] (p q : ℕ) :
    PolyProgram (FlowerRecord α × (ℕ × ClauseList α)) Bool
      (fun x => @decide (GoodFlower x.2.2 p q x.2.1 x.1) (Classical.propDecidable _)) := by
  classical
  let core : PolyProgram (FlowerRecord α × (ℕ × ClauseList α)) (List α) (fun x => x.1.1) :=
    .expr TExpr.input.left.left (by intro x; rfl)
  let petals : PolyProgram (FlowerRecord α × (ℕ × ClauseList α)) (ClauseList α) (fun x => x.1.2) :=
    .expr TExpr.input.left.right (by intro x; rfl)
  let h : PolyProgram (FlowerRecord α × (ℕ × ClauseList α)) ℕ (fun x => x.2.1) :=
    .expr TExpr.input.right.left (by intro x; rfl)
  let input : PolyProgram (FlowerRecord α × (ℕ × ClauseList α)) (FlowerRecord α × ClauseList α)
      (fun x => (x.1,x.2.2)) := .expr (.pair TExpr.input.left TExpr.input.right.right) (by intro x; rfl)
  let cp := core.comp (PolyProgram.cardEq α p)
  let hp := ((petals.comp (PolyProgram.cnfCard α)).pair h).comp (PolyProgram.equal ℕ)
  let qp := petals.comp (PolyProgram.cardEq α q).all
  let apart := (petals.pair core).comp ((PolyProgram.swap (List α) (List α)).comp (PolyProgram.clauseDisjoint α)).allWith
  let pp := petals.comp (PolyProgram.petalsApart α)
  let H := input.comp (PolyProgram.flowerCover α)
  exact (cp.andOn (hp.andOn (qp.andOn (apart.andOn (pp.andOn H))))).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    simp only [Function.comp_def,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,GoodFlower])

noncomputable def ParamPolyProgram.flowerCandidates (α : Type) [TreeCodec α] [DecidableEq α] (p : ℕ) :
    ParamPolyProgram ℕ (ClauseList α) (List (FlowerRecord α)) (fun h F => Complexity.flowerCandidates F p h) := by
  let cores : ParamPolyProgram ℕ (ClauseList α) (List (List α)) (fun _ F => Complexity.allTuples p F.flatten) :=
    .lift ((PolyProgram.flatten α).comp (PolyProgram.allTuples α p))
  let clauses := ParamPolyProgram.allTuples (List α)
  let petalMap := (PolyProgram.clauseDiff α).mapWith
  let cell := (PolyProgram.fst (List α) (ClauseList α)).pair
    ((PolyProgram.swap (List α) (ClauseList α)).comp petalMap)
  let cells := (PolyProgram.swap (List α) (List (ClauseList α))).comp
    ((PolyProgram.swap (ClauseList α) (List α)).comp cell).mapWith
  exact (((cores.pair clauses).post cells.mapWith).post (PolyProgram.flatten (FlowerRecord α))).congr (by
    intro h F
    simp only [Complexity.flowerCandidates,Function.comp_def,List.flatMap_def])

noncomputable def ParamPolyProgram.flowerList (α : Type) [TreeCodec α] [DecidableEq α] (p q : ℕ) :
    ParamPolyProgram ℕ (ClauseList α) (List (FlowerRecord α)) (fun h F => Complexity.flowerList F p q h) := by
  let rest : ParamPolyProgram ℕ (ClauseList α) (ℕ × ClauseList α) (fun h F => (h,F)) :=
    .ofPoly (f := fun h F => (h,F)) (PolyProgram.id _)
  exact (((ParamPolyProgram.flowerCandidates α p).pair rest).post
    (PolyProgram.runtimeGoodFlower α p q).filterWith).congr (by intro h F; rfl)

noncomputable def ParamPolyProgram.sparseStep (α : Type) [TreeCodec α] [DecidableEq α] :
    ParamPolyProgram ℕ (ClauseList α) (SparseResult α) (fun r F => Complexity.sparseStep r F) := by
  let square := ((PolyProgram.id ℕ).pair (PolyProgram.id ℕ)).comp PolyProgram.natMul
  let fourth := square.comp square
  let L₁ := (ParamPolyProgram.flowerList α 1 1).reindex square
  let L₂ := (ParamPolyProgram.flowerList α 2 1).reindex fourth
  let L₃ := (ParamPolyProgram.flowerList α 1 2).reindex fourth
  let I : ParamPolyProgram ℕ (ClauseList α) (ClauseList α) (fun _ F => F) := .lift (PolyProgram.id _)
  let done : PolyProgram (ClauseList α) (SparseResult α) (fun F => (true,F,F)) :=
    .expr (.pair (.const (boolTree true)) (.pair .input .input)) (by intro x; rfl)
  let B₁ := (I.pair (L₁.post (PolyProgram.head (FlowerRecord α) ([],[])))).post (PolyProgram.sparseBranch α)
  let B₂ := (I.pair (L₂.post (PolyProgram.head (FlowerRecord α) ([],[])))).post (PolyProgram.sparseBranch α)
  let B₃ := (I.pair (L₃.post (PolyProgram.head (FlowerRecord α) ([],[])))).post (PolyProgram.sparseBranch α)
  let test := PolyProgram.null (FlowerRecord α)
  exact ((L₁.post test).ite ((L₂.post test).ite ((L₃.post test).ite (.lift done) B₃) B₂) B₁).congr (by
    intro r F
    have h2 : r*r=r^2 := (pow_two r).symm
    have h4 : r^2*r^2=r^4 := by ring
    simp only [Complexity.sparseStep,Function.comp_def,id_eq,h4,h2]
    rfl)

end ParityWL.Complexity

end OAI
