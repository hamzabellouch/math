import OAI.Combinatorics.ParityLifts.FlowerSearch

namespace OAI

namespace ParityWL.Complexity

def PolyProgram.swap (α β : Type) [TreeCodec α] [TreeCodec β] :
    PolyProgram (α × β) (β × α) (fun x => (x.2,x.1)) :=
  .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)


noncomputable def PolyProgram.allWith {α γ : Type} [TreeCodec α] [TreeCodec γ]
    {p : α × γ → Bool} (P : PolyProgram (α × γ) Bool p) :
    PolyProgram (List α × γ) Bool (fun x => x.1.all (fun a => p (a,x.2))) :=
  (P.mapWith.comp (PolyProgram.id Bool).all).congr (by intro x; simp only [Function.comp_def,List.all_map,id_eq])

noncomputable def PolyProgram.card (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (List α) ℕ (fun x => x.toFinset.card) := by
  let P := PolyProgram.dedupBy (_root_.id : α → α) (PolyProgram.equal α)
  exact (P.comp (PolyProgram.length α)).congr (by
    intro x
    have h := List.toFinset_card_of_nodup (dedupBy_nodup (_root_.id : α → α) x)
    have he : (Complexity.dedupBy (_root_.id : α → α) x).toFinset=x.toFinset := by
      simpa only [List.map_id] using dedupBy_set (_root_.id : α → α) x
    simpa only [List.map_id,he,Function.comp_def] using h.symm)

noncomputable def PolyProgram.cnfCard (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (ClauseList α) ℕ (fun x => (listCNF x).card) :=
  ((PolyProgram.compactCNF α).comp (PolyProgram.length (List α))).congr (compactCNF_length)

noncomputable def PolyProgram.cardEq (α : Type) [TreeCodec α] [DecidableEq α] (n : ℕ) :
    PolyProgram (List α) Bool (fun x => decide (x.toFinset.card=n)) :=
  (((PolyProgram.card α).pair (PolyProgram.const n)).comp (PolyProgram.equal ℕ))

noncomputable def PolyProgram.petalsApart (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (ClauseList α) Bool (fun xs => decide (∀ P∈xs, ∀ Q∈xs,
      P.toFinset=Q.toFinset ∨ Disjoint P.toFinset Q.toFinset)) := by
  classical
  let R := (((PolyProgram.clauseEqual α).pair (PolyProgram.clauseDisjoint α)).comp PolyProgram.or).allWith
  let S := ((PolyProgram.swap (List α) (ClauseList α)).comp R).allWith
  exact (((PolyProgram.id (ClauseList α)).pair (PolyProgram.id (ClauseList α))).comp S).congr (by
    intro xs
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_def,id_eq,List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq]
    constructor <;> intro h P hP Q hQ <;> exact h Q hQ P hP)

noncomputable def PolyProgram.clauseMember (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (List α × ClauseList α) Bool (fun x => decide (x.1.toFinset∈listCNF x.2)) := by
  let sw : PolyProgram (List α × ClauseList α) (ClauseList α × List α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  exact (sw.comp ((PolyProgram.clauseEqual α).mapWith.comp (PolyProgram.id Bool).any)).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_def,List.any_map,id_eq,List.any_eq_true,decide_eq_true_eq,mem_listCNF])

noncomputable def PolyProgram.flowerCover (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (FlowerRecord α × ClauseList α) Bool (fun x => decide (∀ P∈x.1.2,
      x.1.1.toFinset∪P.toFinset∈listCNF x.2)) := by
  classical
  let pa : PolyProgram (List α × (List α × ClauseList α)) (List α × List α) (fun x => (x.2.1,x.1)) :=
    .expr (.pair TExpr.input.right.left TExpr.input.left) (by intro x; rfl)
  let fs : PolyProgram (List α × (List α × ClauseList α)) (ClauseList α) (fun x => x.2.2) :=
    .expr TExpr.input.right.right (by intro x; rfl)
  let P := (((pa.comp (PolyProgram.append α)).pair fs).comp (PolyProgram.clauseMember α)).allWith
  let sw : PolyProgram (FlowerRecord α × ClauseList α) (ClauseList α × (List α × ClauseList α))
      (fun x => (x.1.2,(x.1.1,x.2))) :=
    .expr (.pair TExpr.input.left.right (.pair TExpr.input.left.left TExpr.input.right)) (by intro x; rfl)
  exact (sw.comp P).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_def,List.all_eq_true,decide_eq_true_eq,List.toFinset_append])

noncomputable def PolyProgram.goodFlower (α : Type) [TreeCodec α] [DecidableEq α] (p q h : ℕ) :
    PolyProgram (FlowerRecord α × ClauseList α) Bool (fun x => @decide (GoodFlower x.2 p q h x.1) (Classical.propDecidable _)) := by
  classical
  let core : PolyProgram (FlowerRecord α × ClauseList α) (List α) (fun x => x.1.1) :=
    .expr TExpr.input.left.left (by intro x; rfl)
  let petals : PolyProgram (FlowerRecord α × ClauseList α) (ClauseList α) (fun x => x.1.2) :=
    .expr TExpr.input.left.right (by intro x; rfl)
  let cp := core.comp (PolyProgram.cardEq α p)
  let hp := ((petals.comp (PolyProgram.cnfCard α)).pair (PolyProgram.const h)).comp (PolyProgram.equal ℕ)
  let qp := petals.comp (PolyProgram.cardEq α q).all
  let sw : PolyProgram (List α × List α) (List α × List α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  let apart := (petals.pair core).comp (sw.comp (PolyProgram.clauseDisjoint α)).allWith
  let pp := petals.comp (PolyProgram.petalsApart α)
  let H := (PolyProgram.flowerCover α)
  let H' := (pp.pair H).comp PolyProgram.and
  let H'' := (apart.pair H').comp PolyProgram.and
  let H''' := (qp.pair H'').comp PolyProgram.and
  let H'''' := (hp.pair H''').comp PolyProgram.and
  exact ((cp.pair H'''').comp PolyProgram.and).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    simp only [Function.comp_def,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,GoodFlower])

noncomputable def PolyProgram.flowerCandidates (α : Type) [TreeCodec α] [DecidableEq α] (p h : ℕ) :
    PolyProgram (ClauseList α) (List (FlowerRecord α)) (fun F => Complexity.flowerCandidates F p h) := by
  let form := PolyProgram.id (ClauseList α)
  let cores := form.comp ((PolyProgram.flatten α).comp (PolyProgram.allTuples α p))
  let clauses := form.comp (PolyProgram.allTuples (List α) h)
  let petalMap := (PolyProgram.clauseDiff α).mapWith
  let sw : PolyProgram (List α × ClauseList α) (ClauseList α × List α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  let cell := (PolyProgram.fst (List α) (ClauseList α)).pair (sw.comp petalMap)
  let sw2 : PolyProgram (ClauseList α × List α) (List α × ClauseList α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  let cells := (PolyProgram.swap (List α) (List (ClauseList α))).comp (sw2.comp cell).mapWith
  exact (((cores.pair clauses).comp cells.mapWith).comp (PolyProgram.flatten (FlowerRecord α))).congr (by
    intro F
    simp only [Complexity.flowerCandidates,Function.comp_def,id_eq,List.flatMap_def])

noncomputable def PolyProgram.flowerList (α : Type) [TreeCodec α] [DecidableEq α] (p q h : ℕ) :
    PolyProgram (ClauseList α) (List (FlowerRecord α)) (fun F => Complexity.flowerList F p q h) :=
  ((((PolyProgram.flowerCandidates α p h).pair (PolyProgram.id (ClauseList α))).comp
    (PolyProgram.goodFlower α p q h).filterWith)).congr (by intro F; rfl)

end ParityWL.Complexity

end OAI
