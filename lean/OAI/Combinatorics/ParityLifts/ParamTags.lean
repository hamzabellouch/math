import OAI.Combinatorics.ParityLifts.ParamTables

namespace OAI

namespace ParityWL.Complexity

noncomputable def PolyProgram.roleValid : PolyProgram (RawRole × ℕ) Bool
    (fun x => decide (RoleValid x.2 x.1)) := by
  let a : PolyProgram (RawRole × ℕ) ℕ (fun x => x.1.1) :=
    .expr TExpr.input.left.left (by intro x; rfl)
  let b : PolyProgram (RawRole × ℕ) ℕ (fun x => x.1.2.1) :=
    .expr TExpr.input.left.right.left (by intro x; rfl)
  let c : PolyProgram (RawRole × ℕ) ℕ (fun x => x.1.2.2) :=
    .expr TExpr.input.left.right.right (by intro x; rfl)
  let t := PolyProgram.snd RawRole ℕ
  let h := ((a.eqOn b).andOn (c.eqOn a)).orOn
    (((a.pair b).comp PolyProgram.natLt).andOn
      (((c.eqOn a).comp PolyProgram.not).andOn ((c.eqOn b).comp PolyProgram.not)))
  refine (((a.pair t).comp PolyProgram.natLt).andOn
    (((b.pair t).comp PolyProgram.natLt).andOn (((c.pair t).comp PolyProgram.natLt).andOn h))).congr ?_
  intro x
  apply Bool.eq_iff_iff.mpr
  erw [decide_eq_true_eq]
  simp only [Function.comp_apply,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,
    Bool.not_eq_true',decide_eq_false_iff_not,RoleValid]

noncomputable def PolyProgram.allRoles : PolyProgram ℕ (List RawRole) Complexity.allRoles :=
  (((PolyProgram.range.pair (PolyProgram.range.pair PolyProgram.range |>.comp (PolyProgram.product ℕ ℕ)))
    |>.comp (PolyProgram.product ℕ (ℕ × ℕ))).pair (PolyProgram.id ℕ) |>.comp
      PolyProgram.roleValid.filterWith).congr (by intro x; rfl)

noncomputable def PolyProgram.rawNeighbors : PolyProgram (ℕ × RawRole) (List RawRole)
    (fun x => Complexity.rawNeighbors x.1 x.2) := by
  let Q := (PolyProgram.swap RawRole RawRole).comp PolyProgram.rawAdjacent
  exact ((((PolyProgram.fst ℕ RawRole).comp PolyProgram.allRoles).pair
    (PolyProgram.snd ℕ RawRole)).comp Q.filterWith).congr (by intro x; rfl)

noncomputable def PolyProgram.rawCharge : PolyProgram (Bool × RawRole) ℕ
    (fun x => Complexity.rawCharge x.1 x.2) :=
  (((PolyProgram.fst Bool RawRole).andOn ((PolyProgram.snd Bool RawRole).eqOn
    (PolyProgram.const (0,0,0)))).ite (PolyProgram.const 1) (PolyProgram.const 0)).congr (by intro x; rfl)

noncomputable def TreeProgram.rawTags : TreeProgram (ℕ × Bool) (List RawTag)
    (fun x => Complexity.rawTags x.1 x.2) := by
  let p : PolyProgram (RawRole × (ℕ × Bool)) (ℕ × RawRole) (fun x => (x.2.1,x.1)) :=
    .expr (.pair TExpr.input.right.left TExpr.input.left) (by intro x; rfl)
  let nb := (p.comp PolyProgram.rawNeighbors).program.comp (TreeProgram.sublists RawRole)
  let r : PolyProgram (RawRole × (ℕ × Bool)) (Bool × RawRole) (fun x => (x.2.2,x.1)) :=
    .expr (.pair TExpr.input.right.right TExpr.input.left) (by intro x; rfl)
  let charge := (r.comp PolyProgram.rawCharge).program
  let cond := ((PolyProgram.fst (List RawRole) ℕ).comp (PolyProgram.length RawRole) |>.comp PolyProgram.natModTwo)
    |>.eqOn (PolyProgram.snd (List RawRole) ℕ)
  let good := (nb.pair charge).comp cond.filterWith.program
  let a := TreeProgram.fst RawRole (ℕ × Bool)
  let tag : PolyProgram (List RawRole × RawRole) RawTag (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  let tags := (good.pair a).comp tag.mapWith.program
  let roles := (PolyProgram.fst ℕ Bool).comp PolyProgram.allRoles
  refine (((roles.program.pair (TreeProgram.id (ℕ × Bool))).comp tags.mapWith).comp
    (PolyProgram.flatten RawTag).program).congr ?_
  intro x
  simp only [Complexity.rawTags,Function.comp_apply,List.flatMap_def,id_eq]

noncomputable def TreeProgram.tagPair : TreeProgram ℕ (List RawTag × List RawTag)
    (fun t => (Complexity.rawTags t false,Complexity.rawTags t true)) :=
  (((TreeProgram.id ℕ).pair (TreeProgram.const false)).comp TreeProgram.rawTags).pair
    (((TreeProgram.id ℕ).pair (TreeProgram.const true)).comp TreeProgram.rawTags)

end ParityWL.Complexity

end OAI
