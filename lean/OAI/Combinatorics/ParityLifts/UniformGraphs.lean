import OAI.Combinatorics.ParityLifts.UniformOutput

namespace OAI

namespace ParityWL.Complexity

noncomputable def PolyProgram.eqOn {α β : Type} [TreeCodec α] [TreeCodec β] [DecidableEq β]
    {f g : α → β} (P : PolyProgram α β f) (Q : PolyProgram α β g) :
    PolyProgram α Bool (fun x => decide (f x=g x)) := (P.pair Q).comp (PolyProgram.equal β)

def PolyProgram.andOn {α : Type} [TreeCodec α] {f g : α → Bool}
    (P : PolyProgram α Bool f) (Q : PolyProgram α Bool g) :
    PolyProgram α Bool (fun x => f x && g x) := (P.ite Q (PolyProgram.const false)).congr
      (by intro x; cases f x <;> rfl)

def PolyProgram.orOn {α : Type} [TreeCodec α] {f g : α → Bool}
    (P : PolyProgram α Bool f) (Q : PolyProgram α Bool g) :
    PolyProgram α Bool (fun x => f x || g x) := (P.ite (PolyProgram.const true) Q).congr
      (by intro x; cases f x <;> rfl)

noncomputable def PolyProgram.rawAdjacent : PolyProgram (RawRole × RawRole) Bool
    (fun x => Complexity.rawAdjacent x.1 x.2) := by
  let a : PolyProgram (RawRole × RawRole) ℕ (fun x => x.1.1) := .expr TExpr.input.left.left (by intro x; rfl)
  let b : PolyProgram (RawRole × RawRole) ℕ (fun x => x.1.2.1) := .expr TExpr.input.left.right.left (by intro x; rfl)
  let c : PolyProgram (RawRole × RawRole) ℕ (fun x => x.1.2.2) := .expr TExpr.input.left.right.right (by intro x; rfl)
  let d : PolyProgram (RawRole × RawRole) ℕ (fun x => x.2.1) := .expr TExpr.input.right.left (by intro x; rfl)
  let e : PolyProgram (RawRole × RawRole) ℕ (fun x => x.2.2.1) := .expr TExpr.input.right.right.left (by intro x; rfl)
  let f : PolyProgram (RawRole × RawRole) ℕ (fun x => x.2.2.2) := .expr TExpr.input.right.right.right (by intro x; rfl)
  refine ((a.eqOn b).ite ((d.eqOn e).ite ((a.eqOn d).comp PolyProgram.not)
    ((a.eqOn d).orOn ((a.eqOn e).orOn (a.eqOn f))))
      ((d.eqOn e).ite ((d.eqOn a).orOn ((d.eqOn b).orOn (d.eqOn c))) (PolyProgram.const false))).congr ?_
  intro x
  simp only [Function.comp_apply,decide_eq_true_eq,Complexity.rawAdjacent]
  split <;> split <;> simp [Bool.decide_or,decide_not]

noncomputable def PolyProgram.rawEntry :
    PolyProgram (RawChoiceData × (ℕ × (ℕ × ℕ))) ℕ (fun x => x.1.entry x.2.1 x.2.2.1 x.2.2.2) := by
  let D : PolyProgram (RawChoiceData × (ℕ × (ℕ × ℕ))) (List (List (List ℕ))) (fun x => x.1.1) :=
    .expr TExpr.input.left.left (by intro x; rfl)
  let i : PolyProgram (RawChoiceData × (ℕ × (ℕ × ℕ))) ℕ (fun x => x.2.1) :=
    .expr TExpr.input.right.left (by intro x; rfl)
  let d : PolyProgram (RawChoiceData × (ℕ × (ℕ × ℕ))) ℕ (fun x => x.2.2.1) :=
    .expr TExpr.input.right.right.left (by intro x; rfl)
  let j : PolyProgram (RawChoiceData × (ℕ × (ℕ × ℕ))) ℕ (fun x => x.2.2.2) :=
    .expr TExpr.input.right.right.right (by intro x; rfl)
  exact (j.pair ((d.pair ((i.pair D).comp (PolyProgram.getD (List (List ℕ)) []))).comp
    (PolyProgram.getD (List ℕ) []))).comp (PolyProgram.getD ℕ 0)

noncomputable def PolyProgram.rawBound : PolyProgram (RawChoiceData × (ℕ × ℕ)) ℕ
    (fun x => x.1.bound x.2.1 x.2.2) := by
  let D : PolyProgram (RawChoiceData × (ℕ × ℕ)) (List (List ℕ)) (fun x => x.1.2) :=
    .expr TExpr.input.left.right (by intro x; rfl)
  let ij := PolyProgram.snd RawChoiceData (ℕ × ℕ)
  let lo := ij.comp PolyProgram.natMin
  let i := ij.comp (PolyProgram.fst ℕ ℕ)
  let j := ij.comp (PolyProgram.snd ℕ ℕ)
  let hi := ((i.pair j).comp PolyProgram.natLe).ite j i
  refine (hi.pair ((lo.pair D).comp (PolyProgram.getD (List ℕ) [])) |>.comp (PolyProgram.getD ℕ 0)).congr ?_
  intro x
  change _[if decide (x.2.1≤x.2.2) then x.2.2 else x.2.1]?.getD 0=_
  rw [show (if decide (x.2.1≤x.2.2) then x.2.2 else x.2.1)=max x.2.1 x.2.2 by
    by_cases h : x.2.1≤x.2.2 <;> simp [h,max_def]]
  rfl

noncomputable def PolyProgram.rawLabel : PolyProgram (RawChoiceData × (ℕ × (ℕ × ℕ))) ℕ
    (fun x => x.1.label x.2.1 x.2.2.1 x.2.2.2) := by
  let Q : PolyProgram (RawChoiceData × (ℕ × (ℕ × ℕ))) (RawChoiceData × (ℕ × ℕ))
      (fun x => (x.1,x.2.1,x.2.2.2)) :=
    .expr (.pair TExpr.input.left (.pair TExpr.input.right.left TExpr.input.right.right.right)) (by intro x; rfl)
  exact (PolyProgram.rawEntry.pair (Q.comp PolyProgram.rawBound)).comp PolyProgram.natMin

noncomputable def PolyProgram.rawRoleSize : PolyProgram (RawChoiceData × RawRole) ℕ
    (fun x => x.1.roleSize x.2) := by
  let i : PolyProgram (RawChoiceData × RawRole) ℕ (fun x => x.2.1) :=
    .expr TExpr.input.right.left (by intro x; rfl)
  let j : PolyProgram (RawChoiceData × RawRole) ℕ (fun x => x.2.2.1) :=
    .expr TExpr.input.right.right.left (by intro x; rfl)
  let D : PolyProgram (RawChoiceData × RawRole) (List (List (List ℕ))) (fun x => x.1.1) :=
    .expr TExpr.input.left.left (by intro x; rfl)
  let B : PolyProgram (RawChoiceData × RawRole) (List (List ℕ)) (fun x => x.1.2) :=
    .expr TExpr.input.left.right (by intro x; rfl)
  let nr := (i.pair D |>.comp (PolyProgram.getD (List (List ℕ)) [])).comp (PolyProgram.length (List ℕ))
  let nb := (j.pair (i.pair B |>.comp (PolyProgram.getD (List ℕ) [])) |>.comp
    (PolyProgram.getD ℕ 0)).comp PolyProgram.natSucc
  exact ((i.eqOn j).ite nr nb).congr (by intro x; simp only [Function.comp_apply,decide_eq_true_eq]; rfl)

noncomputable def PolyProgram.rawHelperTest : PolyProgram (RawChoiceData × (RawRole × (ℕ × (ℕ × ℕ)))) Bool
    (fun x => x.1.helperTest x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  let i : PolyProgram (RawChoiceData × (RawRole × (ℕ × (ℕ × ℕ)))) ℕ (fun x => x.2.2.2.1) :=
    .expr TExpr.input.right.right.right.left (by intro x; rfl)
  let a : PolyProgram (RawChoiceData × (RawRole × (ℕ × (ℕ × ℕ)))) ℕ (fun x => x.2.1.1) :=
    .expr TExpr.input.right.left.left (by intro x; rfl)
  let b : PolyProgram (RawChoiceData × (RawRole × (ℕ × (ℕ × ℕ)))) ℕ (fun x => x.2.1.2.1) :=
    .expr TExpr.input.right.left.right.left (by intro x; rfl)
  let c : PolyProgram (RawChoiceData × (RawRole × (ℕ × (ℕ × ℕ)))) ℕ (fun x => x.2.1.2.2) :=
    .expr TExpr.input.right.left.right.right (by intro x; rfl)
  let d : PolyProgram (RawChoiceData × (RawRole × (ℕ × (ℕ × ℕ)))) ℕ (fun x => x.2.2.2.2) :=
    .expr TExpr.input.right.right.right.right (by intro x; rfl)
  let q : PolyProgram (RawChoiceData × (RawRole × (ℕ × (ℕ × ℕ)))) ℕ (fun x => x.2.2.1) :=
    .expr TExpr.input.right.right.left (by intro x; rfl)
  let D := PolyProgram.fst RawChoiceData (RawRole × (ℕ × (ℕ × ℕ)))
  exact ((i.eqOn a).ite (((D.pair (i.pair (d.pair b))).comp PolyProgram.rawLabel).eqOn q)
    ((i.eqOn b).ite (((D.pair (i.pair (d.pair a))).comp PolyProgram.rawLabel).eqOn q)
      (i.eqOn c))).congr (by intro x; simp only [Function.comp_apply,decide_eq_true_eq]; rfl)

noncomputable def PolyProgram.rawBaseTest : PolyProgram (RawChoiceData × (RawVertex × RawVertex)) Bool
    (fun x => x.1.baseTest x.2.1.1.1 x.2.1.2 x.2.2.1.1 x.2.2.2) := by
  let D : PolyProgram (RawChoiceData × (RawVertex × RawVertex)) (RawChoiceData) (fun x => x.1) :=
    .expr TExpr.input.left (by intro x; rfl)
  let a : PolyProgram (RawChoiceData × (RawVertex × RawVertex)) (RawRole) (fun x => x.2.1.1.1) :=
    .expr TExpr.input.right.left.left.left (by intro x; rfl)
  let b : PolyProgram (RawChoiceData × (RawVertex × RawVertex)) (RawRole) (fun x => x.2.2.1.1) :=
    .expr TExpr.input.right.right.left.left (by intro x; rfl)
  let d : PolyProgram (RawChoiceData × (RawVertex × RawVertex)) (ℕ) (fun x => x.2.1.2) :=
    .expr TExpr.input.right.left.right (by intro x; rfl)
  let e : PolyProgram (RawChoiceData × (RawVertex × RawVertex)) (ℕ) (fun x => x.2.2.2) :=
    .expr TExpr.input.right.right.right (by intro x; rfl)
  let a₁ := a.comp (PolyProgram.fst ℕ (ℕ × ℕ))
  let a₂ := a.comp ((PolyProgram.snd ℕ (ℕ × ℕ)).comp (PolyProgram.fst ℕ ℕ))
  let b₁ := b.comp (PolyProgram.fst ℕ (ℕ × ℕ))
  let b₂ := b.comp ((PolyProgram.snd ℕ (ℕ × ℕ)).comp (PolyProgram.fst ℕ ℕ))
  let L := (D.pair (a₁.pair (d.pair b₁))).comp PolyProgram.rawLabel
  let R := (D.pair (b₁.pair (e.pair a₁))).comp PolyProgram.rawLabel
  let H1 := (D.pair (b.pair (e.pair (a₁.pair d)))).comp PolyProgram.rawHelperTest
  let H2 := (D.pair (a.pair (d.pair (b₁.pair e)))).comp PolyProgram.rawHelperTest
  refine ((a₁.eqOn a₂).ite ((b₁.eqOn b₂).ite
    (((a₁.eqOn b₁).comp PolyProgram.not).andOn (L.eqOn R)) H1)
      ((b₁.eqOn b₂).ite H2 (PolyProgram.const false))).congr ?_
  intro x
  simp only [Function.comp_apply,decide_eq_true_eq,RawChoiceData.baseTest,decide_not]

noncomputable def PolyProgram.rawTagTest : PolyProgram (RawTag × RawTag) Bool
    (fun x => Complexity.rawTagTest x.1 x.2) := by
  let a : PolyProgram (RawTag × RawTag) (RawRole) (fun x => x.1.1) :=
    .expr TExpr.input.left.left (by intro x; rfl)
  let as : PolyProgram (RawTag × RawTag) (List RawRole) (fun x => x.1.2) :=
    .expr TExpr.input.left.right (by intro x; rfl)
  let b : PolyProgram (RawTag × RawTag) (RawRole) (fun x => x.2.1) :=
    .expr TExpr.input.right.left (by intro x; rfl)
  let bs : PolyProgram (RawTag × RawTag) (List RawRole) (fun x => x.2.2) :=
    .expr TExpr.input.right.right (by intro x; rfl)
  let A := (b.pair as).comp (PolyProgram.mem RawRole)
  let B := (a.pair bs).comp (PolyProgram.mem RawRole)
  refine ((a.pair b |>.comp PolyProgram.rawAdjacent).andOn (A.eqOn B)).congr ?_
  intro x
  simp only [Function.comp_apply,Complexity.rawTagTest]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,decide_eq_decide]

noncomputable def PolyProgram.rawEdgeTest : PolyProgram (RawChoiceData × (RawVertex × RawVertex)) Bool
    (fun x => Complexity.rawEdgeTest x.1 x.2.1 x.2.2) := by
  let P : PolyProgram (RawChoiceData × (RawVertex × RawVertex)) (RawTag × RawTag)
      (fun x => (x.2.1.1,x.2.2.1)) :=
    .expr (.pair TExpr.input.right.left.left TExpr.input.right.right.left) (by intro x; rfl)
  exact PolyProgram.rawBaseTest.andOn (P.comp PolyProgram.rawTagTest)

noncomputable def PolyProgram.rawVertices : PolyProgram (RawChoiceData × List RawTag) (List RawVertex)
    (fun x => Complexity.rawVertices x.1 x.2) := by
  let R : PolyProgram (RawTag × RawChoiceData) (RawChoiceData × RawRole) (fun x => (x.2,x.1.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left.left) (by intro x; rfl)
  let ns := R.comp PolyProgram.rawRoleSize |>.comp PolyProgram.range
  let swap : PolyProgram (ℕ × RawTag) RawVertex (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  let Q := (ns.pair (PolyProgram.fst RawTag RawChoiceData)).comp swap.mapWith
  let S : PolyProgram (RawChoiceData × List RawTag) (List RawTag × RawChoiceData) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  exact (S.comp Q.mapWith |>.comp (PolyProgram.flatten RawVertex)).congr (by intro x; rfl)

noncomputable def PolyProgram.rawMatrix : PolyProgram (RawChoiceData × List RawTag) (List Bool)
    (fun x => Complexity.rawMatrix x.1 x.2) := by
  let E : PolyProgram (RawVertex × (RawVertex × RawChoiceData)) (RawChoiceData × (RawVertex × RawVertex))
      (fun x => (x.2.2,x.2.1,x.1)) :=
    .expr (.pair TExpr.input.right.right (.pair TExpr.input.right.left TExpr.input.left)) (by intro x; rfl)
  let V : PolyProgram (RawVertex × (RawChoiceData × List RawTag)) (List RawVertex)
      (fun x => Complexity.rawVertices x.2.1 x.2.2) :=
    (PolyProgram.snd RawVertex (RawChoiceData × List RawTag)).comp PolyProgram.rawVertices
  let C : PolyProgram (RawVertex × (RawChoiceData × List RawTag)) (RawVertex × RawChoiceData)
      (fun x => (x.1,x.2.1)) :=
    .expr (.pair TExpr.input.left TExpr.input.right.left) (by intro x; rfl)
  let Q := (V.pair C).comp (E.comp PolyProgram.rawEdgeTest).mapWith
  exact ((PolyProgram.rawVertices.pair (PolyProgram.id (RawChoiceData × List RawTag))).comp Q.mapWith
    |>.comp (PolyProgram.flatten Bool)).congr (by intro x; rfl)

noncomputable def PolyProgram.rawOutput : PolyProgram (RawChoiceData × (List RawTag × List RawTag)) (List Bool)
    (fun x => Complexity.rawOutput x.1 x.2) := by
  let L : PolyProgram (RawChoiceData × (List RawTag × List RawTag)) (RawChoiceData × List RawTag)
      (fun x => (x.1,x.2.1)) :=
    .expr (.pair TExpr.input.left TExpr.input.right.left) (by intro x; rfl)
  let R : PolyProgram (RawChoiceData × (List RawTag × List RawTag)) (RawChoiceData × List RawTag)
      (fun x => (x.1,x.2.2)) :=
    .expr (.pair TExpr.input.left TExpr.input.right.right) (by intro x; rfl)
  let C := L.comp PolyProgram.rawVertices |>.comp (PolyProgram.length RawVertex) |>.comp PolyProgram.encodeNat
  exact ((C.pair (L.comp PolyProgram.rawMatrix) |>.comp (PolyProgram.append Bool)).pair
    (R.comp PolyProgram.rawMatrix) |>.comp (PolyProgram.append Bool)).congr (by intro x; rfl)

end ParityWL.Complexity

end OAI
