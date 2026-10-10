import Mathlib
import OAI.Combinatorics.ThinTrees.Arithmetic.ArraySums
import OAI.Combinatorics.ThinTrees.Pencil.PointPrograms
import OAI.Combinatorics.ThinTrees.Pencil.RationalAffineEval

namespace OAI

/-! Scalar constraint realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

private theorem scalar_poly_pointField (k : ℕ) : PolyTime (pointParams.then (paramsField k)) := by
  apply poly_then

def scalarValue (a : Point) (b : ScalarBlock a.p.graph.n a.p.graph.m) : ℚ :=
  Affine.rat a.v (scalarForms a.p.graph.G a.p.κ a.p.t a.p.q a.p.ε a.p.u b)

def scalarTriple : Realizes tripleCode ratCode (fun p => scalarValue p.1 (.inl p.2)) :=
  (tripleDistinct.ite tripleCoordinate (constant tripleCode ratCode 0)).congr (by
    intro p
    simp only [decide_eq_true_eq,scalarValue,scalarForms]
    split_ifs <;> simp)
instance poly_scalarTriple : PolyTime scalarTriple := by unfold scalarTriple;infer_instance

abbrev edgeScalarEquiv := prodEquiv (fun _ : Point => Equiv.refl (Fin 7)) eEquiv
abbrev edgeScalarCode := indexedCode pointCode edgeScalarEquiv
abbrev esPoint := indexedFirst (ea:=pointCode) edgeScalarEquiv
abbrev esP := (indexedProductLeft (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 7))
  eEquiv pointM).then (indexedIndex (fun _ : Point => Equiv.refl (Fin 7)))
abbrev esEdge := indexedProductRight (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 7)) eEquiv pointM
abbrev esE := esEdge.then (indexedIndex eEquiv)
private theorem poly_esE : PolyTime esE := by
  unfold esE
  apply poly_then

def esY := edgeCoord 0 esPoint (fun p => p.2.2) esE
def esZ := edgeCoord 1 esPoint (fun p => p.2.2) esE
def esX := edgeCoord 2 esPoint (fun p => p.2.2) esE
def esU := storedU esPoint (fun p => p.2.2) esE
instance poly_esY : PolyTime esY := by
  unfold esY
  refine @poly_edgeCoord _ _ _ _ _ _ _ ?_ poly_esE
  infer_instance
instance poly_esZ : PolyTime esZ := by
  unfold esZ
  refine @poly_edgeCoord _ _ _ _ _ _ _ ?_ poly_esE
  infer_instance
instance poly_esX : PolyTime esX := by
  unfold esX
  refine @poly_edgeCoord _ _ _ _ _ _ _ ?_ poly_esE
  infer_instance
instance poly_esU : PolyTime esU := by
  unfold esU
  refine @poly_storedU _ _ _ _ _ _ ?_ poly_esE
  infer_instance
abbrev esK := esPoint.then pointK
abbrev esT := esPoint.then pointT

def esActive := (constant edgeScalarCode ratCode 0).lt esU
instance poly_esActive : PolyTime esActive := by unfold esActive;infer_instance

def esCapacityRate : Realizes edgeScalarCode ratCode (fun a =>
    if 0<a.1.p.u a.2.2 then a.1.p.κ+a.1.p.u a.2.2-a.1.v (edgeIndex 1 a.2.2)+
      a.1.p.t*(5*a.1.v (edgeIndex 0 a.2.2)-4) else 0) :=
  let c (q : ℚ) := constant edgeScalarCode ratCode q
  (esActive.ite (((esK.add esU).sub esZ).add (esT.mul (((c 5).mul esY).sub (c 4))))
    (c 0)).congr (by intro a;simp)
instance poly_esCapacityRate : PolyTime esCapacityRate := by
  have hk : PolyTime pointK := scalar_poly_pointField 1
  have : PolyTime esK := by unfold esK; apply poly_then
  have ht : PolyTime pointT := scalar_poly_pointField 2
  have : PolyTime esT := by unfold esT; apply poly_then
  unfold esCapacityRate;infer_instance

def esCapacity : Realizes edgeScalarCode ratCode (fun a =>
    if 0<a.1.p.u a.2.2 then a.1.v (edgeIndex 1 a.2.2) else a.1.p.κ) :=
  (esActive.ite esZ esK).congr (by intro a;simp)
instance poly_esCapacity : PolyTime esCapacity := by
  have hk : PolyTime pointK := scalar_poly_pointField 1
  have : PolyTime esK := by unfold esK; apply poly_then
  unfold esCapacity
  apply poly_congr

def scalarEdge : Realizes edgeScalarCode ratCode
    (fun a => scalarValue a.1 (.inr (.inl a.2))) :=
  (select7 esP esY ((constant _ ratCode 1).sub esY) esZ
    ((esK.add (constant _ ratCode 1)).sub esZ) esCapacityRate esX (esCapacity.sub esX)).congr (by
      rintro ⟨a,p,e⟩
      change ![a.v (edgeIndex 0 e),1-a.v (edgeIndex 0 e),a.v (edgeIndex 1 e),
        a.p.κ+1-a.v (edgeIndex 1 e),
        if 0<a.p.u e then a.p.κ+a.p.u e-a.v (edgeIndex 1 e)+a.p.t*(5*a.v (edgeIndex 0 e)-4) else 0,
        a.v (edgeIndex 2 e),(if 0<a.p.u e then a.v (edgeIndex 1 e) else a.p.κ)-a.v (edgeIndex 2 e)] p
          =scalarValue a (.inr (.inl (p,e)))
      fin_cases p <;> by_cases hu : 0<a.p.u e <;> simp [scalarValue,scalarForms,capacityForm,hu])
instance poly_scalarEdge : PolyTime scalarEdge := by
  have : PolyTime esP := by infer_instance
  have hk : PolyTime pointK := scalar_poly_pointField 1
  have : PolyTime esK := by unfold esK; apply poly_then
  unfold scalarEdge;infer_instance

abbrev rootEdgeEquiv := prodEquiv vEquiv eEquiv
abbrev rootEdgeCode := indexedCode pointCode rootEdgeEquiv
abbrev rePoint := indexedFirst (ea:=pointCode) rootEdgeEquiv
abbrev reR := (indexedProductLeft (ea:=pointCode) vEquiv eEquiv pointM).then (indexedIndex vEquiv)
abbrev reE := (indexedProductRight (ea:=pointCode) vEquiv eEquiv pointM).then (indexedIndex eEquiv)
private theorem poly_reR : PolyTime reR := by
  unfold reR
  apply poly_then

private theorem poly_reE : PolyTime reE := by
  unfold reE
  apply poly_then

def reA := flowCoord 0 rePoint (fun a => a.2.1) (fun a => a.2.2) reR reE
def reB := flowCoord 1 rePoint (fun a => a.2.1) (fun a => a.2.2) reR reE
def reX := edgeCoord 2 rePoint (fun a => a.2.2) reE
instance poly_reA : PolyTime reA := by
  unfold reA
  refine @poly_flowCoord _ _ _ _ _ _ _ _ _ ?_ poly_reR poly_reE
  infer_instance
instance poly_reB : PolyTime reB := by
  unfold reB
  refine @poly_flowCoord _ _ _ _ _ _ _ _ _ ?_ poly_reR poly_reE
  infer_instance
instance poly_reX : PolyTime reX := by
  unfold reX
  refine @poly_edgeCoord _ _ _ _ _ _ _ ?_ poly_reE
  infer_instance

abbrev flowScalarEquiv := prodEquiv (fun _ : Point => Equiv.refl (Fin 3)) rootEdgeEquiv
abbrev flowScalarCode := indexedCode pointCode flowScalarEquiv
abbrev fsRE := indexedProductRight (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 3)) rootEdgeEquiv
  (pointN.nmul pointM)
abbrev fsP := (indexedProductLeft (ea:=pointCode) (fun _ : Point => Equiv.refl (Fin 3)) rootEdgeEquiv
  (pointN.nmul pointM)).then (indexedIndex (fun _ : Point => Equiv.refl (Fin 3)))

def scalarFlow : Realizes flowScalarCode ratCode
    (fun a => scalarValue a.1 (.inr (.inr (.inl a.2)))) :=
  (select3 fsP (fsRE.then reA) (fsRE.then reB)
    (((fsRE.then reA).add (fsRE.then reB)).sub (fsRE.then reX))).congr (by
      rintro ⟨a,p,r,e⟩
      change ![a.v (flowIndex 0 r e),a.v (flowIndex 1 r e),
        a.v (flowIndex 0 r e)+a.v (flowIndex 1 r e)-a.v (edgeIndex 2 e)] p = _
      fin_cases p <;> simp [scalarValue,scalarForms])
instance poly_scalarFlow : PolyTime scalarFlow := by
  have : PolyTime fsP := by infer_instance
  have : PolyTime fsRE := by infer_instance
  unfold scalarFlow;infer_instance

abbrev budgetCode := indexedCode pointCode pairEquiv
abbrev bsPoint := indexedFirst (ea:=pointCode) pairEquiv
abbrev bsR := pairHead.then (indexedIndex vEquiv)
abbrev bsV := pairTail.then (indexedIndex vEquiv)
abbrev budgetEdgeCode := finFamilyCode budgetCode (fun a => a.1.p.graph.m)
abbrev beBudget : Realizes budgetEdgeCode budgetCode (fun a => a.1) := familyFirst
abbrev beE : Realizes budgetEdgeCode natCode (fun a => a.2.val) := familyIndex
abbrev bePoint := beBudget.then bsPoint
abbrev beR := beBudget.then bsR
abbrev beV := beBudget.then bsV
abbrev beGraphEdge := graphEdge bePoint (fun a => a.2) beE
def beA := flowCoord 0 bePoint (fun a => a.1.2.1) (fun a => a.2) beR beE
def beB := flowCoord 1 bePoint (fun a => a.1.2.1) (fun a => a.2) beR beE
instance poly_beA : PolyTime beA := by
  have hr : PolyTime beR := by infer_instance
  unfold beA
  refine @poly_flowCoord _ _ _ _ _ _ _ _ _ ?_ hr ?_
  all_goals infer_instance
instance poly_beB : PolyTime beB := by
  have hr : PolyTime beR := by infer_instance
  unfold beB
  refine @poly_flowCoord _ _ _ _ _ _ _ _ _ ?_ hr ?_
  all_goals infer_instance

def budgetEdge : Realizes budgetEdgeCode ratCode (fun a =>
    (if a.1.1.p.graph.G.left a.2=a.1.2.2 then a.1.1.v (flowIndex 0 a.1.2.1 a.2) else 0)+
    (if a.1.1.p.graph.G.right a.2=a.1.2.2 then a.1.1.v (flowIndex 1 a.1.2.1 a.2) else 0)) :=
  ((((beGraphEdge.then GraphStack.edgeLeft).finEq beV).ite beA (constant _ ratCode 0)).add
    (((beGraphEdge.then GraphStack.edgeRight).finEq beV).ite beB (constant _ ratCode 0))).congr
      (by
        intro a
        change ((if decide (a.1.1.p.graph.G.left a.2 = a.1.2.2) = true then
          a.1.1.v (flowIndex 0 a.1.2.1 a.2) else 0) +
          (if decide (a.1.1.p.graph.G.right a.2 = a.1.2.2) = true then
          a.1.1.v (flowIndex 1 a.1.2.1 a.2) else 0)) = _
        simp only [decide_eq_true_eq])
instance poly_budgetEdge : PolyTime budgetEdge := by
  have : PolyTime beGraphEdge := by infer_instance
  have : PolyTime beV := by infer_instance
  unfold budgetEdge;infer_instance

def budgetIncoming := budgetEdge.sumFin (n:=fun a : Σ b : Point,Fin b.p.graph.n × Fin b.p.graph.n => a.1.p.graph.m)
  (f:=fun a e => (if a.1.p.graph.G.left e=a.2.2 then a.1.v (flowIndex 0 a.2.1 e) else 0)+
    (if a.1.p.graph.G.right e=a.2.2 then a.1.v (flowIndex 1 a.2.1 e) else 0)) (bsPoint.then pointM)
instance poly_budgetIncoming : PolyTime budgetIncoming := by unfold budgetIncoming;infer_instance

def scalarBudget : Realizes budgetCode ratCode
    (fun a => scalarValue a.1 (.inr (.inr (.inr (.inl a.2))))) :=
  ((((bsV.finEq bsR).ite (bsPoint.then pointE) (bsPoint.then pointQ)).sub budgetIncoming)).congr (by
    rintro ⟨a,r,v⟩
    simp only [scalarValue,scalarForms,Affine.rat_sub,Affine.rat_cst,Affine.rat_sum,Affine.rat_add,
      decide_eq_true_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp)
instance poly_scalarBudget : PolyTime scalarBudget := by
  have : PolyTime bsV := by infer_instance
  have : PolyTime bsR := by infer_instance
  have hq : PolyTime pointQ := scalar_poly_pointField 3
  have he : PolyTime pointE := scalar_poly_pointField 4
  unfold scalarBudget
  apply poly_congr

abbrev xePoint : Realizes (finFamilyCode pointCode (fun a => a.p.graph.m)) pointCode (fun a => a.1) := familyFirst
abbrev xeE : Realizes (finFamilyCode pointCode (fun a => a.p.graph.m)) natCode (fun a => a.2.val) := familyIndex
def edgeTotal := (edgeCoord 2 xePoint (fun a => a.2) xeE).sumFin (n:=fun a : Point => a.p.graph.m)
  (f:=fun a e => a.v (edgeIndex 2 e)) pointM
instance poly_edgeTotal : PolyTime edgeTotal := by unfold edgeTotal;infer_instance

def scalarTotalBase : Realizes pointCode ratCode (fun a => scalarValue a (.inr (.inr (.inr (.inr 0))))) :=
  (edgeTotal.sub ((pointQ.mul ((pointN.then natToRat).sub (constant _ ratCode 1))).sub pointE)).congr (by
    intro a
    simp only [scalarValue,scalarForms,Affine.rat_sub,Affine.rat_cst,Affine.rat_sum,Affine.rat_coord])
instance poly_scalarTotalBase : PolyTime scalarTotalBase := by
  have hq : PolyTime pointQ := scalar_poly_pointField 3
  have he : PolyTime pointE := scalar_poly_pointField 4
  unfold scalarTotalBase
  apply poly_congr

def scalarTotal : Realizes (indexedCode pointCode (fun _ : Point => Equiv.refl (Fin 1))) ratCode
    (fun a => scalarValue a.1 (.inr (.inr (.inr (.inr a.2))))) :=
  ((indexedFirst (fun _ : Point => Equiv.refl (Fin 1))).then scalarTotalBase).congr (fun _ => rfl)
instance poly_scalarTotal : PolyTime scalarTotal := by unfold scalarTotal; apply poly_congr

abbrev scalarEquiv := sumEquiv tripleEquiv (sumEquiv edgeScalarEquiv
  (sumEquiv flowScalarEquiv (sumEquiv pairEquiv (fun _ : Point => Equiv.refl (Fin 1)))))
abbrev scalarCode := indexedCode pointCode scalarEquiv

def scalarConstraints : Realizes scalarCode ratCode (fun a => scalarValue a.1 a.2) :=
  (scalarTriple.sumCases (scalarEdge.sumCases (scalarFlow.sumCases
    (scalarBudget.sumCases scalarTotal (pointN.nmul pointN))
      ((constant _ natCode 3).nmul (pointN.nmul pointM)))
      ((constant _ natCode 7).nmul pointM)) (pointN.nmul (pointN.nmul pointN))).congr (by
        rintro ⟨a,b⟩
        rcases b with t | b
        · rfl
        rcases b with e | b
        · rfl
        rcases b with f | b
        · rfl
        rcases b with v | b <;> rfl)
instance poly_scalarConstraints : PolyTime scalarConstraints := by unfold scalarConstraints;infer_instance

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
