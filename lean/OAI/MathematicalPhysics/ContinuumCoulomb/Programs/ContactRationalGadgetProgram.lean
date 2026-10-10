import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactRationalGadget

namespace OAI

/-! Literal polynomial-time computation of the twenty rational gadget
positions, including the two exact outer endpoints. -/

namespace ContinuumCoulomb.ContactRationalGadget
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool :=
  prodCode unaryCode (prodCode Procedure.boolCode
    (prodCode ratCode (prodCode (listCode ratCode) (listCode ratCode))))

def pointCode : (ℚ × ℚ) → List Bool := prodCode ratCode ratCode

noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first unaryCode _

noncomputable opaque restProgram : Procedure inputCode
    (prodCode Procedure.boolCode (prodCode ratCode (prodCode (listCode ratCode) (listCode ratCode))))
      Prod.snd := Procedure.second unaryCode _

noncomputable opaque signProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.1) :=
  (Procedure.first Procedure.boolCode _).comp restProgram

noncomputable opaque dataProgram : Procedure inputCode
    (prodCode ratCode (prodCode (listCode ratCode) (listCode ratCode))) (fun x => x.2.2) :=
  (Procedure.second Procedure.boolCode _).comp restProgram

noncomputable opaque centralProgram : Procedure inputCode ratCode (fun x => x.2.2.1) :=
  (Procedure.first ratCode _).comp dataProgram

noncomputable opaque listsProgram : Procedure inputCode
    (prodCode (listCode ratCode) (listCode ratCode)) (fun x => x.2.2.2) :=
  (Procedure.second ratCode _).comp dataProgram

noncomputable opaque leftListProgram : Procedure inputCode (listCode ratCode)
    (fun x => x.2.2.2.1) := (Procedure.first (listCode ratCode) (listCode ratCode)).comp listsProgram

noncomputable opaque rightListProgram : Procedure inputCode (listCode ratCode)
    (fun x => x.2.2.2.2) := (Procedure.second (listCode ratCode) (listCode ratCode)).comp listsProgram

noncomputable opaque positiveSpanProgram : Procedure inputCode ratCode
    (fun x => (17 - x.2.2.1) / 2) :=
  (Procedure.ratMul.comp
    ((Procedure.constant inputCode ratCode (1 / 2)).pair
      (Procedure.ratSub.comp ((Procedure.constant inputCode ratCode 17).pair centralProgram)))).congrFun
        (by intro x; simp only [Function.comp_apply]; ring)

noncomputable opaque positiveOriginProgram : Procedure inputCode ratCode
    (fun x => (17 + x.2.2.1) / 2) :=
  (Procedure.ratMul.comp
    ((Procedure.constant inputCode ratCode (1 / 2)).pair
      (Procedure.ratAdd.comp ((Procedure.constant inputCode ratCode 17).pair centralProgram)))).congrFun
        (by intro x; simp only [Function.comp_apply]; ring)

noncomputable opaque spanProgram : Procedure inputCode ratCode
    (fun x => span x.2.1 x.2.2.1) :=
  Procedure.conditional signProgram (Procedure.constant inputCode ratCode (17 / 2)) positiveSpanProgram

noncomputable opaque originProgram : Procedure inputCode ratCode
    (fun x => origin x.2.1 x.2.2.1) :=
  Procedure.conditional signProgram (Procedure.constant inputCode ratCode (17 / 2)) positiveOriginProgram

noncomputable opaque leftEnvironmentProgram : Procedure inputCode ContactHeightEvaluation.environmentCode
    leftEnvironment := precisionProgram.pair (leftListProgram.pair spanProgram)

noncomputable opaque rightEnvironmentProgram : Procedure inputCode ContactHeightEvaluation.environmentCode
    rightEnvironment := precisionProgram.pair (rightListProgram.pair spanProgram)

noncomputable opaque leftVertexProgram (k : ℕ) : Procedure inputCode pointCode
    (fun x => ContactHeightEvaluation.closedVertex (leftEnvironment x) k) :=
  (ContactHeightEvaluation.closedVertexProgram k).comp leftEnvironmentProgram

noncomputable opaque rightVertexProgram (k : ℕ) : Procedure inputCode pointCode
    (fun x => ContactHeightEvaluation.closedVertex (rightEnvironment x) k) :=
  (ContactHeightEvaluation.closedVertexProgram k).comp rightEnvironmentProgram

noncomputable opaque rightShiftProgram (k : ℕ) : Procedure inputCode pointCode
    (fun x => (origin x.2.1 x.2.2.1 +
      (ContactHeightEvaluation.closedVertex (rightEnvironment x) k).1,
        (ContactHeightEvaluation.closedVertex (rightEnvironment x) k).2)) := by
  let qx := (Procedure.first ratCode ratCode).comp (rightVertexProgram k)
  let qy := (Procedure.second ratCode ratCode).comp (rightVertexProgram k)
  exact (Procedure.ratAdd.comp (originProgram.pair qx)).pair qy

noncomputable opaque sideProgram : Procedure inputCode pointCode
    (fun x => if x.2.1 then (17 / 2, x.2.2.1) else (origin x.2.1 x.2.2.1, 0)) :=
  Procedure.conditional signProgram
    ((Procedure.constant inputCode ratCode (17 / 2)).pair centralProgram)
    (originProgram.pair (Procedure.constant inputCode ratCode 0))

noncomputable def positionProgram : (s : ContactGadgetSite) →
    Procedure inputCode pointCode (fun x => position x s)
  | Sum.inl k => leftVertexProgram k.val
  | Sum.inr (Sum.inl k) => rightShiftProgram (k.val + 1)
  | Sum.inr (Sum.inr _) => sideProgram

noncomputable def pointListProgram : (ss : List ContactGadgetSite) →
    Procedure inputCode (listCode pointCode) (fun x => ss.map (position x))
  | [] => (Procedure.constant inputCode (listCode pointCode) []).congrFun (by intro x; rfl)
  | s :: ss => ((Procedure.listCons pointCode).comp
      ((positionProgram s).pair (pointListProgram ss))).congrFun (by intro x; rfl)

def sites : List ContactGadgetSite :=
  (List.ofFn (fun k : Fin 10 => Sum.inl k)) ++
    (List.ofFn (fun k : Fin 9 => Sum.inr (Sum.inl k))) ++ [contactGadgetSide]

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode (listCode pointCode)
    (fun x => sites.map (position x)) := (pointListProgram sites).toTM2

end ContinuumCoulomb.ContactRationalGadget

end OAI
