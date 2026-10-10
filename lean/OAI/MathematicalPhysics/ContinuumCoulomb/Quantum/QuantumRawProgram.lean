import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawExchange

namespace OAI

/-! Literal polynomial programs for fixed-size physical exchange instructions. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

noncomputable def fixedListProgram {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (m : ℕ) (f : Fin m → α → β) (p : ∀ i, Procedure ea eb (f i)) :
    Procedure ea (listCode eb) (fun x => List.ofFn (fun i => f i x)) := by
  induction m with
  | zero => exact (Procedure.constant ea (listCode eb) []).congrFun (by intro x; simp)
  | succ m ih =>
    exact ((Procedure.listCons eb).comp ((p 0).pair
      (ih (fun i => f i.succ) (fun i => p i.succ)))).congrFun (by
        intro x
        simp only [Function.comp_apply,List.ofFn_succ])

noncomputable def selectAxis {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {flag : α → Bool} {f : Fin 2 → α → β} (test : Procedure ea Procedure.boolCode flag)
    (p : ∀ a, Procedure ea eb (f a)) :
    Procedure ea eb (fun x => f (axis (flag x)) x) :=
  (Procedure.conditional test (p 0) (p 1)).congrFun (by
    intro x
    cases flag x <;> simp [axis])

noncomputable opaque envProgram : Procedure inputCode environmentCode Prod.fst := Procedure.first _ _
noncomputable opaque rawProgram : Procedure inputCode rawCode Prod.snd := Procedure.second _ _
noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first _ _).comp envProgram
noncomputable opaque scaleProgram : Procedure inputCode ratCode (fun x => x.1.2) :=
  (Procedure.second _ _).comp envProgram
noncomputable opaque flagsProgram : Procedure inputCode (prodCode Procedure.boolCode Procedure.boolCode)
    (fun x => x.2.1) := (Procedure.first _ _).comp rawProgram
noncomputable opaque pairFlagProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.1.1) :=
  (Procedure.first _ _).comp flagsProgram
noncomputable opaque fieldFlagProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.1.2) :=
  (Procedure.second _ _).comp flagsProgram
noncomputable opaque dataProgram : Procedure inputCode
    (prodCode (prodCode Nat.bits Nat.bits) (prodCode (prodCode Procedure.boolCode Procedure.boolCode) ratCode))
    (fun x => x.2.2) := (Procedure.second _ _).comp rawProgram
noncomputable opaque sitesProgram : Procedure inputCode (prodCode Nat.bits Nat.bits)
    (fun x => x.2.2.1) := (Procedure.first _ _).comp dataProgram
noncomputable opaque leftProgram : Procedure inputCode Nat.bits (fun x => x.2.2.1.1) :=
  (Procedure.first _ _).comp sitesProgram
noncomputable opaque rightProgram : Procedure inputCode Nat.bits (fun x => x.2.2.1.2) :=
  (Procedure.second _ _).comp sitesProgram
noncomputable opaque axesWeightProgram : Procedure inputCode
    (prodCode (prodCode Procedure.boolCode Procedure.boolCode) ratCode) (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp dataProgram
noncomputable opaque axesProgram : Procedure inputCode (prodCode Procedure.boolCode Procedure.boolCode)
    (fun x => x.2.2.2.1) := (Procedure.first _ _).comp axesWeightProgram
noncomputable opaque axisLeftProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.2.2.1.1) :=
  (Procedure.first _ _).comp axesProgram
noncomputable opaque axisRightProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.2.2.1.2) :=
  (Procedure.second _ _).comp axesProgram
noncomputable opaque weightProgram : Procedure inputCode ratCode (fun x => x.2.2.2.2) :=
  (Procedure.second _ _).comp axesWeightProgram
noncomputable opaque radialProgram : Procedure inputCode radialCode (fun x => (x.1.1,x.2.2.2.2)) :=
  precisionProgram.pair weightProgram
noncomputable opaque crossInputProgram : Procedure inputCode crossCode (fun x => (x.1,x.2.2.2.2)) :=
  envProgram.pair weightProgram

noncomputable opaque baseLeftProgram : Procedure inputCode Nat.bits (fun x => 4*x.2.2.1.1) :=
  Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits 4).pair leftProgram)
noncomputable opaque baseRightProgram : Procedure inputCode Nat.bits (fun x => 4*x.2.2.1.2) :=
  Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits 4).pair rightProgram)

noncomputable opaque shiftedLeftProgram (p : ℕ) : Procedure inputCode Nat.bits (fun x => 4*x.2.2.1.1+p) :=
  Procedure.binaryAdd.comp (baseLeftProgram.pair (Procedure.constant inputCode Nat.bits p))
noncomputable opaque shiftedRightProgram (p : ℕ) : Procedure inputCode Nat.bits (fun x => 4*x.2.2.1.2+p) :=
  Procedure.binaryAdd.comp (baseRightProgram.pair (Procedure.constant inputCode Nat.bits p))

noncomputable opaque fieldCoefficientProgram (e : Fin 3) : Procedure inputCode ratCode
    (fun x => fieldValue x.1.1 (axis x.2.2.2.1.1) x.2.2.2.2 e) :=
  selectAxis axisLeftProgram (fun a => (fieldValueProgram a e).comp radialProgram)

noncomputable opaque fieldBondProgram (e : Fin 3) : Procedure inputCode bondCode
    (fun x => (4*x.2.2.1.1,4*x.2.2.1.1+(qmaFieldEdgeRight e).val,
      fieldValue x.1.1 (axis x.2.2.2.1.1) x.2.2.2.2 e)) :=
  baseLeftProgram.pair ((shiftedLeftProgram _).pair (fieldCoefficientProgram e))

noncomputable opaque fieldProgram : Procedure inputCode (listCode bondCode)
    (fun x => field x.1.1 x.2.2.1.1 (axis x.2.2.2.1.1) x.2.2.2.2) :=
  fixedListProgram inputCode bondCode 3 _ fieldBondProgram

noncomputable opaque crossCoefficientProgram (p q : Fin 4) : Procedure inputCode ratCode
    (fun x => crossValue x.1.1 x.1.2 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2 p q) :=
  selectAxis axisLeftProgram (fun a => selectAxis axisRightProgram
    (fun b => (crossValueProgram a b p q).comp crossInputProgram))

noncomputable opaque crossBondProgram (p q : Fin 4) : Procedure inputCode bondCode
    (fun x => (4*x.2.2.1.1+p.val,4*x.2.2.1.2+q.val,
      crossValue x.1.1 x.1.2 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2 p q)) :=
  (shiftedLeftProgram p).pair ((shiftedRightProgram q).pair (crossCoefficientProgram p q))

noncomputable opaque crossProgram : Procedure inputCode (listCode bondCode)
    (fun x => cross x.1.1 x.1.2 x.2.2.1.1 x.2.2.1.2
      (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) :=
  fixedListProgram inputCode bondCode 16 _ (fun e =>
    crossBondProgram ((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm e).1
      ((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm e).2)

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
