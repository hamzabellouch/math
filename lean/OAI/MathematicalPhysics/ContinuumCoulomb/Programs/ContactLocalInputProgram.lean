import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactEdgeNumberProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactRationalLocal

namespace OAI

/-! Extract the exact nineteen local lengths from the calibrated final-edge
array. Runtime indices are the proved natural formulas for `encodeEdge`. -/

namespace ContinuumCoulomb.ContactLocalInputProgram
open ExactQuantumFactoring.BitStackProgram ContactMediator

abbrev Input := ℕ × (ℕ × (ℕ × (Bool × List ℚ)))

def inputCode : Input → List Bool := prodCode unaryCode
  (prodCode unaryCode (prodCode unaryCode (prodCode Procedure.boolCode (listCode ratCode))))

def lookup (x : Input) (a : LocalEdge) : ℚ :=
  (x.2.2.2.2.drop (edgeNumber x.2.1 x.2.2.1 a)).headD 1

def record (x : Input) : ContactRationalGadget.Input :=
  (x.1, (x.2.2.2.1, (lookup x (Sum.inl ()),
    (List.ofFn (fun k : Fin 9 => lookup x (leftEdge k)),
      List.ofFn (fun k : Fin 9 => lookup x (rightEdge k))))))

noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first unaryCode _

noncomputable opaque tailProgram : Procedure inputCode
    (prodCode unaryCode (prodCode unaryCode (prodCode Procedure.boolCode (listCode ratCode))))
    Prod.snd := Procedure.second unaryCode _

noncomputable opaque countProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first unaryCode _).comp tailProgram

noncomputable opaque restProgram : Procedure inputCode
    (prodCode unaryCode (prodCode Procedure.boolCode (listCode ratCode))) (fun x => x.2.2) :=
  (Procedure.second unaryCode _).comp tailProgram

noncomputable opaque indexProgram : Procedure inputCode unaryCode (fun x => x.2.2.1) :=
  (Procedure.first unaryCode _).comp restProgram

noncomputable opaque lastProgram : Procedure inputCode
    (prodCode Procedure.boolCode (listCode ratCode)) (fun x => x.2.2.2) :=
  (Procedure.second unaryCode _).comp restProgram

noncomputable opaque signProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.2.2.1) :=
  (Procedure.first Procedure.boolCode (listCode ratCode)).comp lastProgram

noncomputable opaque valuesProgram : Procedure inputCode (listCode ratCode) (fun x => x.2.2.2.2) :=
  (Procedure.second Procedure.boolCode (listCode ratCode)).comp lastProgram

noncomputable opaque lookupProgram (a : LocalEdge) : Procedure inputCode ratCode (fun x => lookup x a) :=
  (Procedure.listGet ratCode 1).comp
    (((ContactEdgeNumberProgram.edgeProgram a).comp (countProgram.pair indexProgram)).pair valuesProgram)

noncomputable def valuesListProgram : (as : List LocalEdge) →
    Procedure inputCode (listCode ratCode) (fun x => as.map (lookup x))
  | [] => (Procedure.constant inputCode (listCode ratCode) []).congrFun (by intro x; rfl)
  | a :: as => ((Procedure.listCons ratCode).comp
      ((lookupProgram a).pair (valuesListProgram as))).congrFun (by intro x; rfl)

noncomputable opaque leftProgram : Procedure inputCode (listCode ratCode)
    (fun x => List.ofFn (fun k : Fin 9 => lookup x (leftEdge k))) :=
  (valuesListProgram (List.ofFn leftEdge)).congrFun (by
    intro x
    simp only [List.map_ofFn, Function.comp_def])

noncomputable opaque rightProgram : Procedure inputCode (listCode ratCode)
    (fun x => List.ofFn (fun k : Fin 9 => lookup x (rightEdge k))) :=
  (valuesListProgram (List.ofFn rightEdge)).congrFun (by
    intro x
    simp only [List.map_ofFn, Function.comp_def])

noncomputable opaque program : Procedure inputCode ContactRationalGadget.inputCode record :=
  precisionProgram.pair (signProgram.pair
    ((lookupProgram (Sum.inl ())).pair (leftProgram.pair rightProgram)))

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode
    ContactRationalGadget.inputCode record := program.toTM2

end ContinuumCoulomb.ContactLocalInputProgram

end OAI
