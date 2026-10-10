import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumExchangeSample

namespace OAI

/-! Literal evaluation of each cross-block physical exchange coefficient. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque stencilProgram (a : Fin 2) (p : Fin 4) : Procedure ratCode ratCode
    (fun t => stencil a (decide (t ≤ 0)) p) := by
  exact (Procedure.conditional positiveProgram (Procedure.constant ratCode ratCode (stencil a false p))
    (Procedure.constant ratCode ratCode (stencil a true p))).congrFun (by
      intro t
      by_cases ht : 0 < t
      · simp [ht,not_le_of_gt ht]
      · simp [ht,le_of_not_gt ht])

abbrev CrossInput := (ℕ × ℚ) × ℚ
def crossCode : CrossInput → List Bool := prodCode (prodCode unaryCode ratCode) ratCode

noncomputable opaque crossParametersProgram : Procedure crossCode (prodCode unaryCode ratCode) Prod.fst :=
  Procedure.first _ _

noncomputable opaque crossPrecisionProgram : Procedure crossCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode ratCode).comp crossParametersProgram

noncomputable opaque crossScaleProgram : Procedure crossCode ratCode (fun x => x.1.2) :=
  (Procedure.second unaryCode ratCode).comp crossParametersProgram

noncomputable opaque crossCoefficientProgram : Procedure crossCode ratCode Prod.snd :=
  Procedure.second _ _

noncomputable opaque crossCouplingProgram (a b : Fin 2) : Procedure crossCode ratCode
    (fun x => calibrated a b (x.1.1,x.2)) :=
  (calibratedProgram a b).comp (crossPrecisionProgram.pair crossCoefficientProgram)

noncomputable opaque crossBaseProgram (a b : Fin 2) : Procedure crossCode ratCode
    (fun x => x.1.2*calibrated a b (x.1.1,x.2)) :=
  Procedure.ratMul.comp (crossScaleProgram.pair (crossCouplingProgram a b))

noncomputable opaque crossStencilProgram (a b : Fin 2) (p q : Fin 4) : Procedure crossCode ratCode
    (fun x => stencil a true p*stencil b (decide (x.2 ≤ 0)) q) :=
  Procedure.ratMul.comp ((Procedure.constant crossCode ratCode (stencil a true p)).pair
    ((stencilProgram b q).comp crossCoefficientProgram))

noncomputable opaque crossValueProgram (a b : Fin 2) (p q : Fin 4) : Procedure crossCode ratCode
    (fun x => crossValue x.1.1 x.1.2 a b x.2 p q) :=
  (Procedure.ratMul.comp ((crossBaseProgram a b).pair (crossStencilProgram a b p q))).congrFun
    (by intro x; rfl)

noncomputable def crossValueCertificate (a b : Fin 2) (p q : Fin 4) :
    Turing.TM2ComputableInPolyTime crossCode ratCode (fun x => crossValue x.1.1 x.1.2 a b x.2 p q) :=
  (crossValueProgram a b p q).toTM2

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
