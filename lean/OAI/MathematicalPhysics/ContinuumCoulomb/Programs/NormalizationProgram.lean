import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.NormalizationArithmetic

namespace OAI

/-! Actual polynomial TM2 computation of the normalization integral at
inverse-polynomial precision. Every mesh and sample parameter is built
using the proved unary arithmetic procedures. -/

namespace ContinuumCoulomb.NormalizationSchedule
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque radiusRationalProgram : Procedure unaryCode ratCode (fun P => (radius P : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp radiusProgram)

noncomputable opaque meshRationalProgram : Procedure unaryCode ratCode (fun P => (mesh P : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp meshProgram)

noncomputable opaque doubleRadiusRationalProgram : Procedure unaryCode ratCode
    (fun P => ((2 * radius P : ℕ) : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp doubleRadiusProgram)

noncomputable opaque lowerProgram : Procedure unaryCode ratCode (fun P => -(radius P : ℚ)) :=
  Procedure.ratNeg.comp radiusRationalProgram

noncomputable opaque stepProgram : Procedure unaryCode ratCode
    (fun P => (2 * (radius P : ℚ)) / (mesh P : ℚ)) :=
  (Procedure.ratDiv.comp (doubleRadiusRationalProgram.pair meshRationalProgram)).congrFun
    (by intro P; simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat])

noncomputable opaque inputProgram :
    Procedure unaryCode (RationalRectangleProgram.inputCode NormalizationQuadrature.settingsCode) input :=
  (meshProgram.pair ((doubleRadiusProgram.pair accuracyProgram).pair
    (lowerProgram.pair stepProgram))).congrFun (by intro P; rfl)

noncomputable opaque program : Procedure unaryCode ratCode approximate :=
  (NormalizationQuadrature.program.comp inputProgram).congrFun (by intro P; rfl)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime unaryCode ratCode approximate := program.toTM2

end ContinuumCoulomb.NormalizationSchedule

end OAI
