import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.NormalizationSchedule

namespace OAI

/-! Unary arithmetic for the explicit normalization quadrature schedule. -/

namespace ContinuumCoulomb.NormalizationSchedule
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque constant4096Program : Procedure unaryCode unaryCode (fun _ => 4096) :=
  ResolventSchedule.constant4096Program.comp
    ((Procedure.identity unaryCode).pair (Procedure.identity unaryCode))

noncomputable opaque constant8192Program : Procedure unaryCode unaryCode (fun _ => 8192) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant unaryCode unaryCode 2).pair constant4096Program)).congrFun
      (by intro P; norm_num)

noncomputable opaque scaleSuccessorProgram (c : ℕ)
    (pc : Procedure unaryCode unaryCode (fun _ => c)) :
    Procedure unaryCode unaryCode (fun P => c * (P + 1)) :=
  ResolventSchedule.mulProgram.comp (pc.pair Procedure.unarySuccessor)

noncomputable opaque radiusProgram : Procedure unaryCode unaryCode radius :=
  (scaleSuccessorProgram 8192 constant8192Program).congrFun
    (by intro P; exact (radius_def P).symm)

noncomputable opaque cubeProgram : Procedure unaryCode unaryCode (fun n => n ^ 3) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.identity unaryCode).pair ResolventSchedule.squareProgram)).congrFun
      (by intro n; dsimp; ring)

noncomputable opaque radiusCubeProgram : Procedure unaryCode unaryCode (fun P => radius P ^ 3) :=
  cubeProgram.comp radiusProgram

noncomputable opaque meshPrefixProgram : Procedure unaryCode unaryCode meshPrefix :=
  (ResolventSchedule.mulProgram.comp (constant4096Program.pair radiusCubeProgram)).congrFun
    (by intro P; rfl)

noncomputable opaque meshFactorsProgram : Procedure unaryCode (prodCode unaryCode unaryCode)
    (fun P => (meshPrefix P, P + 1)) := meshPrefixProgram.pair Procedure.unarySuccessor

noncomputable opaque meshRawProgram : Procedure unaryCode unaryCode
    (fun P => meshPrefix P * (P + 1)) := ResolventSchedule.mulProgram.comp meshFactorsProgram

noncomputable opaque meshProgram : Procedure unaryCode unaryCode mesh :=
  meshRawProgram.congrFun (by intro P; rfl)

noncomputable opaque radiusSquareProgram : Procedure unaryCode unaryCode (fun P => radius P ^ 2) :=
  ResolventSchedule.squareProgram.comp radiusProgram

noncomputable opaque accuracyPrefixProgram : Procedure unaryCode unaryCode accuracyPrefix :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant unaryCode unaryCode 48).pair radiusSquareProgram)).congrFun
      (by intro P; rfl)

noncomputable opaque accuracyFactorsProgram : Procedure unaryCode (prodCode unaryCode unaryCode)
    (fun P => (accuracyPrefix P, P + 1)) := accuracyPrefixProgram.pair Procedure.unarySuccessor

noncomputable opaque accuracyRawProgram : Procedure unaryCode unaryCode
    (fun P => accuracyPrefix P * (P + 1)) := ResolventSchedule.mulProgram.comp accuracyFactorsProgram

noncomputable opaque accuracyProgram : Procedure unaryCode unaryCode accuracy :=
  accuracyRawProgram.congrFun (by intro P; rfl)

noncomputable opaque doubleRadiusProgram : Procedure unaryCode unaryCode (fun P => 2 * radius P) :=
  ResolventSchedule.mulProgram.comp ((Procedure.constant unaryCode unaryCode 2).pair radiusProgram)

end ContinuumCoulomb.NormalizationSchedule

end OAI
