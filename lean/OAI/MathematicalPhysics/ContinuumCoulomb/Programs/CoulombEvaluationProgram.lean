import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombEvaluationError

namespace OAI

/-! A single polynomial-time TM2 program for the actual localized
Coulomb coefficient at every rational separation and unary precision. -/

namespace ContinuumCoulomb.CoulombEvaluation
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × ℚ
def inputCode : Input → List Bool := prodCode unaryCode ratCode

noncomputable opaque scaleProgram (k : ℕ) : Procedure unaryCode unaryCode (fun P => k * P) :=
  ResolventSchedule.mulProgram.comp
    ((Procedure.constant unaryCode unaryCode k).pair (Procedure.identity unaryCode))

noncomputable opaque sixthProgram : Procedure unaryCode unaryCode (fun P => P ^ 6) :=
  (ResolventSchedule.squareProgram.comp NormalizationSchedule.cubeProgram).congrFun
    (by intro P; simp only [Function.comp_apply]; ring)

noncomputable opaque truncationPrecisionProgram : Procedure unaryCode unaryCode truncationPrecision :=
  (scaleProgram 4).comp Procedure.unarySuccessor

noncomputable opaque capScaleProgram : Procedure unaryCode unaryCode
    (fun P => CoulombTruncationSchedule.scale (truncationPrecision P)) :=
  ((scaleProgram 8).comp (Procedure.unarySuccessor.comp truncationPrecisionProgram)).congrFun
    (by intro P; rfl)

noncomputable opaque denominatorProgram (rho : ℕ) : Procedure unaryCode unaryCode (denominator rho) :=
  (scaleProgram (CoulombTruncationSchedule.guard (GaussianFrequency.frequency rho))).comp capScaleProgram

noncomputable opaque radiusProgram (rho : ℕ) : Procedure unaryCode unaryCode (radius rho) :=
  ((scaleProgram (CoulombTruncationSchedule.guard (GaussianFrequency.frequency rho))).comp
    (ResolventSchedule.squareProgram.comp capScaleProgram)).congrFun (by intro P; rfl)

noncomputable opaque rawPrecisionProgram (rho : ℕ) : Procedure unaryCode unaryCode (rawPrecision rho) :=
  ((scaleProgram (4 * normalizationBound rho)).comp Procedure.unarySuccessor).congrFun
    (by intro P; rfl)

noncomputable opaque volumeProgram (rho : ℕ) : Procedure unaryCode unaryCode
    (fun P => CoulombQuadratureSchedule.volume (radius rho P)) :=
  (sixthProgram.comp ((scaleProgram 2).comp (radiusProgram rho))).congrFun (by intro P; rfl)

noncomputable opaque lipschitzProgram (rho : ℕ) : Procedure unaryCode unaryCode
    (fun P => CoulombQuadratureSchedule.lipschitz (frequencyBound rho) (radius rho P) (denominator rho P)) := by
  let r := radiusProgram rho
  let d := denominatorProgram rho
  let t := (scaleProgram (2 * frequencyBound rho)).comp r
  let k := ResolventSchedule.addProgram.comp ((Procedure.constant unaryCode unaryCode 64).pair t)
  let kd := ResolventSchedule.mulProgram.comp (k.pair d)
  let dsq := ResolventSchedule.squareProgram.comp d
  exact (ResolventSchedule.addProgram.comp (kd.pair dsq)).congrFun (by intro P; rfl)

noncomputable opaque meshProgram (rho : ℕ) : Procedure unaryCode unaryCode (mesh rho) := by
  let r := (scaleProgram 48).comp (radiusProgram rho)
  let rl := ResolventSchedule.mulProgram.comp (r.pair (lipschitzProgram rho))
  let rlv := ResolventSchedule.mulProgram.comp (rl.pair (volumeProgram rho))
  exact (ResolventSchedule.mulProgram.comp (rlv.pair (rawPrecisionProgram rho))).congrFun
    (by intro P; rfl)

noncomputable opaque samplePrecisionProgram (rho : ℕ) :
    Procedure unaryCode unaryCode (samplePrecision rho) := by
  let d := (scaleProgram 32).comp (denominatorProgram rho)
  let dv := ResolventSchedule.mulProgram.comp (d.pair (volumeProgram rho))
  exact (ResolventSchedule.mulProgram.comp (dv.pair (rawPrecisionProgram rho))).congrFun
    (by intro P; rfl)

noncomputable opaque kernelPrecisionProgram (rho : ℕ) :
    Procedure unaryCode unaryCode (kernelPrecision rho) := by
  let d := (scaleProgram 4).comp (ResolventSchedule.squareProgram.comp (denominatorProgram rho))
  let dv := ResolventSchedule.mulProgram.comp (d.pair (volumeProgram rho))
  exact (ResolventSchedule.mulProgram.comp (dv.pair (rawPrecisionProgram rho))).congrFun
    (by intro P; rfl)

noncomputable opaque normalizationPrecisionProgram (rho : ℕ) :
    Procedure unaryCode unaryCode (normalizationPrecision rho) := by
  let d := (scaleProgram (8 * rawMassBound rho)).comp (denominatorProgram rho)
  exact (ResolventSchedule.mulProgram.comp (d.pair Procedure.unarySuccessor)).congrFun
    (by intro P; rfl)

noncomputable opaque radiusRationalProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => (radius rho x.1 : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp
    ((radiusProgram rho).comp (Procedure.first unaryCode ratCode)))

noncomputable opaque meshRationalProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => (mesh rho x.1 : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp
    ((meshProgram rho).comp (Procedure.first unaryCode ratCode)))

noncomputable opaque epsilonProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => 1 / (denominator rho x.1 : ℚ)) :=
  (Procedure.ratInv.comp (Procedure.natToRat.comp (Procedure.unaryToBits.comp
    ((denominatorProgram rho).comp (Procedure.first unaryCode ratCode))))).congrFun
      (by intro x; simp only [one_div]; rfl)

noncomputable opaque inputProgram (rho : ℕ) :
    Procedure inputCode (RationalRectangleProgram.inputCode RawCoulombSample.settingsCode)
      (fun x => input rho x.1 x.2) := by
  let p := Procedure.first unaryCode ratCode
  let r := (radiusProgram rho).comp p
  let q := (samplePrecisionProgram rho).comp p
  let b := (kernelPrecisionProgram rho).comp p
  let eps := epsilonProgram rho
  let z := Procedure.constant inputCode ratCode (0 : ℚ)
  let s := (Procedure.second unaryCode ratCode).pair (z.pair z)
  let settings := (r.pair q).pair ((b.pair eps).pair s)
  let nr := meshRationalProgram rho
  let rr := radiusRationalProgram rho
  let low := Procedure.ratNeg.comp rr
  let width := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode (2 : ℚ)).pair rr)
  let step := Procedure.ratDiv.comp (width.pair nr)
  exact (((meshProgram rho).comp p).pair (settings.pair (low.pair step))).congrFun
    (by intro x; rfl)

noncomputable opaque rawProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => rawApproximate rho x.1 x.2) :=
  ((RawCoulombSample.quadratureProgram rho).comp (inputProgram rho)).congrFun (by intro x; rfl)

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode
    (fun x => approximate rho x.1 x.2) := by
  let p := Procedure.first unaryCode ratCode
  let n := (normalizationPrecisionProgram rho).comp p
  let c := (CoulombNormalization.program rho).comp n
  exact (Procedure.ratMul.comp (c.pair (rawProgram rho))).congrFun (by intro x; rfl)

noncomputable def certificate (rho : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode ratCode (fun x => approximate rho x.1 x.2) :=
  (program rho).toTM2

end ContinuumCoulomb.CoulombEvaluation

end OAI
