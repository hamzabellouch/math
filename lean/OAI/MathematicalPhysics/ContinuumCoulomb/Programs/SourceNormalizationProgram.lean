import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceNormalizedPromise

namespace OAI

/-! Actual polynomial-time normalization of a literal source-bond list.
The input coefficient bound and inverse precision are unary metadata; the
rounding denominator uses the actual list length, and zero bonds are deleted. -/

namespace ContinuumCoulomb.SourceNormalizationProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque add : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 + x.2) := Procedure.unaryAdd
noncomputable opaque mul : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 * x.2) := Procedure.unaryMul

noncomputable opaque xsProgram : Procedure inputCode (listCode bondCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque environment : Procedure inputCode envCode Prod.fst := Procedure.first _ _
noncomputable opaque lengthProgram : Procedure inputCode unaryCode (fun x => x.2.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp xsProgram
noncomputable opaque wProgram : Procedure inputCode unaryCode (fun x => x.1.2.1) :=
  ((Procedure.first unaryCode _).comp (Procedure.second unaryCode _)).comp environment
noncomputable opaque gProgram : Procedure inputCode unaryCode (fun x => x.1.2.2.1) :=
  (((Procedure.first unaryCode unaryCode).comp (Procedure.second unaryCode _)).comp
    (Procedure.second unaryCode _)).comp environment
noncomputable opaque nProgram : Procedure inputCode unaryCode (fun x => x.1.2.2.2) :=
  (((Procedure.second unaryCode unaryCode).comp (Procedure.second unaryCode _)).comp
    (Procedure.second unaryCode _)).comp environment

noncomputable opaque denominatorProgram : Procedure inputCode unaryCode
    (fun x => SourceNormalizedSpectrum.denominator x.2.length x.1.2.2.1) := by
  let rPlus : Procedure inputCode unaryCode (fun x => x.2.length + 1) :=
    Procedure.unarySuccessor.comp lengthProgram
  let base : Procedure inputCode unaryCode (fun x => 1024 * (x.2.length + 1)) :=
    mul.comp ((Procedure.constant inputCode unaryCode 1024).pair rPlus)
  exact (mul.comp (base.pair gProgram)).congrFun (by intro x; rfl)

def rounded (x : Input) : List Bond := x.2.map (fun e =>
  (e.1, e.2.1, SourceCoefficientRounding.coefficient
    (SourceNormalizedSpectrum.denominator x.2.length x.1.2.2.1) e.2.2))

def retained (x : Input) : List Bond := (rounded x).filter SourceZeroFilter.keep

noncomputable opaque roundList : Procedure (prodCode unaryCode (listCode bondCode))
    (listCode bondCode) (fun x => x.2.map (fun e =>
      (e.1, e.2.1, SourceCoefficientRounding.coefficient x.1 e.2.2))) :=
  SourceCoefficientRounding.listProgram
noncomputable opaque roundedProgram : Procedure inputCode (listCode bondCode) rounded := by
  let p : Procedure inputCode (prodCode unaryCode (listCode bondCode))
      (fun x => (SourceNormalizedSpectrum.denominator x.2.length x.1.2.2.1, x.2)) :=
    denominatorProgram.pair xsProgram
  exact (roundList.comp p).congrFun (by intro x; rfl)
noncomputable opaque retainedProgram : Procedure inputCode (listCode bondCode) retained :=
  SourceZeroFilter.filterProgram.comp roundedProgram
noncomputable opaque retainedLength : Procedure inputCode unaryCode
    (fun x => (retained x).length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength bondCode zeroBond).comp retainedProgram
noncomputable opaque boundProgram : Procedure inputCode unaryCode
    (fun x => SourceNormalizedSpectrum.denominator x.2.length x.1.2.2.1 + x.1.2.1 + 1) :=
  Procedure.unarySuccessor.comp (add.comp (denominatorProgram.pair wProgram))

def normalized (x : Input) : Input :=
  (((retained x).length,
    SourceNormalizedSpectrum.denominator x.2.length x.1.2.2.1 + x.1.2.1 + 1,
    x.1.2.2.1, x.1.2.2.2), retained x)

noncomputable opaque normalizedEnv : Procedure inputCode envCode (fun x => (normalized x).1) :=
  retainedLength.pair (boundProgram.pair (gProgram.pair nProgram))
noncomputable opaque normalizedProgram : Procedure inputCode inputCode normalized :=
  normalizedEnv.pair retainedProgram
noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode inputCode normalized :=
  normalizedProgram.toTM2

end ContinuumCoulomb.SourceNormalizationProgram

end OAI
