import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedFieldEvaluation
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CountertermProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PlanarWellProgram

namespace OAI

/-! A literal polynomial TM2 scalar evaluator for the actual manufactured
three-dimensional well field. All sites, widths and scales are input data. -/

namespace ContinuumCoulomb.ManufacturedFieldEvaluation
open ExactQuantumFactoring.BitStackProgram

def pointCode := CoulombPairEvaluation.pointCode
def sitesCode := listCode pointCode
abbrev PlanarInput := ℕ×(ℚ×(List (ℚ×ℚ)×(ℚ×ℚ)))
def planarCode : PlanarInput → List Bool := prodCode unaryCode
  (prodCode ratCode (prodCode sitesCode pointCode))
abbrev TermInput := PlanarInput×(ℚ×ℚ)
def termCode : TermInput → List Bool := prodCode planarCode pointCode
abbrev Input := ℕ×((ℚ×ℚ)×(List (ℚ×ℚ)×CappedKernelProgram.Triple))
def inputCode : Input → List Bool := prodCode unaryCode
  (prodCode (prodCode ratCode ratCode) (prodCode sitesCode CappedKernelProgram.tripleCode))

noncomputable opaque translateProgram : Procedure (prodCode pointCode pointCode) pointCode
    (fun x => translate x.1 x.2) := by
  let a := Procedure.first pointCode pointCode
  let b := Procedure.second pointCode pointCode
  let a0 := (Procedure.first ratCode ratCode).comp a
  let a1 := (Procedure.second ratCode ratCode).comp a
  let b0 := (Procedure.first ratCode ratCode).comp b
  let b1 := (Procedure.second ratCode ratCode).comp b
  exact (Procedure.ratSub.comp (a0.pair b0)).pair (Procedure.ratSub.comp (a1.pair b1))

noncomputable opaque termEnvironmentProgram : Procedure termCode planarCode Prod.fst :=
  Procedure.first planarCode pointCode
noncomputable opaque termSiteProgram : Procedure termCode pointCode Prod.snd :=
  Procedure.second planarCode pointCode
noncomputable opaque termPrecisionProgram : Procedure termCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode (prodCode ratCode (prodCode sitesCode pointCode))).comp termEnvironmentProgram
noncomputable opaque termDataProgram : Procedure termCode
    (prodCode ratCode (prodCode sitesCode pointCode)) (fun x => x.1.2) :=
  (Procedure.second unaryCode _).comp termEnvironmentProgram
noncomputable opaque termScaleProgram : Procedure termCode ratCode (fun x => x.1.2.1) :=
  (Procedure.first ratCode _).comp termDataProgram
noncomputable opaque termListPointProgram : Procedure termCode (prodCode sitesCode pointCode)
    (fun x => x.1.2.2) := (Procedure.second ratCode _).comp termDataProgram
noncomputable opaque termSitesProgram : Procedure termCode sitesCode (fun x => x.1.2.2.1) :=
  (Procedure.first sitesCode pointCode).comp termListPointProgram
noncomputable opaque termPointProgram : Procedure termCode pointCode (fun x => x.1.2.2.2) :=
  (Procedure.second sitesCode pointCode).comp termListPointProgram

noncomputable opaque termRowProgram (rho : ℕ) : Procedure termCode ratCode
    (fun x => CountertermEvaluation.row rho x.1.1 x.2 x.1.2.2.1) :=
  (CountertermEvaluation.rowProgram rho).comp
    (termPrecisionProgram.pair (termSiteProgram.pair termSitesProgram))

noncomputable opaque termFractionProgram (rho : ℕ) : Procedure termCode ratCode
    (fun x => CountertermEvaluation.row rho x.1.1 x.2 x.1.2.2.1/x.1.2.1) :=
  Procedure.ratDiv.comp ((termRowProgram rho).pair termScaleProgram)

noncomputable opaque termClippedProgram (rho : ℕ) : Procedure termCode ratCode
    (fun x => RationalSmoothTransition.clip
      (CountertermEvaluation.row rho x.1.1 x.2 x.1.2.2.1/x.1.2.1)) :=
  SmoothTransitionProgram.clipProgram.comp (termFractionProgram rho)

noncomputable opaque coefficientProgram (rho : ℕ) : Procedure termCode ratCode
    (fun x => coefficient rho x.1.1 x.1.2.1 x.1.2.2.1 x.2) :=
  Procedure.ratAdd.comp ((Procedure.constant termCode ratCode (1:ℚ)).pair (termClippedProgram rho))

noncomputable opaque termRelativeProgram : Procedure termCode pointCode
    (fun x => translate x.1.2.2.2 x.2) :=
  translateProgram.comp (termPointProgram.pair termSiteProgram)

noncomputable opaque termWellProgram : Procedure termCode ratCode
    (fun x => PlanarWellNumerics.approximate x.1.1 (translate x.1.2.2.2 x.2)) :=
  by
    let p := PlanarWellNumerics.program.comp (termPrecisionProgram.pair termRelativeProgram)
    exact p.congrFun (by intro x; rfl)

noncomputable opaque termProgram (rho : ℕ) : Procedure termCode ratCode
    (fun x => coefficient rho x.1.1 x.1.2.1 x.1.2.2.1 x.2 *
      PlanarWellNumerics.approximate x.1.1 (translate x.1.2.2.2 x.2)) :=
  Procedure.ratMul.comp ((coefficientProgram rho).pair termWellProgram)

noncomputable opaque planarProgram (rho : ℕ) : Procedure planarCode ratCode
    (fun x => planar rho x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let tail := Procedure.second unaryCode (prodCode ratCode (prodCode sitesCode pointCode))
  let listpoint := (Procedure.second ratCode (prodCode sitesCode pointCode)).comp tail
  let sites := (Procedure.first sitesCode pointCode).comp listpoint
  let mapped := (Procedure.listMapWith (ea := planarCode) (eb := pointCode) (ec := ratCode)
    (f := fun env a => coefficient rho env.1 env.2.1 env.2.2.1 a *
      PlanarWellNumerics.approximate env.1 (translate env.2.2.2 a))
    (0,0) 0 (termProgram rho)).comp ((Procedure.identity planarCode).pair sites)
  exact RationalSumProgram.sumProgram.comp mapped

noncomputable opaque precisionFactorsProgram : Procedure (prodCode unaryCode unaryCode)
    (prodCode unaryCode unaryCode) (fun x => ((x.1+1)^2,x.2+1)) := by
  let m := Procedure.unarySuccessor.comp (Procedure.first unaryCode unaryCode)
  let p := Procedure.unarySuccessor.comp (Procedure.second unaryCode unaryCode)
  exact ((Procedure.unaryMul.comp (m.pair m)).pair p).congrFun
    (by intro x; simp only [pow_two]; rfl)

noncomputable opaque precisionProgram (rho : ℕ) : Procedure (prodCode unaryCode unaryCode)
    unaryCode (fun x => precision rho x.1 x.2) := by
  let base := Procedure.unaryMul.comp precisionFactorsProgram
  let C := Procedure.constant (prodCode unaryCode unaryCode) unaryCode
    (16*(CountertermEvaluation.guard rho)^4)
  exact (Procedure.unaryMul.comp (C.pair base)).congrFun (by intro x; change 16*(CountertermEvaluation.guard rho)^4*((x.1+1)^2*(x.2+1)) = _; unfold precision; ring)

noncomputable opaque dataProgram : Procedure inputCode
    (prodCode (prodCode ratCode ratCode) (prodCode sitesCode CappedKernelProgram.tripleCode))
    (fun x => x.2) := Procedure.second unaryCode _
noncomputable opaque parametersProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.2.1) := (Procedure.first _ _).comp dataProgram
noncomputable opaque geometryProgram : Procedure inputCode (prodCode sitesCode CappedKernelProgram.tripleCode)
    (fun x => x.2.2) := (Procedure.second _ _).comp dataProgram
noncomputable opaque sitesProgram : Procedure inputCode sitesCode (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp geometryProgram
noncomputable opaque pointProgram : Procedure inputCode CappedKernelProgram.tripleCode (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp geometryProgram
noncomputable opaque scaleProgram : Procedure inputCode ratCode (fun x => x.2.1.1) :=
  (Procedure.first ratCode ratCode).comp parametersProgram
noncomputable opaque widthProgram : Procedure inputCode ratCode (fun x => x.2.1.2) :=
  (Procedure.second ratCode ratCode).comp parametersProgram
noncomputable opaque coordinateTailProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.2.2.2.2) := (Procedure.second ratCode (prodCode ratCode ratCode)).comp pointProgram
noncomputable opaque planarPointProgram : Procedure inputCode pointCode
    (fun x => (x.2.2.2.1,x.2.2.2.2.1)) :=
  ((Procedure.first ratCode (prodCode ratCode ratCode)).comp pointProgram).pair
    ((Procedure.first ratCode ratCode).comp coordinateTailProgram)
noncomputable opaque heightProgram : Procedure inputCode ratCode (fun x => x.2.2.2.2.2) :=
  (Procedure.second ratCode ratCode).comp coordinateTailProgram

noncomputable opaque rawCutoffProgram : Procedure inputCode ratCode
    (fun x => RationalSmoothTransition.clip (VerticalCutoffProgram.value (x.1,(x.2.1.2,x.2.2.2.2.2)))) := by
  let p : Procedure inputCode unaryCode Prod.fst := Procedure.first unaryCode
    (prodCode (prodCode ratCode ratCode) (prodCode sitesCode CappedKernelProgram.tripleCode))
  exact SmoothTransitionProgram.clipProgram.comp (VerticalCutoffProgram.program.comp
    (p.pair (widthProgram.pair heightProgram)))

noncomputable opaque rawPlanarProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => planar rho x.1 x.2.1.1 x.2.2.1 (x.2.2.2.1,x.2.2.2.2.1)) :=
  by
    let p := (planarProgram rho).comp ((Procedure.first unaryCode
      (prodCode (prodCode ratCode ratCode) (prodCode sitesCode CappedKernelProgram.tripleCode))).pair
      (scaleProgram.pair (sitesProgram.pair planarPointProgram)))
    exact p.congrFun (by intro x; rfl)

noncomputable opaque rawProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => rawValue rho x.1 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2) :=
  Procedure.ratMul.comp (rawCutoffProgram.pair (rawPlanarProgram rho))

noncomputable opaque inputPrecisionProgram (rho : ℕ) : Procedure inputCode unaryCode
    (fun x => precision rho x.2.2.1.length x.1) := by
  let p : Procedure inputCode unaryCode Prod.fst := Procedure.first unaryCode
    (prodCode (prodCode ratCode ratCode) (prodCode sitesCode CappedKernelProgram.tripleCode))
  let m := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pointCode (0,0)).comp sitesProgram
  exact (precisionProgram rho).comp (m.pair p)

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode
    (fun x => value rho x.1 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2) :=
  by
    let p := (rawProgram rho).comp ((inputPrecisionProgram rho).pair dataProgram)
    exact p.congrFun (by intro x; rfl)

noncomputable def certificate (rho : ℕ) : Turing.TM2ComputableInPolyTime inputCode ratCode
    (fun x => value rho x.1 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2) := (program rho).toTM2

end ContinuumCoulomb.ManufacturedFieldEvaluation

end OAI
