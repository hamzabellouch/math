import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.TransformedGaussProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.TransformedGaussSeparation

namespace OAI

/-! The same certified node program is applied to the whole finite list of
Gauss labels. It preserves the nucleus count and, at the proved precision,
pairwise distinctness. -/

open scoped NNReal
namespace ContinuumCoulomb.TransformedGauss
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode position)
open EulerRegisters (Registers registersCode)
open RationalGaussNodes (Signs signsCode)

abbrev Environment := (ℕ×ℕ)×((ℚ×ℚ)×List (ℚ×ℚ))
abbrev Label := Registers×Signs
def labelCode : Label → List Bool := prodCode registersCode signsCode
def environmentCode : Environment → List Bool :=
  prodCode (prodCode unaryCode Nat.bits)
    (prodCode (prodCode ratCode ratCode) ManufacturedFieldEvaluation.sitesCode)
def listInputCode : (Environment×List Label) → List Bool :=
  prodCode environmentCode (listCode labelCode)

noncomputable def nodes (rho U C K : ℕ) (x : Environment×List Label) : List Triple :=
  x.2.map (fun l => value rho U C K x.1.1.1 x.1.1.2 x.1.2.1.1 x.1.2.1.2 x.1.2.2 l.1 l.2)

private noncomputable opaque nodeEnvironmentProgram :
    Procedure (prodCode environmentCode labelCode) environmentCode Prod.fst :=
  Procedure.first _ _
private noncomputable opaque nodeLabelProgram :
    Procedure (prodCode environmentCode labelCode) labelCode Prod.snd := Procedure.second _ _
private noncomputable opaque nodeParametersProgram :
    Procedure (prodCode environmentCode labelCode) (prodCode unaryCode Nat.bits)
      (fun x => x.1.1) := (Procedure.first _ _).comp nodeEnvironmentProgram
private noncomputable opaque nodeFieldProgram :
    Procedure (prodCode environmentCode labelCode)
      (prodCode (prodCode ratCode ratCode) ManufacturedFieldEvaluation.sitesCode)
      (fun x => x.1.2) := (Procedure.second _ _).comp nodeEnvironmentProgram
private noncomputable opaque nodeArgumentProgram :
    Procedure (prodCode environmentCode labelCode) inputCode
      (fun x => (x.1.1,(x.1.2.1,(x.1.2.2,x.2)))) :=
  nodeParametersProgram.pair
    (((Procedure.first _ _).comp nodeFieldProgram).pair
      (((Procedure.second _ _).comp nodeFieldProgram).pair nodeLabelProgram))

noncomputable opaque listProgram (rho U C K : ℕ) :
    Procedure listInputCode (listCode tripleCode) (nodes rho U C K) := by
  let sample := (program rho U C K).comp nodeArgumentProgram
  exact (Procedure.listMapWith (ea := environmentCode) (eb := labelCode) (ec := tripleCode)
    (f := fun e l => value rho U C K e.1.1 e.1.2 e.2.1.1 e.2.1.2 e.2.2 l.1 l.2)
    ((0,(0,0)),(false,(false,false))) (0,(0,0)) sample).congrFun (by intro x; rfl)

noncomputable def listCertificate (rho U C K : ℕ) :
    Turing.TM2ComputableInPolyTime listInputCode (listCode tripleCode) (nodes rho U C K) :=
  (listProgram rho U C K).toTM2

theorem nodes_length (rho U C K : ℕ) (x : Environment×List Label) :
    (nodes rho U C K x).length = x.2.length := by simp only [nodes,List.length_map]

theorem nodes_nodup (rho U C K : ℕ) (P : ℕ) {N : ℕ} (hN : 0 < N)
    (scale S : ℚ) (sites : List (ℚ×ℚ)) (labels : List Label) (hnodup : labels.Nodup)
    (G : Position → Position) {J : ℝ≥0} (hG : AntilipschitzWith J G)
    (herror : ∀ l : Label,
      ‖position (value rho U C K P N scale S sites l.1 l.2)-
        G (gaussLatticePoint (N:ℝ)⁻¹ (RationalGaussNodes.index l.1 l.2))‖ ≤ ((P:ℝ)+1)⁻¹)
    (hprecision : 2*(J:ℝ)*((P:ℝ)+1)⁻¹ < (N:ℝ)⁻¹/3) :
    (nodes rho U C K (((P,N),((scale,S),sites)),labels)).Nodup := by
  exact hnodup.map (value_injective id Function.injective_id rho U C K P hN scale S sites G
    hG herror hprecision)

end ContinuumCoulomb.TransformedGauss

end OAI
