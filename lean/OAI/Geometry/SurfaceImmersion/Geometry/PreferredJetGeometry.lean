import OAI.Geometry.SurfaceImmersion.Primitive.ConstructedSurfaceLoop
import OAI.Geometry.SurfaceImmersion.Geometry.ProjectedFrameConstruction
import OAI.Geometry.SurfaceImmersion.Geometry.MetricAcceleration

namespace OAI

/-! Extend a preferred normal to nearby second jets by orthogonal projection.
All coefficients and normal vectors are explicit functions of the jet. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry

abbrev GeometricJet := CollarVelocity.JetBase

def jetTangentGram (j : GeometricJet) : ℝ := gramDet (j.2 0) (j.2 1)

def jetAccelerationCoefficients (j : GeometricJet) : Base :=
  (((j.2 1 ⬝ᵥ j.2 1)*(j.2 0 ⬝ᵥ j.2 4)-(j.2 0 ⬝ᵥ j.2 1)*(j.2 1 ⬝ᵥ j.2 4))/jetTangentGram j,
   ((j.2 0 ⬝ᵥ j.2 0)*(j.2 1 ⬝ᵥ j.2 4)-(j.2 0 ⬝ᵥ j.2 1)*(j.2 0 ⬝ᵥ j.2 4))/jetTangentGram j)

def jetSecondNormal (j : GeometricJet) : Vec := realNormalPart (j.2 0) (j.2 1) (j.2 4)

def jetProjectedPreferred (n : Base → Vec) (j : GeometricJet) : Vec :=
  realNormalPart (j.2 0) (j.2 1) (n j.1)

def jetPreferred (n : Base → Vec) (j : GeometricJet) : Vec :=
  normalize (jetProjectedPreferred n j)

private lemma jetDot_smooth (a b : Fin 5) :
    ContDiff ℝ ∞ (fun j : GeometricJet => j.2 a ⬝ᵥ j.2 b) := by
  unfold dotProduct
  apply ContDiff.sum
  intro k _
  exact ((contDiff_apply ℝ ℝ k).comp (jetSlot_smooth a)).mul
    ((contDiff_apply ℝ ℝ k).comp (jetSlot_smooth b))

lemma jetTangentGram_smooth : ContDiff ℝ ∞ jetTangentGram := by
  exact ((jetDot_smooth 0 0).mul
    (jetDot_smooth 1 1)).sub
      ((jetDot_smooth 0 1).pow 2)

lemma jetAccelerationCoefficients_smoothAt {j : GeometricJet}
    (hj : jetTangentGram j ≠ 0) : ContDiffAt ℝ ∞ jetAccelerationCoefficients j := by
  have hd (a b : Fin 5) : ContDiffAt ℝ ∞ (fun z : GeometricJet => z.2 a ⬝ᵥ z.2 b) j :=
    (jetDot_smooth a b).contDiffAt
  exact (((hd 1 1).mul (hd 0 4)).sub ((hd 0 1).mul (hd 1 4))).div
      jetTangentGram_smooth.contDiffAt hj |>.prodMk
    ((((hd 0 0).mul (hd 1 4)).sub ((hd 0 1).mul (hd 0 4))).div
      jetTangentGram_smooth.contDiffAt hj)

lemma jetSecondNormal_smoothAt {j : GeometricJet} (hj : jetTangentGram j ≠ 0) :
    ContDiffAt ℝ ∞ jetSecondNormal j :=
  contDiffAt_realNormalPart (jetSlot_smooth 0).contDiffAt (jetSlot_smooth 1).contDiffAt
    (jetSlot_smooth 4).contDiffAt hj

lemma jetProjectedPreferred_smoothAt {n : Base → Vec} {j : GeometricJet}
    (hn : ContDiffAt ℝ ∞ n j.1) (hj : jetTangentGram j ≠ 0) :
    ContDiffAt ℝ ∞ (jetProjectedPreferred n) j :=
  contDiffAt_realNormalPart (jetSlot_smooth 0).contDiffAt (jetSlot_smooth 1).contDiffAt
    (hn.comp j contDiffAt_fst) hj

lemma jetPreferred_smoothAt {n : Base → Vec} {j : GeometricJet}
    (hn : ContDiffAt ℝ ∞ n j.1) (hj : jetTangentGram j ≠ 0)
    (hproj : jetProjectedPreferred n j ≠ 0) :
    ContDiffAt ℝ ∞ (jetPreferred n) j :=
  normalize_smoothAt (jetProjectedPreferred_smoothAt hn hj) hproj

lemma jetAcceleration_decomposition (j : GeometricJet) :
    j.2 4 = (jetAccelerationCoefficients j).1 • j.2 0 +
      (jetAccelerationCoefficients j).2 • j.2 1 + jetSecondNormal j := by
  unfold jetAccelerationCoefficients jetSecondNormal realNormalPart jetTangentGram
  abel

lemma realNormalPart_eq_self {X Y n : Vec} (hX : X ⬝ᵥ n = 0) (hY : Y ⬝ᵥ n = 0) :
    realNormalPart X Y n = n := by
  simp [realNormalPart,hX,hY]

lemma jetPreferred_on_section {F n : Base → Vec} {p : Base}
    (hX : coordDeriv dx F p ⬝ᵥ n p = 0) (hY : coordDeriv dy F p ⬝ᵥ n p = 0)
    (hn : n p ⬝ᵥ n p = 1) : jetPreferred n (CollarVelocity.jetSection F p) = n p := by
  change normalize (realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (n p)) = n p
  rw [realNormalPart_eq_self hX hY,normalize_of_unit hn]

lemma jetAccelerationCoefficients_on_section {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : Base) : jetAccelerationCoefficients (CollarVelocity.jetSection F p) =
      metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p) 2 := by
  rw [induced_connection_yy hF p]
  rfl

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
