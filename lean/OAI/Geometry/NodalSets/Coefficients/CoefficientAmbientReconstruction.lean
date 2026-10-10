import OAI.Geometry.NodalSets.Charts.CenteredSphereChart
import OAI.Geometry.NodalSets.Charts.ChartFrameSmooth
import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientMap

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance coefficientReconstructionDimension : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

def sphereChartAmbientCovector (p : Base) (v : AmbientBase) (z : BaseModel) :
    BaseModel →L[ℝ] ℝ := (innerSL ℝ v).comp (sphereChartDerivative p z)

lemma sphereChartAmbientCovector_rep (p : Base) (v : AmbientBase) (z : BaseModel) :
    sphereCoordinateCovector p z (baseCovectorCoordinates (sphereChartAmbientCovector p v z)) =
      sphereCovectorRestriction ((extChartAt (𝓡 4) p).symm z) v := by
  symm
  apply sphereCoordinateCovector_unique p (by rw [centeredSphereChart_target]; trivial)
  intro w
  exact baseCovectorCoordinates_apply (sphereChartAmbientCovector p v z) (WithLp.toLp 2 w)

lemma sphereChartAmbientCovector_smooth (p : Base) (v : AmbientBase) :
    ContDiff ℝ ∞ (sphereChartAmbientCovector p v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact contDiffAt_const.clm_comp
    (sphereChartDerivative_smooth_at p (by rw [centeredSphereChart_target]; trivial))

def coefficientAmbientEntry (p : Base) (c : BaseModel → CoefficientPoint BaseModel)
    (i j : Fin 5) (z : BaseModel) : ℝ :=
  sphereChartAmbientCovector p (EuclideanSpace.basisFun (Fin 5) ℝ i) z
    ((c z).1 (sphereChartAmbientCovector p (EuclideanSpace.basisFun (Fin 5) ℝ j) z)) +
      (((extChartAt (𝓡 4) p).symm z : AmbientBase) i) *
        (((extChartAt (𝓡 4) p).symm z : AmbientBase) j)

lemma coefficientAmbientEntry_intrinsic (A : IntrinsicTensor) (rho : Base → ℝ)
    (p : Base) (i j : Fin 5) (z : BaseModel) :
    coefficientAmbientEntry p (intrinsicChartCoefficient A rho p) i j z =
      intrinsicAmbientMatrix A ((extChartAt (𝓡 4) p).symm z) i j := by
  unfold coefficientAmbientEntry
  rw [intrinsicChartCoefficient_pair,sphereChartAmbientCovector_rep,sphereChartAmbientCovector_rep]
  simp only [intrinsicAmbientMatrix,ambientFormMatrix,intrinsicAmbientForm_apply,
    EuclideanSpace.inner_basisFun_real]

lemma coefficientAmbientEntry_smoothOn (p : Base)
    (c : BaseModel → CoefficientPoint BaseModel) {S : Set BaseModel}
    (hc : ContDiffOn ℝ ∞ c S) (i j : Fin 5) :
    ContDiffOn ℝ ∞ (coefficientAmbientEntry p c i j) S := by
  have hcoord : ContDiff ℝ ∞ (fun z ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase)) :=
    contDiff_iff_contDiffAt.mpr (fun z ↦ smooth_inverse_chart_comp
      (Subtype.val : Base → AmbientBase) (contMDiff_coe_sphere (n := 4)) p
      (by rw [centeredSphereChart_target]; trivial))
  have hi : ContDiff ℝ ∞ (fun z ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i) :=
    (contDiff_piLp_apply 2).comp hcoord
  have hj : ContDiff ℝ ∞ (fun z ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) j) :=
    (contDiff_piLp_apply 2).comp hcoord
  exact ((sphereChartAmbientCovector_smooth p _).contDiffOn.clm_apply
    (hc.fst.clm_apply (sphereChartAmbientCovector_smooth p _).contDiffOn)).add
    (hi.contDiffOn.mul hj.contDiffOn)

end
end Yau.Target

end OAI
