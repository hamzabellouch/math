import OAI.Geometry.SurfaceImmersion.Atlas.PhaseTransitionRegularity
import OAI.Geometry.SurfaceImmersion.Geometry.CovectorPullbackParameters

namespace OAI

/-! Independent phase covectors give the nonzero first components of the
actual transported directions at every finite crossing. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SmallModes RealModes SurfaceJetCoordinates PhaseGeometry

namespace PhaseGeometry

def firstCoordinateCovector (L : Base →L[ℝ] Base) : Base := ((L dx).1,(L dy).1)

lemma firstCoordinateCovector_apply (L : Base →L[ℝ] Base) (v : Base) :
    phaseLinear (firstCoordinateCovector L) v = (L v).1 := by
  have hv : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]
  conv_rhs => rw [hv]
  simp only [map_add,map_smul,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
  change (L dx).1*v.1 + (L dy).1*v.2 = _
  ring

lemma phaseDerivative_fst {T : Base → Base} {x : Base} (hT : DifferentiableAt ℝ T x) :
    phaseDerivative (Prod.fst ∘ T) x = firstCoordinateCovector (fderiv ℝ T x) := by
  have hd := ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp x hT.hasFDerivAt).fderiv
  change fderiv ℝ (Prod.fst ∘ T) x = _ at hd
  rw [phaseDerivative,hd]
  rfl

end PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem phase_crossing_first_nonzero (q₀ q₁ q₂ : M)
    (e₀ e₁ e₂ : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he₀ : ContDiff ℝ ∞ e₀) (hi₀ : ContDiff ℝ ∞ e₀.symm)
    (he₁ : ContDiff ℝ ∞ e₁) (hi₁ : ContDiff ℝ ∞ e₁.symm)
    (he₂ : ContDiff ℝ ∞ e₂)
    {p : M} (h₀ : p ∈ (surfacePhaseChart q₀ e₀).source)
    (h₁ : p ∈ (surfacePhaseChart q₁ e₁).source)
    (h₂ : p ∈ (surfacePhaseChart q₂ e₂).source)
    (hcross : covectorDet
      (firstCoordinateCovector (fderiv ℝ (surfacePhaseTransition q₀ e₀ q₁ e₁) (surfacePhaseChart q₀ e₀ p)))
      (firstCoordinateCovector (fderiv ℝ (surfacePhaseTransition q₀ e₀ q₂ e₂) (surfacePhaseChart q₀ e₀ p))) ≠ 0) :
    (fderiv ℝ (surfacePhaseTransition q₁ e₁ q₂ e₂) (surfacePhaseChart q₁ e₁ p) dy).1 ≠ 0 := by
  let L₀₁ := fderiv ℝ (surfacePhaseTransition q₀ e₀ q₁ e₁) (surfacePhaseChart q₀ e₀ p)
  let L₀₂ := fderiv ℝ (surfacePhaseTransition q₀ e₀ q₂ e₂) (surfacePhaseChart q₀ e₀ p)
  let L₁₀ := fderiv ℝ (surfacePhaseTransition q₁ e₁ q₀ e₀) (surfacePhaseChart q₁ e₁ p)
  let v := L₁₀ dy
  have hv : v ≠ 0 := by
    have hI := surfacePhaseTransition_fderiv_injective q₁ q₀ e₁ e₀ he₁ hi₁ he₀ hi₀ h₁ h₀
    intro hz
    have hh : (dy : Base) = 0 := hI (hz.trans (map_zero _).symm)
    exact (show (dy : Base) ≠ 0 by simp [dy]) hh
  have hid := surfacePhaseTransition_fderiv_cocycle q₁ q₀ q₁ e₁ e₀ e₁ hi₁ he₀ hi₀ he₁ h₁ h₀ h₁
  rw [surfacePhaseTransition_self_fderiv q₁ e₁ ((surfacePhaseChart q₁ e₁).map_source h₁)] at hid
  have hv₁ : phaseLinear (firstCoordinateCovector L₀₁) v = 0 := by
    rw [firstCoordinateCovector_apply]
    have hh := congrArg (fun L : Base →L[ℝ] Base => (L dy).1) hid
    exact hh.symm
  have hn := phaseLinear_ne_zero_on_kernel hcross hv hv₁
  rw [firstCoordinateCovector_apply] at hn
  have hc := surfacePhaseTransition_fderiv_cocycle q₁ q₀ q₂ e₁ e₀ e₂ hi₁ he₀ hi₀ he₂ h₁ h₀ h₂
  rw [hc]
  exact hn

end ClosedSurfaceR4

end

end OAI
