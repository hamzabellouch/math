import OAI.Geometry.SurfaceImmersion.Atlas.ChartSecondFormBounds
import OAI.Geometry.SurfaceImmersion.Geometry.PureRadialGauss

namespace OAI

/-! Exact second-form identities through a local smooth coordinate change. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma pure_radial_comp_on {F : RField 4} {φ : Base → Base}
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hφ : ContDiffOn ℝ ∞ φ U)
    {p : Base} (hp : p ∈ U) (hφp : φ p ∈ V)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) (n : RVec 4) (r : ℝ)
    (hB : ∀ v w, realSecondForm F v w (φ p) =
      (r⁻¹*(coordDeriv v F (φ p) ⬝ᵥ coordDeriv w F (φ p))) • n)
    (v w : Base) :
    realSecondForm (F ∘ φ) v w p =
      (r⁻¹*(coordDeriv v (F ∘ φ) p ⬝ᵥ coordDeriv w (F ∘ φ) p)) • n := by
  rw [realSecondForm_comp_on hU hV hF hφ hp hφp v w hD hdet,hB]
  have hf := ((hF _ hφp).contDiffAt (hV.mem_nhds hφp)).differentiableAt (by simp)
  have hg := ((hφ _ hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simp only [coordDeriv,fderiv_comp p hf hg,ContinuousLinearMap.comp_apply]

end ClosedSurfaceR4.RealModes

end

end OAI
