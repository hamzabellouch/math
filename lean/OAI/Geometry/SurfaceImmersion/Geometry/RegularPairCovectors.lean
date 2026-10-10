import OAI.Geometry.SurfaceImmersion.Geometry.CovectorPullbackParameters

namespace OAI

/-! A regular pair of real functions on a surface has independent
coordinate covectors. This is the local form of transverse level curves. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma coordDet_ne_of_surjective (A : CurvePlane →L[ℝ] CurvePlane)
    (hA : Function.Surjective A) : coordDet A ≠ 0 := by
  obtain ⟨x,hx⟩ := hA dx
  obtain ⟨y,hy⟩ := hA dy
  let B : CurvePlane →L[ℝ] CurvePlane :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight x + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight y
  have he : A.comp B = ContinuousLinearMap.id ℝ CurvePlane := by
    apply ContinuousLinearMap.ext
    intro v
    change A (v.1 • x+v.2 • y) = v
    rw [map_add,map_smul,map_smul,hx,hy]
    exact (base_eq_basis v).symm
  have hd := congrArg coordDet he
  rw [coordDet_comp,coordDet_id] at hd
  intro hz
  rw [hz,zero_mul] at hd
  exact zero_ne_one hd

lemma regular_pair_covectors {f g : CurvePlane → ℝ} {x : CurvePlane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hreg : Function.Surjective (fderiv ℝ (fun y => (f y,g y)) x)) :
    covectorDet (phaseDerivative f x) (phaseDerivative g x) ≠ 0 := by
  have h := coordDet_ne_of_surjective _ hreg
  have hd : fderiv ℝ (fun y => (f y,g y)) x = (fderiv ℝ f x).prod (fderiv ℝ g x) :=
    (hf.hasFDerivAt.prodMk hg.hasFDerivAt).fderiv
  rw [hd] at h
  convert h using 1
  dsimp [coordDet,covectorDet,phaseDerivative]
  ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
