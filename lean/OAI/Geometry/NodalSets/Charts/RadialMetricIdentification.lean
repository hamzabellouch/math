import OAI.Geometry.NodalSets.Charts.IndependentAmbientMetric
import OAI.Geometry.NodalSets.Elliptic.RadialVolumeMatrix

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section
local instance : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

def sphereAmbientDerivative (x : Base) : TangentSpace (𝓡 4) x →L[ℝ] AmbientBase :=
  mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x

lemma sphere_derivative_radial_orthogonal (x : Base) (v : TangentSpace (𝓡 4) x) :
    (fun i ↦ (x : AmbientBase) i) ⬝ᵥ
      (fun i ↦ (sphereAmbientDerivative x v) i) = 0 := by
  have hm : (sphereAmbientDerivative x v) ∈
      (ℝ ∙ (x : AmbientBase))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := 4) x]
    exact ⟨v,rfl⟩
  have hi := (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℝ) (E := AmbientBase)).mp hm
  simpa [PiLp.inner_apply,dotProduct,mul_comm] using hi

lemma ambientMatrixForm_dot (A : Matrix (Fin 5) (Fin 5) ℝ) (v w : AmbientBase) :
    ambientMatrixForm A v w = (fun i ↦ v i) ⬝ᵥ (A *ᵥ (fun i ↦ w i)) := by
  rw [ambientMatrixForm_apply]
  simp [dotProduct,mulVec,Finset.mul_sum,mul_assoc]

lemma radialVolumeMatrix_sphere_form (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ)
    (x : Base) (v : AmbientBase) (w : TangentSpace (𝓡 4) x) :
    ambientMatrixForm (radialVolumeMatrix A rho (fun i ↦ (x : AmbientBase) i)) v
      (sphereAmbientDerivative x w) =
    ambientMatrixForm (weightedBaseMatrix A rho) v
      (sphereAmbientDerivative x w) := by
  rw [ambientMatrixForm_dot,ambientMatrixForm_dot,
    radialVolumeMatrix_tangent _ _ _ _ (sphere_derivative_radial_orthogonal x w)]

lemma radialVolumeMatrix_sqrt (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (x : Fin 5 → ℝ)
    (hx : A *ᵥ x = x) (hn : x ⬝ᵥ x = 1) :
    Real.sqrt (radialVolumeMatrix A rho x).det = rho^2 / Real.sqrt A.det := by
  rw [radialVolumeMatrix_det A hA hr x hx hn,Real.sqrt_div (by positivity)]
  have he : rho^4 = (rho^2)^2 := by ring
  rw [he,Real.sqrt_sq (sq_nonneg rho)]

lemma ambientCircleWeight_radial_volume (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (x : Fin 5 → ℝ)
    (hx : A *ᵥ x = x) (hn : x ⬝ᵥ x = 1) :
    ambientCircleWeight A rho = rho / Real.sqrt (radialVolumeMatrix A rho x).det := by
  rw [radialVolumeMatrix_sqrt A hA hr x hx hn,ambientCircleWeight]
  field_simp

end
end Yau.Target

end OAI
