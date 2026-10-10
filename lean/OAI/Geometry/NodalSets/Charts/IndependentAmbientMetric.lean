import OAI.Geometry.NodalSets.Charts.ManifoldMatrixSmooth
import OAI.Geometry.NodalSets.Charts.TargetWarpedMetric
import OAI.Geometry.NodalSets.Elliptic.AmbientMatrixForm

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def ambientCircleWeight (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ) : ℝ :=
  Real.sqrt A.det / rho

lemma ambientCircleWeight_pos (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) : 0 < ambientCircleWeight A rho :=
  div_pos (Real.sqrt_pos.mpr hA.det_pos) hr

lemma ambientCircleWeight_smooth (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ ambientCircleWeight (A x) (rho x)) := by
  have hd := manifold_positive_sqrt_smooth _ (manifold_matrix_det_smooth A hA)
    (fun x ↦ (hp x).det_pos)
  convert hd.smul (hr.inv₀ (fun x ↦ (hrp x).ne')) using 1
  funext x
  simp [ambientCircleWeight,div_eq_mul_inv]

lemma ambientWeightedBase_smooth (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) :
    ContMDiff (𝓡 4) 𝓘(ℝ,AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞
      (fun x ↦ ambientMatrixForm (weightedBaseMatrix (A x) (rho x))) := by
  apply ambientMatrixForm_smooth
  intro i j
  exact hr.smul (manifold_matrix_inverse_smooth A hA (fun x ↦ (hp x).det_pos.ne') i j)

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)

def independentAmbientMetric : SmoothMetric :=
  ambientWeightedMetric
    (fun x ↦ ambientMatrixForm (weightedBaseMatrix (A x) (rho x)))
    (ambientWeightedBase_smooth A rho hA hp hr)
    (fun x ↦ ambientMatrixForm_symm _ (weightedBaseMatrix_posDef (hp x) (hrp x)).1)
    (fun x ↦ ambientMatrixForm_pos _ (weightedBaseMatrix_posDef (hp x) (hrp x)))
    (fun x ↦ ambientCircleWeight (A x) (rho x))
    (ambientCircleWeight_smooth A rho hA hp hr hrp)
    (fun x ↦ ambientCircleWeight_pos _ (hp x) (hrp x))

lemma independentAmbientMetric_inner (x : Manifold5) (v w : TangentSpace modelWithCorners x) :
    (independentAmbientMetric A rho hA hp hr hrp).inner x v w =
      ambientMatrixForm (weightedBaseMatrix (A x.1) (rho x.1))
        (mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x.1 v.1)
        (mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x.1 w.1) +
      (ambientCircleWeight (A x.1) (rho x.1))^2 * @inner ℝ ℂ _
        (mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 v.2 : ℂ)
        (mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2 w.2 : ℂ) :=
  ambientWeightedMetric_inner ..

end
end Yau.Target

end OAI
