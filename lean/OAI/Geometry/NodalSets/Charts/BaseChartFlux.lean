import OAI.Geometry.NodalSets.Charts.ChartFrameSmooth
import OAI.Geometry.NodalSets.Charts.ProductChartPullback
import OAI.Geometry.NodalSets.Elliptic.LocalMatrixSmooth

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def baseChartMetric (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (p : Base) (z : BaseModel) : Matrix (Fin 4) (Fin 4) ℝ :=
  sphereWeightedChartMatrix (A ((extChartAt (𝓡 4) p).symm z))
    (rho ((extChartAt (𝓡 4) p).symm z)) p z

def roundChartDensity (p : Base) (z : BaseModel) : ℝ :=
  Real.sqrt (sphereRoundChartMatrix p z).det

def baseChartDensity (rho : Base → ℝ) (p : Base) (z : BaseModel) : ℝ :=
  rho ((extChartAt (𝓡 4) p).symm z) * roundChartDensity p z

def baseChartFlux (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (f : Base → ℝ) (p : Base) (i : Fin 4) (z : BaseModel) : ℝ :=
  baseChartDensity rho p z * ∑ j, (baseChartMetric A rho p z)⁻¹ i j *
    fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) z (EuclideanSpace.basisFun (Fin 4) ℝ j)

lemma roundChartDensity_pos (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) : 0 < roundChartDensity p z :=
  Real.sqrt_pos.mpr (sphereRoundChartMatrix_posDef p hz).det_pos

lemma roundChartDensity_smooth_at (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (roundChartDensity p) z := by
  exact (matrix_det_smooth_at _ (matrix_gram_smooth_at _ (sphereChartFrame_smooth_at p hz))).sqrt
    (sphereRoundChartMatrix_posDef p hz).det_pos.ne'

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)

include hA hp hr in
lemma baseChartMetric_smooth_at (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w ↦ baseChartMetric A rho p w i j) z := by
  have ha (i j : Fin 5) := smooth_inverse_chart_comp _ (hA i j) p hz
  have hi := matrix_inverse_smooth_at (fun w ↦ A ((extChartAt (𝓡 4) p).symm w)) ha
    (hp _).det_pos.ne'
  have hw (i j : Fin 5) : ContDiffAt ℝ ∞
      (fun w ↦ weightedBaseMatrix (A ((extChartAt (𝓡 4) p).symm w))
        (rho ((extChartAt (𝓡 4) p).symm w)) i j) z :=
    (smooth_inverse_chart_comp rho hr p hz).mul (hi i j)
  simp only [baseChartMetric,sphereWeightedChartMatrix,mul_apply,transpose_apply]
  apply ContDiffAt.sum
  intro k _
  apply ContDiffAt.mul
  · apply ContDiffAt.sum
    intro l _
    exact (sphereChartFrame_smooth_at p hz l i).mul (hw l k)
  · exact sphereChartFrame_smooth_at p hz k j

include hA hp hr hrp in
lemma baseChartMetric_inverse_smooth_at (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w ↦ (baseChartMetric A rho p w)⁻¹ i j) z := by
  apply matrix_inverse_smooth_at _ (baseChartMetric_smooth_at A rho hA hp hr p hz)
  exact (sphereWeightedChartMatrix_posDef _ (hp _) (hrp _) p hz).det_pos.ne'

include hr in
lemma baseChartDensity_smooth_at (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (baseChartDensity rho p) z :=
  (smooth_inverse_chart_comp rho hr p hz).mul (roundChartDensity_smooth_at p hz)

include hA hp hr hrp in
lemma baseChartFlux_smooth_at (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i : Fin 4) :
    ContDiffAt ℝ ∞ (baseChartFlux A rho f p i) z := by
  apply (baseChartDensity_smooth_at rho hr p hz).mul
  apply ContDiffAt.sum
  intro j _
  exact (baseChartMetric_inverse_smooth_at A rho hA hp hr hrp p hz i j).mul
    ((smooth_inverse_chart_derivative f hf p hz).clm_apply contDiffAt_const)

end
end Yau.Target

end OAI
