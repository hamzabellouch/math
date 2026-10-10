import OAI.Geometry.NodalSets.Charts.CircleLaplacian
import OAI.Geometry.NodalSets.Charts.SphereContravariant

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section

def sphereChartTensor (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (p : Base) (z : BaseModel) : Matrix (Fin 4) (Fin 4) ℝ :=
  frameContravariant (A ((extChartAt (𝓡 4) p).symm z)) (sphereChartFrame p z)

def roundTensorFlux (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (f : Base → ℝ) (p : Base) (i : Fin 4) (z : BaseModel) : ℝ :=
  roundChartDensity p z * ∑ j, sphereChartTensor A p z i j *
    fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) z (EuclideanSpace.basisFun (Fin 4) ℝ j)

def ambientWeightedChartOperator (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (rho : Base → ℝ) (f : Base → ℝ) (p : Base) (z : BaseModel) : ℝ :=
  (rho ((extChartAt (𝓡 4) p).symm z))⁻¹ * (roundChartDensity p z)⁻¹ *
    ∑ i, fderiv ℝ (roundTensorFlux A f p i) z (EuclideanSpace.basisFun (Fin 4) ℝ i)

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))

include hp hrp hrad in
lemma baseChartFlux_eq_roundTensorFlux (f : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i : Fin 4) :
    baseChartFlux A rho f p i z = roundTensorFlux A f p i z := by
  unfold baseChartFlux roundTensorFlux sphereChartTensor
  rw [sphereChart_contravariant _ (hp _) (hrp _) p hz (hrad _)]
  simp only [Matrix.smul_apply,smul_eq_mul,baseChartMetric,baseChartDensity,
    mul_assoc,← Finset.mul_sum]
  ring

include hp hrp hrad in
lemma baseChartFlux_eq_roundTensorFlux_eventually (f : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i : Fin 4) :
    baseChartFlux A rho f p i =ᶠ[𝓝 z] roundTensorFlux A f p i := by
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with w hw
  exact baseChartFlux_eq_roundTensorFlux A rho hp hrp hrad f p hw i

include hrad in
lemma independentAmbientMetric_weighted_lift (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    chartLaplacian (independentAmbientMetric A rho hA hp hr hrp)
      (extChartAt modelWithCorners p) (circleLift f) y =
    ambientWeightedChartOperator A rho f p.1 y.1 := by
  rw [independentAmbientMetric_circle_laplacian A rho hA hp hr hrp hrad f hf p hy]
  have hd (i : Fin 4) := (baseChartFlux_eq_roundTensorFlux_eventually A rho hp hrp hrad f p.1
    (product_chart_target p hy).1 i).fderiv_eq (𝕜 := ℝ)
  simp_rw [hd]
  unfold ambientWeightedChartOperator baseChartDensity
  rw [_root_.mul_inv_rev]
  ring

end
end Yau.Target

end OAI
