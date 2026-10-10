import OAI.Geometry.NodalSets.Waves.GaussianWaveJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma gaussianWaveField_differentiable (V : ι → Coord → ℂ) (a : ι × Fin 2 → ℝ)
    (x : Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x) :
    DifferentiableAt ℝ (gaussianWaveField V a) x := by
  classical
  change DifferentiableAt ℝ (Complex.reCLM ∘ (fun z ↦ ∑ i, gaussianCoefficient a i*V i z)) x
  exact Complex.reCLM.differentiableAt.comp x (DifferentiableAt.fun_sum (fun i _ ↦ (hV i).const_mul _))

lemma seeded_gaussian_dual_variance (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (x v : Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x) (hseed : DifferentiableAt ℝ seed x)
    (N S b : ℝ) :
    Var[(fun a : ι × Fin 2 → ℝ ↦ Real.exp (-N*S)*(b*(seed x+gaussianWaveField V a x)+
      N⁻¹*fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z) x v)); gaussianPairs] =
      ∑ i, ‖dualWaveCoefficient N (V i) S x b v‖^2 := by
  let z := fun i ↦ dualWaveCoefficient N (V i) S x b v
  let mean := Real.exp (-N*S)*(b*seed x+N⁻¹*fderiv ℝ seed x v)
  have he : (fun a : ι × Fin 2 → ℝ ↦ Real.exp (-N*S)*(b*(seed x+gaussianWaveField V a x)+
      N⁻¹*fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z) x v)) =
      fun a ↦ mean+pairLinearSum z a := by
    funext a
    rw [fderiv_fun_add hseed (gaussianWaveField_differentiable V a x hV),add_apply]
    have h := gaussianWaveField_dual V a x v hV N S b
    change _ = mean+pairLinearSum z a
    rw [← h]
    dsimp [mean]
    ring
  rw [he]
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : ι × Fin 2 ↦ gaussianReal 0 1))
    infer_instance
  have hc : Continuous (pairLinearSum z) := by
    unfold pairLinearSum
    fun_prop
  rw [variance_const_add hc.aestronglyMeasurable]
  exact variance_pairLinearSum _

end
end Yau.Geometry

end OAI
