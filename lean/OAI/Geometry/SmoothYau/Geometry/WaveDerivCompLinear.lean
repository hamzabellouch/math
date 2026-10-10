import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.WaveDeriv

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma waveDeriv_comp_linear (A : E →L[ℝ] F) {f : F → ℂ}
    (hf : Differentiable ℝ f) (v x : E) :
    waveDeriv v (f ∘ A) x = waveDeriv (A v) f (A x) := by
  simp only [waveDeriv, fderiv_comp x (hf _) A.differentiableAt,
    ContinuousLinearMap.comp_apply, A.fderiv]

lemma waveCoordinateOperator_comp_linear (A : E →L[ℝ] F)
    (e : Fin 3 → E) (g : Fin 3 → Fin 3 → F → ℂ) (b : Fin 3 → F → ℂ)
    {f : F → ℂ} (hf : ContDiff ℝ ∞ f) (x : E) :
    waveCoordinateOperator e (fun i j => g i j ∘ A) (fun i => b i ∘ A) (f ∘ A) x =
      waveCoordinateOperator (fun i => A (e i)) g b f (A x) := by
  have hD (i : Fin 3) : waveDeriv (e i) (f ∘ A) = waveDeriv (A (e i)) f ∘ A := by
    funext y
    exact waveDeriv_comp_linear A (hf.differentiable (by simp)) (e i) y
  simp only [waveCoordinateOperator, hD, Function.comp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [waveDeriv_comp_linear A ((contDiff_waveDeriv _ _ hf).differentiable (by simp))]
end YauCounterexamples

end

end OAI
