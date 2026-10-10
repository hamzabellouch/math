import OAI.MeasureTheory.Falconer.Graphs.GraphLiftJacobian
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def graphPolarMap (p : GraphLiftSpace) : GraphLiftSpace :=
  ![p 0*Real.cos (p 1), p 0*Real.sin (p 1), p 2]

noncomputable def graphPolarInverse (x : GraphLiftSpace) : GraphLiftSpace :=
  ![(polarCoord (x 0,x 1)).1, (polarCoord (x 0,x 1)).2, x 2]

def graphPolarDomain : Set GraphLiftSpace :=
  {p | 0 < p 0 ∧ p 1 ∈ Ioo (-Real.pi) Real.pi}

noncomputable def graphPolarMatrix (p : GraphLiftSpace) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos (p 1), -p 0*Real.sin (p 1), 0;
     Real.sin (p 1), p 0*Real.cos (p 1), 0;
     0, 0, 1]

noncomputable def graphPolarDerivative (p : GraphLiftSpace) : GraphLiftSpace →L[ℝ] GraphLiftSpace :=
  (Matrix.toLin' (graphPolarMatrix p)).toContinuousLinearMap

theorem graphPolarMap_hasFDerivAt (p : GraphLiftSpace) :
    HasFDerivAt graphPolarMap (graphPolarDerivative p) p := by
  have h₀ := hasFDerivAt_apply (𝕜 := ℝ) 0 p
  have h₁ := hasFDerivAt_apply (𝕜 := ℝ) 1 p
  have h₂ := hasFDerivAt_apply (𝕜 := ℝ) 2 p
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert! h₀.mul ((Real.hasDerivAt_cos (p 1)).comp_hasFDerivAt p h₁) using 1
    ext vector
    simp [graphPolarDerivative, graphPolarMatrix,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    ring
  · convert! h₀.mul ((Real.hasDerivAt_sin (p 1)).comp_hasFDerivAt p h₁) using 1
    ext vector
    simp [graphPolarDerivative, graphPolarMatrix,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    ring
  · convert! h₂ using 1
    ext vector
    simp [graphPolarDerivative, graphPolarMatrix,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]

theorem graphPolarDerivative_det (p : GraphLiftSpace) : (graphPolarDerivative p).det = p 0 := by
  simp only [graphPolarDerivative, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']
  simp [graphPolarMatrix, Matrix.det_fin_three]
  calc
    _ = p 0*(Real.sin (p 1)^2+Real.cos (p 1)^2) := by ring
    _ = p 0 := by rw [Real.sin_sq_add_cos_sq, mul_one]

theorem graphPolarInverse_left {p : GraphLiftSpace} (hp : p ∈ graphPolarDomain) :
    graphPolarInverse (graphPolarMap p) = p := by
  have he := polarCoord.right_inv (show (p 0,p 1) ∈ polarCoord.target from hp)
  change polarCoord (p 0*Real.cos (p 1),p 0*Real.sin (p 1)) = (p 0,p 1) at he
  ext i
  fin_cases i <;> simp [graphPolarMap, graphPolarInverse, he]

theorem graphPolarMap_injOn : InjOn graphPolarMap graphPolarDomain := by
  intro p hp q hq he
  rw [← graphPolarInverse_left hp, ← graphPolarInverse_left hq, he]

theorem graphPolarMap_lintegral (S : Set GraphLiftSpace) (hS : MeasurableSet S)
    (hdom : S ⊆ graphPolarDomain) (f : GraphLiftSpace → ℝ≥0∞) :
    (∫⁻ x in graphPolarMap '' S, f x) =
      ∫⁻ p in S, ENNReal.ofReal (p 0) * f (graphPolarMap p) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun p (_ : p ∈ S) => (graphPolarMap_hasFDerivAt p).hasFDerivWithinAt)
    (graphPolarMap_injOn.mono hdom)]
  apply setLIntegral_congr_fun hS
  intro p hp
  dsimp only
  rw [graphPolarDerivative_det, abs_of_pos (hdom hp).1]

end PlanarFalconer

end OAI
