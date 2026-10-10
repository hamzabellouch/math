import OAI.Geometry.NodalSets.Charts.WeightedCircleSmooth
import OAI.Geometry.NodalSets.Elliptic.IndependentWeightedMatrix

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma matrix_adjugate_smooth (A : E → Matrix n n ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x ↦ A x i j)) (i j : n) :
    ContDiff ℝ ∞ (fun x ↦ (A x).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply matrix_det_smooth
  intro k l
  by_cases hk : k = j
  · subst k; simpa using (contDiff_const (c := (Pi.single i (1:ℝ) : n → ℝ) l) : ContDiff ℝ ∞ (fun _ : E ↦ _))
  · simpa only [Matrix.updateRow_ne hk] using hA k l

lemma matrix_inverse_smooth (A : E → Matrix n n ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x ↦ A x i j)) (hdet : ∀ x, (A x).det ≠ 0) (i j : n) :
    ContDiff ℝ ∞ (fun x ↦ (A x)⁻¹ i j) := by
  have heq : (fun x ↦ (A x)⁻¹ i j) = (fun x ↦ ((A x).det)⁻¹ * (A x).adjugate i j) := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    rfl
  rw [heq]
  exact ((matrix_det_smooth A hA).inv hdet).mul (matrix_adjugate_smooth A hA i j)

lemma independent_weighted_matrix_smooth (A : E → Matrix n n ℝ) (rho gamma0 : E → ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ∀ x, 0 < rho x)
    (hrs : ContDiff ℝ ∞ rho) (hgs : ContDiff ℝ ∞ gamma0) (i j : n ⊕ Fin 1) :
    ContDiff ℝ ∞ (fun x ↦ weightedCircleMatrix (weightedBaseMatrix (A x) (rho x))
      (rho x) (gamma0 x) i j) := by
  apply weightedCircleMatrix_smooth
  · intro i j
    exact hrs.mul (matrix_inverse_smooth A hA (fun x ↦ (hp x).det_pos.ne') i j)
  · intro x; exact weightedBaseMatrix_posDef (hp x) (hr x)
  · exact hrs
  · exact hgs

end
end Yau.Geometry

end OAI
