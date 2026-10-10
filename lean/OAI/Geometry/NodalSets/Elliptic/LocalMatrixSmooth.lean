import OAI.Geometry.NodalSets.Elliptic.IndependentWeightedSmooth

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma matrix_det_smooth_at (A : E → Matrix n n ℝ) {x : E}
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun z ↦ A z i j) x) :
    ContDiffAt ℝ ∞ (fun z ↦ (A z).det) x := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i _
  exact hA (σ i) i

lemma matrix_adjugate_smooth_at (A : E → Matrix n n ℝ) {x : E}
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun z ↦ A z i j) x) (i j : n) :
    ContDiffAt ℝ ∞ (fun z ↦ (A z).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  apply matrix_det_smooth_at
  intro k l
  by_cases hk : k = j
  · subst k; simpa using (contDiffAt_const (c := (Pi.single i (1:ℝ) : n → ℝ) l) : ContDiffAt ℝ ∞ (fun _ : E ↦ _) x)
  · simpa only [Matrix.updateRow_ne hk] using hA k l

lemma matrix_inverse_smooth_at (A : E → Matrix n n ℝ) {x : E}
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun z ↦ A z i j) x)
    (hdet : (A x).det ≠ 0) (i j : n) :
    ContDiffAt ℝ ∞ (fun z ↦ (A z)⁻¹ i j) x := by
  have heq : (fun z ↦ (A z)⁻¹ i j) =
      (fun z ↦ ((A z).det)⁻¹ * (A z).adjugate i j) := by
    funext z
    rw [Matrix.inv_def,Ring.inverse_eq_inv]
    rfl
  rw [heq]
  exact ((matrix_det_smooth_at A hA).inv hdet).mul (matrix_adjugate_smooth_at A hA i j)

omit [Fintype n] [DecidableEq n] in
lemma matrix_gram_smooth_at (J : E → Matrix m n ℝ) {x : E}
    (hJ : ∀ i j, ContDiffAt ℝ ∞ (fun z ↦ J z i j) x) (i j : n) :
    ContDiffAt ℝ ∞ (fun z ↦ ((J z).transpose * J z) i j) x := by
  simp only [mul_apply,transpose_apply]
  exact ContDiffAt.sum (fun k _ ↦ (hJ k i).mul (hJ k j))

end
end Yau.Geometry

end OAI
