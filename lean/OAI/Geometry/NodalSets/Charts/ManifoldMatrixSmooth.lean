import Mathlib.Geometry.Manifold.Algebra.LieGroup
import OAI.Geometry.NodalSets.Elliptic.IndependentWeightedSmooth

namespace OAI

namespace Yau.Geometry
open Manifold Matrix
open scoped ContDiff
noncomputable section
local instance : ContMDiffMul 𝓘(ℝ,ℝ) ∞ ℝ := by
  constructor
  rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod]
  exact contDiff_mul.contMDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : Type*} [Fintype n] [DecidableEq n]

lemma manifold_matrix_det_smooth (A : M → Matrix n n ℝ)
    (hA : ∀ i j, ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j)) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ (A x).det) := by
  simp only [Matrix.det_apply']
  apply ContMDiff.sum
  intro σ _
  apply contMDiff_const.mul
  apply ContMDiff.prod
  intro i _
  exact hA (σ i) i

lemma manifold_matrix_adjugate_smooth (A : M → Matrix n n ℝ)
    (hA : ∀ i j, ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j)) (i j : n) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ (A x).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply manifold_matrix_det_smooth
  intro k l
  by_cases hk : k = j
  · subst k
    simpa using (contMDiff_const (I := I) (c := (Pi.single i (1:ℝ) : n → ℝ) l))
  · simpa only [Matrix.updateRow_ne hk] using hA k l

lemma manifold_matrix_inverse_smooth (A : M → Matrix n n ℝ)
    (hA : ∀ i j, ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hdet : ∀ x, (A x).det ≠ 0) (i j : n) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ (A x)⁻¹ i j) := by
  have heq : (fun x ↦ (A x)⁻¹ i j) =
      (fun x ↦ ((A x).det)⁻¹ * (A x).adjugate i j) := by
    funext x
    rw [Matrix.inv_def,Ring.inverse_eq_inv]
    rfl
  rw [heq]
  exact ((manifold_matrix_det_smooth A hA).inv₀ hdet).mul
    (manifold_matrix_adjugate_smooth A hA i j)

lemma manifold_positive_sqrt_smooth (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ,ℝ) ∞ f) (hp : ∀ x, 0 < f x) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ Real.sqrt (f x)) := by
  intro x
  exact (ContDiffAt.contMDiffAt (contDiffAt_id.sqrt (hp x).ne')).comp x (hf x)

end
end Yau.Geometry

end OAI
