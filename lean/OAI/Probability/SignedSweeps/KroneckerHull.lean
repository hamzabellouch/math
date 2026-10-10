import Mathlib

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped Classical
open Set

lemma kronecker_closed_hull {I J : Type*} [Fintype I] [Fintype J]
    {S : Set (Matrix I I ℂ)} {T : Set (Matrix J J ℂ)}
    {C : Set (Matrix (I × J) (I × J) ℂ)} (hC : IsClosed C) (hV : Convex ℝ C)
    (hST : ∀ A ∈ S, ∀ B ∈ T, Matrix.kroneckerMap (· * ·) A B ∈ C)
    {A : Matrix I I ℂ} (hA : A ∈ closedConvexHull ℝ S)
    {B : Matrix J J ℂ} (hB : B ∈ closedConvexHull ℝ T) :
    Matrix.kroneckerMap (· * ·) A B ∈ C := by
  let f : Matrix I I ℂ →ₗ[ℝ] Matrix (I × J) (I × J) ℂ :=
    { toFun := fun X => Matrix.kroneckerMap (· * ·) X B
      map_add' := fun _ _ => Matrix.add_kronecker _ _ _
      map_smul' := fun _ _ => Matrix.smul_kronecker _ _ _ }
  apply closedConvexHull_min (t := f ⁻¹' C) _ (hV.linear_preimage f)
    (hC.preimage (by dsimp only [f]; fun_prop)) hA
  intro X hX
  let g : Matrix J J ℂ →ₗ[ℝ] Matrix (I × J) (I × J) ℂ :=
    { toFun := fun Y => Matrix.kroneckerMap (· * ·) X Y
      map_add' := fun _ _ => Matrix.kronecker_add _ _ _
      map_smul' := fun _ _ => Matrix.kronecker_smul _ _ _ }
  exact closedConvexHull_min (t := g ⁻¹' C) (hST X hX) (hV.linear_preimage g)
    (hC.preimage (by dsimp only [g]; fun_prop)) hB

end SignedSweeps
end

end OAI
