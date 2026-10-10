import OAI.Analysis.KadisonSimilarity.Similarity.SimilarityRetract

namespace OAI

/-! Restriction of a bounded homomorphism to a closed invariant subspace.
Similarity passes to this restriction through its orthogonal compression. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def restrictBoundedHom (π : BoundedUnitalHom A H) (M : ClosedSubmodule ℂ H)
    (hM : ∀ a x, x ∈ M → π.1 a x ∈ M) : BoundedUnitalHom A M := by
  let ρ : A →ₐ[ℂ] (M →L[ℂ] M) := {
    toFun := fun a => (π.1 a).restrict (hM a)
    map_zero' := by ext x; simp
    map_one' := by ext x; simp
    map_add' := by intro a b; ext x; simp
    map_mul' := by intro a b; ext x; simp [mul_apply_eq_comp]
    commutes' := by intro c; ext x; simp [Algebra.algebraMap_eq_smul_one] }
  let f : A →L[ℂ] (H →L[ℂ] H) := ⟨π.1.toLinearMap, π.2⟩
  have hn (a : A) : ‖ρ a‖ ≤ ‖f‖ * ‖a‖ := by
    apply opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro x
    change ‖π.1 a (x : H)‖ ≤ _
    exact ((π.1 a).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (f.le_opNorm a) (norm_nonneg x))
  exact ⟨ρ, (ρ.toLinearMap.mkContinuous ‖f‖ hn).continuous⟩

@[simp] theorem restrictBoundedHom_apply (π : BoundedUnitalHom A H)
    (M : ClosedSubmodule ℂ H) (hM : ∀ a x, x ∈ M → π.1 a x ∈ M) (a : A) (x : M) :
    ((restrictBoundedHom π M hM).1 a x : H) = π.1 a x := rfl

theorem restrictBoundedHom_bound (π : BoundedUnitalHom A H)
    (M : ClosedSubmodule ℂ H) (hM : ∀ a x, x ∈ M → π.1 a x ∈ M)
    {C : ℝ} (hC : 0 ≤ C) (hπ : ∀ a, ‖π.1 a‖ ≤ C * ‖a‖) (a : A) :
    ‖(restrictBoundedHom π M hM).1 a‖ ≤ C * ‖a‖ := by
  apply opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro x
  change ‖π.1 a (x : H)‖ ≤ _
  exact ((π.1 a).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hπ a) (norm_nonneg x))

theorem similarity_restrictBoundedHom (π : BoundedUnitalHom A H)
    (M : ClosedSubmodule ℂ H) (hM : ∀ a x, x ∈ M → π.1 a x ∈ M)
    (hπ : SimilarToStar A H π) : SimilarToStar A M (restrictBoundedHom π M hM) := by
  apply similarity_of_retract (restrictBoundedHom π M hM) π
    M.toSubmodule.subtypeL M.toSubmodule.orthogonalProjectionOnto ?_ hπ
  intro a
  ext x
  change M.toSubmodule.starProjection (π.1 a (x : H)) = π.1 a (x : H)
  exact Submodule.starProjection_eq_self_iff.mpr (hM a x x.property)

end KadisonSimilarity

end

end OAI
