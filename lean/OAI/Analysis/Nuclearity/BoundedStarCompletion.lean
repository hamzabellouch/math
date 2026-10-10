import OAI.Analysis.Nuclearity.MinimalTensorExtension

namespace OAI

/-! A fixed finite bound suffices to extend an algebraic star homomorphism.
The extended star homomorphism is then contractive by the C*-identity. -/
noncomputable section
namespace WeakPureInfiniteness

variable {R E F : Type*} [Ring R] [StarAddMonoid R] [Algebra ℂ R]
  [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra F]

def boundedStarCompletion (f : R →⋆ₙₐ[ℂ] E) (g : R →⋆ₙₐ[ℂ] F)
    (hf : DenseRange f) (C : ℝ) (hn : ∀ x, ‖g x‖ ≤ C * ‖f x‖) : E →⋆ₙₐ[ℂ] F := by
  let L : E →L[ℂ] F :=
    (nonUnitalStarLinearMap g).extendOfNorm (nonUnitalStarLinearMap f)
  have he (x : R) : L (f x) = g x :=
    LinearMap.extendOfNorm_eq hf ⟨C, hn⟩ x
  exact {
    toFun := L
    map_zero' := L.map_zero
    map_add' := L.map_add
    map_smul' := L.map_smul
    map_mul' := by
      refine hf.induction_on₂ ?_ ?_
      · exact isClosed_eq (L.continuous.comp continuous_mul)
          ((L.continuous.comp continuous_fst).mul (L.continuous.comp continuous_snd))
      · intro x y
        rw [← map_mul, he, he, he, map_mul]
    map_star' := by
      intro x
      refine hf.induction_on x ?_ ?_
      · exact isClosed_eq (L.continuous.comp continuous_star) L.continuous.star
      · intro y
        rw [← map_star, he, he, map_star] }

lemma boundedStarCompletion_apply (f : R →⋆ₙₐ[ℂ] E) (g : R →⋆ₙₐ[ℂ] F)
    (hf : DenseRange f) (C : ℝ) (hn : ∀ x, ‖g x‖ ≤ C * ‖f x‖) (x : R) :
    boundedStarCompletion f g hf C hn (f x) = g x :=
  LinearMap.extendOfNorm_eq hf ⟨C, hn⟩ x

lemma contractive_of_bounded_star_hom (f : R →⋆ₙₐ[ℂ] E) (g : R →⋆ₙₐ[ℂ] F)
    (hf : DenseRange f) (C : ℝ) (hn : ∀ x, ‖g x‖ ≤ C * ‖f x‖) (x : R) :
    ‖g x‖ ≤ ‖f x‖ := by
  rw [← boundedStarCompletion_apply f g hf C hn x]
  exact NonUnitalStarAlgHom.norm_apply_le _ _

end WeakPureInfiniteness

end

end OAI
