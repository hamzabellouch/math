import OAI.Analysis.Pureness.Tensor.SpatialCompletionIndependence

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped CStarAlgebra
variable {R E F : Type*} [Ring R] [StarAddMonoid R] [Algebra ℂ R]
variable [CStarAlgebra E] [CStarAlgebra F]
variable (f : R →⋆ₐ[ℂ] E) (g : R →⋆ₐ[ℂ] F)
variable (hf : DenseRange f) (hn : ∀ x, ‖g x‖ ≤ ‖f x‖)

def denseStarCompletionHom : E →⋆ₐ[ℂ] F := by
  let L : E →L[ℂ] F := g.toLinearMap.extendOfNorm f.toLinearMap
  have heq (x : R) : L (f x) = g x :=
    LinearMap.extendOfNorm_eq hf ⟨1, fun x => by simpa using hn x⟩ x
  exact {
    toFun := L
    map_zero' := L.map_zero
    map_add' := L.map_add
    map_one' := by rw [← map_one f, heq, map_one]
    map_mul' := by
      refine hf.induction_on₂ ?_ ?_
      · exact isClosed_eq (L.continuous.comp continuous_mul)
          ((L.continuous.comp continuous_fst).mul (L.continuous.comp continuous_snd))
      · intro x y
        change L (f x * f y) = L (f x) * L (f y)
        rw [← map_mul, heq, heq, heq, map_mul]
    commutes' := by
      intro c
      rw [← f.commutes]
      change L (f (algebraMap ℂ R c)) = _
      rw [heq]
      exact g.commutes c
    map_star' := by
      intro x
      refine hf.induction_on x ?_ ?_
      · exact isClosed_eq (L.continuous.comp continuous_star) L.continuous.star
      · intro y
        rw [← map_star, heq, heq, map_star] }

lemma denseStarCompletionHom_apply (x : R) :
    denseStarCompletionHom f g hf hn (f x) = g x :=
  LinearMap.extendOfNorm_eq hf ⟨1, fun x => by simpa using hn x⟩ x

lemma denseStarCompletionHom_unique (L : E →⋆ₐ[ℂ] F)
    (hL : ∀ x, L (f x) = g x) : L = denseStarCompletionHom f g hf hn := by
  ext x
  refine hf.induction_on x (isClosed_eq (map_continuous L)
    (map_continuous (denseStarCompletionHom f g hf hn))) ?_
  intro y
  rw [hL, denseStarCompletionHom_apply]

lemma denseStarCompletionHom_denseRange (hg : DenseRange g) :
    DenseRange (denseStarCompletionHom f g hf hn) := by
  apply hg.mono
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, denseStarCompletionHom_apply f g hf hn x⟩
end CuntzPureness

end

end OAI
