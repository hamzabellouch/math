import OAI.Analysis.TracialSplitting.NuclearTransfer

namespace OAI

universe uE uF uR

noncomputable section

namespace Pureness

section

open scoped CStarAlgebra

variable {R : Type uR} {E : Type uE} {F : Type uF} [Ring R] [StarAddMonoid R] [Algebra ℂ R]

variable [CStarAlgebra E] [CStarAlgebra F]

variable (f : R →⋆ₐ[ℂ] E) (g : R →⋆ₐ[ℂ] F)

variable (hf : DenseRange f) (hn : ∀ x, ‖g x‖ ≤ ‖f x‖)

def denseStarCompletionHom : E →⋆ₐ[ℂ] F := by
  let L : E →L[ℂ] F := g.toLinearMap.extendOfNorm f.toLinearMap
  have heq (x : R) : L (f x) = g x :=
    LinearMap.extendOfNorm_eq hf ⟨1, fun element => by
      simpa only [AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, one_mul] using hn element⟩ x
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
  LinearMap.extendOfNorm_eq hf ⟨1, fun element => by
    simpa only [AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, one_mul] using hn element⟩ x

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

end

open scoped TensorProduct

universe u v

variable {A : Type u} [CStarAlgebra A] {B : Type v} [CStarAlgebra B]

theorem IsNuclear.representation_norm_le (hA : IsNuclear.{u,v} A)
    {E : Type uE} {F : Type uF} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (z : A ⊗[ℂ] B) : ‖g z‖ ≤ ‖f z‖ := by
  let k := f.prod g
  have hk : Function.Injective k := by
    intro x y h
    apply hf
    exact congrArg Prod.fst h
  have hn := hA.faithful_tensor_norm_eq f k hf hk z
  change ‖f z‖ = ‖(f z,g z)‖ at hn
  rw [Prod.norm_def] at hn
  exact (le_max_right _ _).trans_eq hn.symm

def IsNuclear.extendRepresentation (hA : IsNuclear.{u,v} A)
    {E : Type uE} {F : Type uF} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hfd : DenseRange f) : E →⋆ₐ[ℂ] F :=
  denseStarCompletionHom f g hfd (hA.representation_norm_le f g hf)

lemma IsNuclear.extendRepresentation_apply (hA : IsNuclear.{u,v} A)
    {E : Type uE} {F : Type uF} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hfd : DenseRange f) (z : A ⊗[ℂ] B) :
    hA.extendRepresentation f g hf hfd (f z) = g z :=
  denseStarCompletionHom_apply f g hfd (hA.representation_norm_le f g hf) z

end Pureness

end

end OAI
