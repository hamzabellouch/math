import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.Regularization
import OAI.Analysis.JiangSu.TensorProducts.SimpleCStarAlgebraic

namespace OAI


noncomputable section
namespace Pureness
open scoped TensorProduct

variable {A B N : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra N]
section Simple

variable [Nontrivial A]

theorem commutingStarTensorHom_injective (hsimple : TopologicallySimple A)
    (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N) (hψ : Function.Injective ψ)
    (hc : ∀ a b, Commute (φ a) (ψ b)) :
    Function.Injective (commutingStarTensorHom φ ψ hc) :=
  commutingAlgTensorHom_injective hsimple φ.toAlgHom ψ.toAlgHom hψ hc

variable (hsimple : TopologicallySimple A)
variable (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
variable (hψ : Function.Injective ψ) (hc : ∀ a b, Commute (φ a) (ψ b))

abbrev commutingTensorNormedRing : NormedRing (A ⊗[ℂ] B) :=
  NormedRing.induced _ N (commutingStarTensorHom φ ψ hc)
    (commutingStarTensorHom_injective hsimple φ ψ hψ hc)

abbrev commutingTensorNormedAlgebra :
    letI := commutingTensorNormedRing hsimple φ ψ hψ hc
    NormedAlgebra ℂ (A ⊗[ℂ] B) := by
  letI := commutingTensorNormedRing hsimple φ ψ hψ hc
  exact
  NormedAlgebra.induced ℂ _ N (commutingStarTensorHom φ ψ hc)

theorem commutingTensorCStarRing :
    letI := commutingTensorNormedRing hsimple φ ψ hψ hc
    CStarRing (A ⊗[ℂ] B) := by
  let := commutingTensorNormedRing hsimple φ ψ hψ hc
  refine ⟨fun z => ?_⟩
  change ‖commutingStarTensorHom φ ψ hc z‖*‖commutingStarTensorHom φ ψ hc z‖ ≤
      ‖commutingStarTensorHom φ ψ hc (star z*z)‖
  rw [map_mul,map_star,CStarRing.norm_star_mul_self]

lemma commutingTensor_norm_def (z : A ⊗[ℂ] B) :
    letI := commutingTensorNormedRing hsimple φ ψ hψ hc
    ‖z‖ = ‖commutingStarTensorHom φ ψ hc z‖ := rfl

lemma commutingTensor_norm_tmul_le (a : A) (b : B) :
    letI := commutingTensorNormedRing hsimple φ ψ hψ hc
    ‖a ⊗ₜ[ℂ] b‖ ≤ ‖a‖*‖b‖ := by
  change ‖φ a*ψ b‖ ≤ ‖a‖*‖b‖
  exact (norm_mul_le _ _).trans (mul_le_mul
    (NonUnitalStarAlgHom.norm_apply_le φ.toNonUnitalStarAlgHom a)
    (NonUnitalStarAlgHom.norm_apply_le ψ.toNonUnitalStarAlgHom b)
    (norm_nonneg _) (norm_nonneg _))

end Simple


variable (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
variable (hc : ∀ a b, Commute (φ a) (ψ b))

def commutingTensorClosureMap : A ⊗[ℂ] B →⋆ₐ[ℂ] commutingTensorClosure φ ψ hc :=
  (commutingStarTensorHom φ ψ hc).codRestrict _
    (fun z => StarSubalgebra.le_topologicalClosure _ ⟨z,rfl⟩)

lemma commutingTensorClosureMap_coe (z : A ⊗[ℂ] B) :
    (commutingTensorClosureMap φ ψ hc z : N) = commutingStarTensorHom φ ψ hc z := rfl

lemma commutingTensorClosureMap_injective [Nontrivial A]
    (hsimple : TopologicallySimple A) (hψ : Function.Injective ψ) :
    Function.Injective (commutingTensorClosureMap φ ψ hc) := by
  intro x y h
  exact commutingStarTensorHom_injective hsimple φ ψ hψ hc (congrArg Subtype.val h)

lemma commutingTensorClosureMap_denseRange :
    DenseRange (commutingTensorClosureMap φ ψ hc) := by
  have hd : DenseRange (Set.inclusion
      (StarSubalgebra.le_topologicalClosure (commutingStarTensorHom φ ψ hc).range)) := by
    exact (denseRange_inclusion_iff _).2 subset_rfl
  have hs : Function.Surjective (commutingStarTensorHom φ ψ hc).rangeRestrict := by
    rintro ⟨x,z,hz⟩
    exact ⟨z,Subtype.ext hz⟩
  exact hd.comp hs.denseRange (continuous_inclusion _)

lemma commutingTensorClosureMap_isometry [Nontrivial A]
    (hsimple : TopologicallySimple A) (hψ : Function.Injective ψ) :
    letI := commutingTensorNormedRing hsimple φ ψ hψ hc
    Isometry (commutingTensorClosureMap φ ψ hc) := by
  let := commutingTensorNormedRing hsimple φ ψ hψ hc
  apply AddMonoidHomClass.isometry_of_norm
  intro z
  rfl

lemma commutingTensorClosure_eq_generated :
    commutingTensorClosure φ ψ hc =
      (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range ψ)).topologicalClosure := by
  apply le_antisymm
  · apply StarSubalgebra.topologicalClosure_minimal
      _ (StarSubalgebra.isClosed_topologicalClosure _)
    rintro _ ⟨z,rfl⟩
    apply StarSubalgebra.le_topologicalClosure
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change φ a*ψ b ∈ StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range ψ)
      apply mul_mem
      · exact StarAlgebra.subset_adjoin (R := ℂ) _ (Set.mem_union_left _ ⟨a,rfl⟩)
      · exact StarAlgebra.subset_adjoin (R := ℂ) _ (Set.mem_union_right _ ⟨b,rfl⟩)
    | add x y hx hy =>
      rw [map_add]
      exact add_mem hx hy
  · apply StarSubalgebra.topologicalClosure_minimal _ (commutingTensorClosure_closed φ ψ hc)
    apply StarAlgebra.adjoin_le
    rintro x (⟨a,rfl⟩ | ⟨b,rfl⟩)
    · exact StarSubalgebra.le_topologicalClosure _ ⟨a ⊗ₜ[ℂ] (1 : B),by
        simp [commutingStarTensorHom_tmul]⟩
    · exact StarSubalgebra.le_topologicalClosure _ ⟨(1 : A) ⊗ₜ[ℂ] b,by
        simp [commutingStarTensorHom_tmul]⟩

open scoped TensorProduct InnerProductSpace

variable {R E F : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
variable [CStarAlgebra E] [CStarAlgebra F]
variable (f : R →⋆ₐ[ℂ] E) (g : R →⋆ₐ[ℂ] F)
variable (hf : DenseRange f) (hg : DenseRange g) (hn : ∀ x, ‖g x‖ = ‖f x‖)

def denseStarCompletionLinearEquiv : E ≃ₗᵢ[ℂ] F :=
  (LinearEquiv.refl ℂ R).extendOfIsometry f.toLinearMap g.toLinearMap hf hg hn

lemma denseStarCompletionLinearEquiv_apply (x : R) :
    denseStarCompletionLinearEquiv f g hf hg hn (f x) = g x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ hf hg hn x

def denseStarCompletionEquiv : E ≃⋆ₐ[ℂ] F where
  __ := (denseStarCompletionLinearEquiv f g hf hg hn).toLinearEquiv
  map_mul' := by
    let L := denseStarCompletionLinearEquiv f g hf hg hn
    refine hf.induction_on₂ ?_ ?_
    · exact isClosed_eq (L.continuous.comp continuous_mul)
        ((L.continuous.comp continuous_fst).mul (L.continuous.comp continuous_snd))
    · intro x y
      change L (f x * f y) = L (f x) * L (f y)
      have heq := denseStarCompletionLinearEquiv_apply f g hf hg hn
      rw [← map_mul, heq, heq, heq, map_mul]
  map_star' := by
    intro x
    let L := denseStarCompletionLinearEquiv f g hf hg hn
    refine hf.induction_on x ?_ ?_
    · exact isClosed_eq (L.continuous.comp continuous_star) L.continuous.star
    · intro y
      change L (star (f y)) = star (L (f y))
      have heq := denseStarCompletionLinearEquiv_apply f g hf hg hn
      rw [← map_star, heq, heq, map_star]

lemma denseStarCompletionEquiv_apply (x : R) :
    denseStarCompletionEquiv f g hf hg hn (f x) = g x :=
  denseStarCompletionLinearEquiv_apply f g hf hg hn x

lemma denseStarCompletionEquiv_norm (x : E) :
    ‖denseStarCompletionEquiv f g hf hg hn x‖ = ‖x‖ :=
  (denseStarCompletionLinearEquiv f g hf hg hn).norm_map x
end Pureness

end

end OAI
