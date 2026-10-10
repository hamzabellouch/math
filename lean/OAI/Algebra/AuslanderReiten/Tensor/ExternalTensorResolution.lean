import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorSingle
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]

def augmentation : complex k A B P.complex Q.complex ⟶
    (ChainComplex.single₀ (ModuleCat (A ⊗[k] B))).obj (moduleObject k A B M N) :=
  mapBifunctorMap P.π Q.π (bifunctor k A B) (ComplexShape.down ℕ) ≫
    (singleTotalIso k A B M N).hom

def projectiveResolution : ProjectiveResolution (moduleObject k A B M N) where
  complex := complex k A B P.complex Q.complex
  projective n := by
    have : Module.Projective (A ⊗[k] B) ((complex k A B P.complex Q.complex).X n) :=
      term_projective k A B P.complex Q.complex n
    infer_instance
  π := augmentation k A B P Q
  quasiIso := by
    have := map_quasiIso k A B P.π Q.π
    change QuasiIso (mapBifunctorMap P.π Q.π (bifunctor k A B) (ComplexShape.down ℕ) ≫
      (singleTotalIso k A B M N).hom)
    infer_instance

theorem differential_exact (n : ℕ) :
    Function.Exact ((complex k A B P.complex Q.complex).d (n+2) (n+1)).hom
      ((complex k A B P.complex Q.complex).d (n+1) n).hom := by
  have h := (projectiveResolution k A B P Q).exact_succ n
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  exact h

theorem augmentation_surjective : Function.Surjective ((augmentation k A B P Q).f 0) :=
  (ModuleCat.epi_iff_surjective ((projectiveResolution k A B P Q).π.f 0)).mp inferInstance

end ArExplicit.ExternalTensor

end

end OAI
