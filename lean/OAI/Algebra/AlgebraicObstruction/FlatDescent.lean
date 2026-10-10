import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
open TensorProduct
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]

theorem mem_of_tmul_mem_baseChange (U : Submodule A N) (x : N)
    (hx : (1 : B) ⊗ₜ[A] x ∈ U.baseChange B) : x ∈ U := by
  apply (Submodule.Quotient.mk_eq_zero U).mp
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) (N ⧸ U)
  change (1 : B) ⊗ₜ[A] (U.mkQ x) = (1 : B) ⊗ₜ[A] (0 : N ⧸ U)
  obtain ⟨y,hy⟩ := hx
  have he : U.mkQ.baseChange B ∘ₗ U.subtype.baseChange B = 0 := by
    ext scalar
    simp
  calc
    (1 : B) ⊗ₜ[A] (U.mkQ x) = U.mkQ.baseChange B ((1 : B) ⊗ₜ[A] x) := rfl
    _ = U.mkQ.baseChange B (U.subtype.baseChange B y) := by rw [hy]
    _ = 0 := LinearMap.congr_fun he y
    _ = (1 : B) ⊗ₜ[A] (0 : N ⧸ U) := by simp

theorem whole_tuple_descends (f : M →ₗ[A] N) (x : N)
    (hx : (1 : B) ⊗ₜ[A] x ∈ (LinearMap.range f).baseChange B) :
    ∃ y : M, f y = x :=
  mem_of_tmul_mem_baseChange (LinearMap.range f) x hx

theorem kernel_baseChange (f : M →ₗ[A] N) :
    (LinearMap.ker f).baseChange B = LinearMap.ker (f.baseChange B) := by
  have h : Function.Exact (LinearMap.ker f).subtype f := by
    rw [LinearMap.exact_iff]
    simp
  have hb := Module.Flat.lTensor_exact B h
  ext x
  exact (hb x).symm

end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement
open TensorProduct
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

lemma ideal_baseChange_rid (I : Ideal A) :
    (I.baseChange B).map (AlgebraTensorModule.rid A B B).toLinearMap =
      I.map (algebraMap A B) := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  change Submodule.span B
    ((AlgebraTensorModule.rid A B B) ''
      (TensorProduct.mk A B A 1 '' (I : Set A))) = _
  rw [Set.image_image]
  change Submodule.span B ((fun a : A ↦ a • (1 : B)) '' (I : Set A)) = _
  simp only [Algebra.smul_def, mul_one]
  rfl

lemma tmul_one_mem_ideal_baseChange_iff (I : Ideal A) (b : B) :
    b ⊗ₜ[A] (1 : A) ∈ I.baseChange B ↔ b ∈ I.map (algebraMap A B) := by
  rw [← ideal_baseChange_rid]
  constructor
  · intro h
    exact ⟨b ⊗ₜ[A] (1 : A), h, by simp⟩
  · rintro ⟨x,hx,h⟩
    have he : x = b ⊗ₜ[A] (1 : A) := by
      apply (AlgebraTensorModule.rid A B B).injective
      simpa using h
    rwa [he] at hx

end BoundaryOnly.FormalObstruction.AlgebraicReplacement

end

end OAI
