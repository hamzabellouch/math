import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexCartanQuotient

namespace OAI

/-! # Real Cartan representatives of the complex adjoint-weight quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

/-- Taking real parts is averaging with the canonical conjugation. -/
theorem complexification_add_conjugate (x : ℂ ⊗[ℝ] L) :
    x + complexificationConjugation L x =
      (complexificationLieHom L) ((2 : ℝ) • complexificationRealPart L x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z y =>
    change z ⊗ₜ[ℝ] y + star z ⊗ₜ[ℝ] y =
      (1 : ℂ) ⊗ₜ[ℝ] ((2 : ℝ) • (z.re • y))
    rw [← TensorProduct.add_tmul, smul_smul, ← TensorProduct.smul_tmul]
    congr 1
    apply Complex.ext <;> simp
    ring
  | add x y hx hy =>
    simp only [map_add, smul_add]
    rw [← hx, ← hy]
    abel

variable {L} {n : ℕ} (T : ComplexTriangularAdjoint L n)

namespace ComplexTriangularAdjoint

/-- Conjugation preserves the common complex weight kernel. -/
theorem complexWeightMap_conjugate_zero {x : ℂ ⊗[ℝ] L}
    (hx : T.complexWeightMap x = 0) :
    T.complexWeightMap (complexificationConjugation L x) = 0 := by
  rw [T.complexWeightMap_eq_zero_iff] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  let c := complexificationConjugation L
  have hi (m : ℕ) (y : ℂ ⊗[ℝ] L) :
      ((ad ℂ (ℂ ⊗[ℝ] L) (c x)) ^ m) (c y) =
        c (((ad ℂ (ℂ ⊗[ℝ] L) x) ^ m) y) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]
      exact (c.map_lie x _).symm
  refine ⟨k, ?_⟩
  apply LinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := c.surjective y
  change ((ad ℂ (ℂ ⊗[ℝ] L) (c x)) ^ k) (c z) = 0
  rw [hi, hk]
  simp

/-- The real part of a vector in the complex weight kernel is in the
original real weight kernel. -/
theorem weightMap_realPart_zero {x : ℂ ⊗[ℝ] L}
    (hx : T.complexWeightMap x = 0) :
    T.weightMap (complexificationRealPart L x) = 0 := by
  have hc := T.complexWeightMap_conjugate_zero hx
  have he := congrArg T.complexWeightMap (complexification_add_conjugate L x)
  rw [map_add, hx, hc, zero_add] at he
  have hr : (2 : ℝ) • T.weightMap (complexificationRealPart L x) = 0 := by
    have hr' : T.weightMap ((2 : ℝ) • complexificationRealPart L x) = 0 := he.symm
    simpa only [map_smul] using hr'
  exact (smul_eq_zero.mp hr).resolve_left (by norm_num)

variable [FiniteDimensional ℝ L] (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- Every real adjoint-weight vector has a real Cartan representative. -/
theorem exists_real_cartan_representative (x : L) :
    ∃ h : H, T.weightMap h = T.weightMap x := by
  obtain ⟨h, hh⟩ := T.exists_complex_cartan_representative H ((1 : ℂ) ⊗ₜ[ℝ] x)
  have hz : T.complexWeightMap (((1 : ℂ) ⊗ₜ[ℝ] x) - h) = 0 := by
    rw [map_sub, hh, sub_self]
  have hr := T.weightMap_realPart_zero hz
  have hm : complexificationRealPart L (h : ℂ ⊗[ℝ] L) ∈ H :=
    ((mem_complexifiedSubalgebra_iff L H _).mp h.property).1
  refine ⟨⟨complexificationRealPart L h, hm⟩, ?_⟩
  have he : T.weightMap x - T.weightMap (complexificationRealPart L h) = 0 := by
    simpa only [map_sub, complexificationRealPart_tmul, Complex.one_re, one_smul] using hr
  exact (sub_eq_zero.mp he).symm

/-- Surjectivity is onto the actual linear image of the adjoint weights. -/
theorem cartan_weightRange_surjective :
    Function.Surjective (fun h : H => T.weightMap.rangeRestrict (h : L)) := by
  rintro ⟨w, x, rfl⟩
  obtain ⟨h, hh⟩ := T.exists_real_cartan_representative H x
  exact ⟨h, Subtype.ext hh⟩

/-- A linear choice of real Cartan representative for each weight vector. -/
def cartanWeightSection : T.weightMap.range →ₗ[ℝ] H :=
  Classical.choose ((T.weightMap.rangeRestrict.comp H.subtype).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (T.cartan_weightRange_surjective H)))

@[simp] theorem cartanWeightSection_weight (w : T.weightMap.range) :
    T.weightMap (T.cartanWeightSection H w : L) = w := by
  have he := Classical.choose_spec
    ((T.weightMap.rangeRestrict.comp H.subtype).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (T.cartan_weightRange_surjective H)))
  exact congrArg Subtype.val (congrArg (fun f : T.weightMap.range →ₗ[ℝ] T.weightMap.range => f w) he)

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
