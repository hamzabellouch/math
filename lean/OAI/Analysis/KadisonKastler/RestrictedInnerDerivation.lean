import OAI.Analysis.KadisonKastler.PublishedSimpleDerivation
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI

/-! # Restricting a spatial commutator to an invariant C-star subalgebra

An injective star homomorphism reflects the algebraic identities and the
norm bound. Thus invariance under an ambient commutator gives an actual
bounded derivation on the source algebra.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable {A : Type u} {E : Type v} [CStarAlgebra A] [CStarAlgebra E]

theorem exists_restricted_inner_derivation (φ : A →⋆ₐ[ℂ] E)
    (hφ : Function.Injective φ) (T : E)
    (hrange : ∀ x : A, ∃ y : A, φ y = T * φ x - φ x * T) :
    ∃ D : A →L[ℂ] A,
      (∀ x, φ (D x) = T * φ x - φ x * T) ∧
      (∀ x y, D (x * y) = D x * y + x * D y) ∧
      (IsSelfAdjoint T → ∀ x, D (star x) = -star (D x)) := by
  choose f hf using hrange
  let L : A →ₗ[ℂ] A :=
    { toFun := f
      map_add' := by
        intro x y
        apply hφ
        simp only [hf, map_add]
        noncomm_ring
      map_smul' := by
        intro c x
        apply hφ
        simp only [hf, map_smul, smul_mul_assoc, mul_smul_comm, smul_sub]
        rfl }
  have hL : ∀ x, φ (L x) = T * φ x - φ x * T := hf
  have hbound : ∀ x, ‖L x‖ ≤ (2 * ‖T‖) * ‖x‖ := by
    intro x
    rw [← NonUnitalStarAlgHom.norm_map φ hφ (L x), hL]
    calc
      ‖T * φ x - φ x * T‖ ≤ ‖T * φ x‖ + ‖φ x * T‖ := norm_sub_le _ _
      _ ≤ ‖T‖ * ‖φ x‖ + ‖φ x‖ * ‖T‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = (2 * ‖T‖) * ‖x‖ := by
        rw [NonUnitalStarAlgHom.norm_map φ hφ x]
        ring
  let D := L.mkContinuous (2 * ‖T‖) hbound
  have hD : ∀ x, φ (D x) = T * φ x - φ x * T := hL
  refine ⟨D, hD, ?_, ?_⟩
  · intro x y
    apply hφ
    simp only [map_add, map_mul, hD]
    noncomm_ring
  · intro hT x
    apply hφ
    simp only [map_neg, map_star, hD, star_sub, star_mul, hT.star_eq, neg_sub]

theorem exists_selfAdjoint_ambient_correction
    [Nontrivial A] (hPublished : PublishedSimpleDerivationInner.{u})
    (hSimple : CStarSimple A) (φ : A →⋆ₐ[ℂ] E)
    (hφ : Function.Injective φ) (T : E) (hT : IsSelfAdjoint T)
    (hrange : ∀ x : A, ∃ y : A, φ y = T * φ x - φ x * T) :
    ∃ a : A, IsSelfAdjoint a ∧ ∀ x : A, Commute (T - φ a) (φ x) := by
  obtain ⟨D, hD, hderiv, hstar⟩ := exists_restricted_inner_derivation φ hφ T hrange
  obtain ⟨a, ha, hDa⟩ := exists_selfAdjoint_implementer_of_published
    hPublished hSimple D hderiv (hstar hT)
  refine ⟨a, ha, fun x => ?_⟩
  have h := hD x
  rw [hDa, map_sub, map_mul, map_mul] at h
  change (T - φ a) * φ x = φ x * (T - φ a)
  rw [sub_mul, mul_sub]
  calc
    T * φ x - φ a * φ x = (T * φ x - φ x * T) -
        (φ a * φ x - φ x * φ a) + (φ x * T - φ x * φ a) := by abel
    _ = φ x * T - φ x * φ a := by rw [← h, sub_self, zero_add]

end

end KadisonKastler

end OAI
