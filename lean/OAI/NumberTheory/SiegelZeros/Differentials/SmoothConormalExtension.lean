import Mathlib.RingTheory.Smooth.Basic

namespace OAI

namespace SiegelZeros

section

noncomputable section
open TensorProduct
namespace WeightedTorusJets.SmoothConormalExtension

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
variable [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
variable [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]

theorem exists_derivation_extending_conormal
    (hAB : Function.Surjective (algebraMap A B))
    (φ : (RingHom.ker (algebraMap A B)).Cotangent →ₗ[A] B) :
    ∃ D : Derivation K A B, ∀ x : RingHom.ker (algebraMap A B),
      D x = φ (Ideal.toCotangent _ x) := by
  obtain ⟨l, hl⟩ :=
    (Algebra.FormallySmooth.iff_split_injection (R := K) (P := A) (A := B) hAB).mp
      (inferInstance : Algebra.FormallySmooth K B)
  let f : KaehlerDifferential K A →ₗ[A] B :=
    (φ.comp l).comp (TensorProduct.mk A B (KaehlerDifferential K A) 1)
  refine ⟨f.compDer (KaehlerDifferential.D K A), ?_⟩
  intro x
  change φ (l (1 ⊗ₜ[A] KaehlerDifferential.D K A x.1)) =
    φ (Ideal.toCotangent _ x)
  have h := LinearMap.congr_fun hl (Ideal.toCotangent _ x)
  rw [LinearMap.comp_apply, KaehlerDifferential.kerCotangentToTensor_toCotangent,
    LinearMap.id_apply] at h
  exact congrArg φ h

theorem exists_derivation_extending_ideal
    (hAB : Function.Surjective (algebraMap A B))
    (I : Ideal A) (hI : RingHom.ker (algebraMap A B) = I)
    (φ : I.Cotangent →ₗ[A] B) :
    ∃ D : Derivation K A B, ∀ x : I, D x = φ (I.toCotangent x) := by
  subst I
  exact exists_derivation_extending_conormal hAB φ

end WeightedTorusJets.SmoothConormalExtension

end

end

end SiegelZeros

end OAI
