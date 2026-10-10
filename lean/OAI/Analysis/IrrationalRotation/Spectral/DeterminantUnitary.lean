import OAI.Analysis.IrrationalRotation.Spectral.SpectralNaturality

namespace OAI

noncomputable section
namespace Invariant233
open scoped ENNReal CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

theorem TracialState.unitary_conj (τ : TracialState A) (u : unitary A) (a : A) :
    τ ((u : A) * a * star (u : A)) = τ a := by
  rw [τ.tracial, ← mul_assoc, Unitary.star_mul_self_of_mem u.property, one_mul]

theorem fugledeKadisonDeterminant_unitary_conj
    (τ : TracialState A) (u : unitary A) (a : A) :
    fugledeKadisonDeterminant τ ((u : A) * a * star (u : A)) =
      fugledeKadisonDeterminant τ a := by
  exact fugledeKadisonDeterminant_map
    (Unitary.conjStarAlgAut ℂ A u).toStarAlgHom τ τ
    (fun b => τ.unitary_conj u b) a

theorem fugledeKadisonDeterminant_mul_unitary
    (τ : TracialState A) (u : unitary A) (a : A) :
    fugledeKadisonDeterminant τ (a * (u : A)) =
      fugledeKadisonDeterminant τ a := by
  have h := fugledeKadisonDeterminant_unitary_conj τ u (a * (u : A))
  have he : (u : A) * (a * (u : A)) * star (u : A) = (u : A) * a := by
    simp only [mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]
  rw [he, fugledeKadisonDeterminant_unitary_mul] at h
  exact h.symm

theorem IsBrownMeasure.unitary_conj
    (τ : TracialState A) {a : A} {μ : MeasureTheory.Measure ℂ}
    (h : IsBrownMeasure τ a μ) (u : unitary A) :
    IsBrownMeasure τ ((u : A) * a * star (u : A)) μ := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro z
  let φ : A →⋆ₐ[ℂ] A := (Unitary.conjStarAlgAut ℂ A u).toStarAlgHom
  have he : (u : A) * a * star (u : A) - algebraMap ℂ A z =
      φ (a - algebraMap ℂ A z) := by
    simp only [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    rfl
  rw [he, fugledeKadisonDeterminant_map φ τ τ (fun b => τ.unitary_conj u b)]
  exact h.2.2 z

end Invariant233

end

end OAI
