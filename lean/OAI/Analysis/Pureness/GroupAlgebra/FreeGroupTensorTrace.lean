import OAI.Analysis.Pureness.Tensor.SpatialPartialNormBounds
import OAI.Analysis.Pureness.Tensor.SpatialCreationVacuum
import OAI.Analysis.Pureness.Operators.PolarIsometryObstruction
import OAI.Analysis.Pureness.Operators.RowContractionPowers
import OAI.Analysis.Pureness.Tensor.SpatialGroupConjugation
import Mathlib.Analysis.CStarAlgebra.Spectrum

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct CStarAlgebra
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H))

def spatialFreeRowPolynomial {n : ℕ} (a : Fin n → A) :
    representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype :=
  ∑ i, spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
    (a i ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup ℕ) (FreeGroup.of (i : ℕ)) :
      reducedGroupAlgebra (FreeGroup ℕ)))

omit [PartialOrder A] [StarOrderedRing A] in
lemma spatialFreeRowPolynomial_coe {n : ℕ} (a : Fin n → A) :
    (spatialFreeRowPolynomial α a : SpatialHilbert H (GroupL2 (FreeGroup ℕ)) →L[ℂ]
      SpatialHilbert H (GroupL2 (FreeGroup ℕ))) =
        spatialFreeCreationSum α a + spatialFreeCancellationSum α a := by
  rw [spatialFreeTranslation_split]
  change (representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype).subtype
    (spatialFreeRowPolynomial α a) = _
  refine (map_sum (representedSpatialTensor α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype).subtype _ _).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  change spatialStarTensorHom α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
    (a i ⊗ₜ[ℂ] (reducedGroupUnitary (FreeGroup ℕ) (FreeGroup.of (i : ℕ)) :
      reducedGroupAlgebra (FreeGroup ℕ))) = _
  rw [spatialStarTensorHom_tmul]
  rfl

theorem spatialFreeTensor_nonunitary_isometry [Nontrivial H] {n : ℕ} (a : Fin n → A)
    (ha : (∑ i, star (a i) * a i) = 1) (hr : ‖∑ i, a i * star (a i)‖ ≤ 1 / 16) :
    ∃ u : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype,
      star u * u = 1 ∧ u * star u ≠ 1 := by
  have hbounds := @spatialFreePartial_norm_bounds A H _ _ _ _ _ _ α n a ha hr
  let K := SpatialHilbert H (GroupL2 (FreeGroup ℕ))
  have : Nontrivial K := by
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    apply nontrivial_of_ne (spatialVacuumVector x) 0
    intro he
    have hh := congrArg norm he
    rw [spatialVacuumVector_norm, norm_zero] at hh
    exact hx (norm_eq_zero.mp hh)
  have hp := @small_perturbation_near_isometry (K →L[ℂ] K) inferInstance inferInstance
    (spatialFreeCreationSum α a) (spatialFreeCancellationSum α a) hbounds.1 hbounds.2.1 hbounds.2.2
      (spatialFreeCreationSum_not_isUnit α a)
  have hsq := hp.1
  have hy := hp.2
  let S := representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
  let := CStarAlgebra.spectralOrder S
  let := CStarAlgebra.spectralOrderedRing S
  apply nonunitary_isometry_of_nonunit_square (spatialFreeRowPolynomial α a)
  · apply (StarSubalgebra.coe_isUnit S).mp
    change IsUnit (star (spatialFreeRowPolynomial α a : K →L[ℂ] K) *
      (spatialFreeRowPolynomial α a : K →L[ℂ] K))
    simpa only [spatialFreeRowPolynomial_coe] using hsq
  · intro hh
    apply hy
    have hm := hh.map S.subtype
    change IsUnit (spatialFreeRowPolynomial α a : K →L[ℂ] K) at hm
    simpa only [spatialFreeRowPolynomial_coe] using hm

theorem tracialState_of_finite_freeGroup_tensor [Nontrivial H]
    (hfinite : ∀ x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype,
      star x * x = 1 → x * star x = 1) : Nonempty (TracialState A) := by
  by_contra h
  obtain ⟨n, a, ha, hr⟩ := exists_arbitrarily_small_rowFamily h (1 / 16) (by norm_num)
  obtain ⟨u, hu, hnu⟩ := spatialFreeTensor_nonunitary_isometry α a ha hr.le
  exact hnu (hfinite u hu)
end CuntzPureness

end

end OAI
