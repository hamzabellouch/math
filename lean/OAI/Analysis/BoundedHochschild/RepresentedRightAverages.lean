import OAI.Analysis.BoundedHochschild.OperatorRowAverages
import OAI.Analysis.BoundedHochschild.NormalGNSMatrices

namespace OAI

/-! Apply the constructed operator factorization to the given normal faithful
representation, and lift elementary right averages to the factorization space. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem normalGNS_nontrivial [Nontrivial M] (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Nontrivial (NormalGNS e) := by
  by_contra h
  let : Subsingleton (NormalGNS e) := not_nontrivial_iff_subsingleton.mp h
  exact one_ne_zero ((normalGNSRepresentation_injective e) (Subsingleton.elim
    (normalGNSRepresentation e 1) (normalGNSRepresentation e 0)))

variable {I H K : Type*} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem represented_factorization [Nontrivial M] [Nontrivial H]
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : M →L[ℂ] M)
    {C : ℝ} (hC : 0 < C) (hT : CompletelyBoundedEstimate T C) :
    Nonempty (OperatorFactorization (σ.toLinearMap.comp T.toLinearMap) C) := by
  apply factorization_of_complete_bound _ hC
  intro n A
  have he : A.map (σ.toLinearMap.comp T.toLinearMap) = (A.map T).map σ := by
    apply CStarMatrix.ext
    intro i j
    rfl
  rw [he]
  exact (NonUnitalStarAlgHom.norm_apply_le
    (CStarMatrix.mapₙₐ (n := Fin n) σ.toNonUnitalStarAlgHom) (A.map T)).trans (hT.2 n A)

def representedRightAverage (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (W : H →L[ℂ] K) : H →L[ℂ] K :=
  operatorRowAverage (fun i => π (m i)) (fun i => σ (m i)) W

omit [PartialOrder M] [StarOrderedRing M] in
theorem representedRightAverage_norm_le (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∑ i, m i * star (m i) = 1) (W : H →L[ℂ] K) :
    ‖representedRightAverage π σ m W‖ ≤ ‖W‖ := by
  apply operatorRowAverage_norm_le
  · simpa only [map_sum, map_mul, map_star, map_one] using congrArg π hm
  · simpa only [map_sum, map_mul, map_star, map_one] using congrArg σ hm

omit [PartialOrder M] [StarOrderedRing M] in
theorem representedRightAverage_factorization (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : M →L[ℂ] M) (L W : H →L[ℂ] K)
    (hT : ∀ a, σ (T a) = L.adjoint.comp ((π a).comp W)) (m : I → M) (a : M) :
    σ (finiteRightAverage m T a) =
      L.adjoint.comp ((π a).comp (representedRightAverage π σ m W)) := by
  rw [finiteRightAverage_apply, map_sum]
  simp only [map_mul, map_star, hT]
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [sum_apply, ContinuousLinearMap.comp_apply, representedRightAverage,
    operatorRowAverage_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
