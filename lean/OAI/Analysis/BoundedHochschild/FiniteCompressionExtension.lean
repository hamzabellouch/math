import OAI.Analysis.BoundedHochschild.FinitePositiveExtension
import OAI.Analysis.BoundedHochschild.OperatorSystemCompression
import OAI.Analysis.BoundedHochschild.CompletelyPositiveNorm

namespace OAI

/-! Extend a finite compression and then regard it as a map on the original
Hilbert space. All coefficients on that finite subspace are retained. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_finite_compression_extension (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (hstar : ∀ a ∈ S, star a ∈ S) (φ : S →ₗ[ℂ] (H →L[ℂ] H))
    (hφ1 : φ ⟨1, h1⟩ = 1) {n : ℕ} (i₀ : Fin n)
    (V : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] H)
    (hφ : ∀ X : operatorSystemMatrices S n,
      0 ≤ (X : CStarMatrix (Fin n) (Fin n) A) →
        0 ≤ operatorSystemAmplification S φ n X) :
    ∃ Ψ : CompletelyPositiveMap A (H →L[ℂ] H),
      (∀ a, ‖Ψ a‖ ≤ ‖a‖) ∧ ∀ (a : S) ξ η,
        inner ℂ (V η) (Ψ (a : A) (V ξ)) = inner ℂ (V η) (φ a (V ξ)) := by
  let ψ := compressOperatorSystem S φ V.toContinuousLinearMap
  obtain ⟨Φ, hΦ⟩ := exists_finite_completelyPositive_extension S h1 hstar i₀ ψ
    (fun X hX => compressOperatorSystem_positive S φ _ X (hφ X hX))
  have hΦ1 : Φ 1 = 1 := (hΦ ⟨1, h1⟩).trans (compressOperatorSystem_one S h1 φ hφ1 V)
  let Ψ := compressCompletelyPositive Φ V.toContinuousLinearMap.adjoint
  have hV : ‖V.toContinuousLinearMap‖ ≤ 1 := by
    apply V.toContinuousLinearMap.opNorm_le_bound zero_le_one
    intro ξ
    simp only [LinearIsometry.coe_toContinuousLinearMap, V.norm_map, one_mul]
    exact le_rfl
  have hΨ1 : Ψ 1 = V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint := by
    change V.toContinuousLinearMap.adjoint.adjoint.comp
      ((Φ 1).comp V.toContinuousLinearMap.adjoint) = _
    rw [ContinuousLinearMap.adjoint_adjoint, hΦ1]
    rfl
  have hn : ‖Ψ 1‖ ≤ 1 := by
    rw [hΨ1]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    nlinarith [norm_nonneg V.toContinuousLinearMap]
  have hVV (ξ : EuclideanSpace ℂ (Fin n)) : V.toContinuousLinearMap.adjoint (V ξ) = ξ := by
    exact congrArg (fun T => T ξ) V.adjoint_comp_self
  refine ⟨Ψ, fun a => (completelyPositive_norm_apply_le Ψ a).trans ?_, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg a)
  · intro a ξ η
    change inner ℂ (V η) (V.toContinuousLinearMap.adjoint.adjoint
      (Φ (a : A) (V.toContinuousLinearMap.adjoint (V ξ)))) = _
    rw [ContinuousLinearMap.adjoint_inner_right, hVV, hVV, hΦ a]
    change inner ℂ η (V.toContinuousLinearMap.adjoint (φ a (V ξ))) = _
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

end BoundedHochschild.KadisonRingrose

end

end OAI
