import OAI.Analysis.KadisonSimilarity.Representation.IntertwinerExtension
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixVonNeumannRange

namespace OAI

/-! # Compressing a represented bicommutant

Commutation of zero extensions of the original commutant suffices to
recover the original von Neumann algebra after compression. The operator
being compressed need not be supported on the range of the isometry.
-/

noncomputable section
namespace KadisonSimilarity

variable {H K A : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [CStarAlgebra A] (J : H →ₗᵢ[ℂ] K)

/-- Applying the isometry's adjoint to a zero extension intertwines the
extended operator with the original one. -/
theorem adjoint_isometricExtension_apply (T : H →L[ℂ] H) (y : K) :
    J.toContinuousLinearMap.adjoint (isometricExtension J T y) =
      T (J.toContinuousLinearMap.adjoint y) := by
  have h (x : H) : J.toContinuousLinearMap.adjoint (J x) = x :=
    congrArg (fun U : H →L[ℂ] H => U x) J.adjoint_comp_self
  change J.toContinuousLinearMap.adjoint
    (J (T (J.toContinuousLinearMap.adjoint y))) = _
  exact h _

/-- A commutation relation with a zero extension compresses without any
range-support assumption on the other operator. -/
theorem compression_commutes_of_isometricExtension_commutes
    (T : H →L[ℂ] H) (Q : K →L[ℂ] K)
    (hcomm : isometricExtension J T * Q = Q * isometricExtension J T) :
    T * (J.toContinuousLinearMap.adjoint.comp (Q.comp J.toContinuousLinearMap)) =
      (J.toContinuousLinearMap.adjoint.comp (Q.comp J.toContinuousLinearMap)) * T := by
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg
    (fun U : K →L[ℂ] K => J.toContinuousLinearMap.adjoint (U (J x))) hcomm
  simpa only [mul_apply_eq_comp, adjoint_isometricExtension_apply,
    isometricExtension_on_range, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap] using h

/-- If the extended original commutant commutes with a represented
algebra, its represented bicommutant compresses into the original algebra. -/
theorem compression_mem_of_extended_commutant
    (P : VonNeumannAlgebra H) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hcomm : ∀ T : H →L[ℂ] H, T ∈ P.commutant →
      ∀ a : A, isometricExtension J T * σ a = σ a * isometricExtension J T)
    (Q : K →L[ℂ] K) (hQ : Q ∈ representationVonNeumannAlgebra σ) :
    J.toContinuousLinearMap.adjoint.comp (Q.comp J.toContinuousLinearMap) ∈ P := by
  rw [← P.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have hET : isometricExtension J T ∈
      (representationVonNeumannAlgebra σ).commutant := by
    apply (mem_representation_commutant_iff σ _).mpr
    rintro _ ⟨a, rfl⟩
    exact (hcomm T hT a).symm
  apply compression_commutes_of_isometricExtension_commutes J T Q
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hET Q hQ).symm

end KadisonSimilarity

end

end OAI
