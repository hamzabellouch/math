import Mathlib
import OAI.Analysis.Crouzeix.ContourExistence
import OAI.Analysis.Crouzeix.EndpointInterpolation
import OAI.Analysis.Crouzeix.RationalContours

namespace OAI

/-! Disk Endpoint. -/

noncomputable section

open Set

open scoped TensorProduct Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace CrouzeixHilbert

open Boundary Realization Endpoint

@[simp] theorem vectorization_smul {n : ℕ} (c : ℂ) (X : Coeff n) :
    vectorization (c • X) = c • vectorization X := by
  let e : Amplification (EuclideanSpace ℂ (Fin n)) n →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n × Fin n) :=
    ⟨(matrixAmplificationCoordinates n n).toLinearMap, norm_matrixAmplificationCoordinates n n⟩
  apply e.injective
  change matrixAmplificationCoordinates n n _ = matrixAmplificationCoordinates n n _
  rw [map_smul, vectorization_coordinates, vectorization_coordinates]
  apply PiLp.ext
  intro ij
  rfl

theorem tensor_endpoint_of_matrix_endpoint {n : ℕ} (S X : Coeff n)
    (t : ℝ) (h : S * X = t • X) :
    tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) S) (1 : Coeff n)
      (vectorization X) = (t : ℂ) • vectorization X := by
  rw [tensorOperator_vectorization, Matrix.transpose_one, mul_one, h]
  rw [← vectorization_smul]
  congr 1

theorem trace_gram_eq_norm_vectorization_sq {n : ℕ} (X : Coeff n) :
    (X * Xᴴ).trace = (‖vectorization X‖ : ℂ) ^ 2 := by
  rw [Matrix.trace_mul_comm, ← inner_toHS, inner_self_eq_norm_sq_to_K, norm_vectorization]
  norm_cast

theorem disk_endpoint_extremal {n : ℕ} (hn : 0 < n) (T : Coeff n)
    (hT : spectralRadius ℂ T < 1) {κ : ℝ} (hκ : 1 < κ)
    (H : Coeff n) (hH : Metric.Feasible T (κ ^ 2) H)
    (hmin : ∀ s J, Metric.Feasible T s J → κ ^ 2 ≤ s) :
    ∃ (X Y : Coeff n) (R : RationalMatrix n) (U : Set ℂ),
      (X * Xᴴ).trace = 1 ∧ (Y * Yᴴ).trace = 1 ∧
      CFC.sqrt H * X = κ • X ∧ CFC.sqrt H * Y = Y ∧ Xᴴ * Y = 0 ∧
      ‖vectorization X‖ = 1 ∧ ‖vectorization Y‖ = 1 ∧
      tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) (CFC.sqrt H)) (1 : Coeff n)
        (vectorization X) = (κ : ℂ) • vectorization X ∧
      tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) (CFC.sqrt H)) (1 : Coeff n)
        (vectorization Y) = vectorization Y ∧
      IsOpen U ∧ Metric.closedBall (0 : ℂ) 1 ⊆ U ∧ PolesOutside U R ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖matrixRationalFunction R z‖ ≤ 1) ∧
      matrixRationalEval (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))) R
          (vectorization X) = vectorization Y ∧
      matrixHolomorphicEval (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))) U
          (matrixRationalFunction R) (vectorization X) = vectorization Y := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨E⟩ := endpointFactors_of_minimum T hT hκ H hH hmin
  obtain ⟨C, hL, hY⟩ := E.exists_colligation
  let D := CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)
  have hD : spectralRadius ℂ D < 1 := by
    simpa only [D, spectralRadius_eq_of_unital, hH.sqrt_spectrum] using hT
  have ha : ‖e.symm C.a‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def, StarAlgEquiv.apply_symm_apply]
    exact C.norm_a_le
  have hi : matrixRationalEval (e D) C.diskExtremal (vectorization E.X) =
      vectorization E.Y :=
    rational_transfer_interpolates D (e.symm C.a) (e.symm C.b) (e.symm C.c) (e.symm C.d)
      (CFC.sqrt E.Q) E.X E.Y hD ha hL hY
  obtain ⟨U, hU, hKU, hRU, hFU⟩ := rational_poleFree_neighborhood C.diskExtremal
    C.diskExtremal_polesOutside
  have hKD : numericalClosure (e D) ⊆ Metric.closedBall (0 : ℂ) 1 :=
    (numericalClosure_subset_closedBall (e D)).trans
      (Metric.closedBall_subset_closedBall (by
        have hnD := hH.sqrt_similarity.2.1
        rwa [← Matrix.cstar_norm_def]))
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure (e D))
    (convex_numericalClosure (e D)) (numericalClosure_nonempty (e D)) hU (hKD.trans hKU)
  have heval := matrixHolomorphicEval_matrixRationalFunction (e D) Γ C.diskExtremal hRU
  have hXn : ‖vectorization E.X‖ = 1 := by rw [norm_vectorization, E.X_norm]
  have hYn : ‖vectorization E.Y‖ = 1 := by rw [norm_vectorization, E.Y_norm]
  refine ⟨E.X, E.Y, C.diskExtremal, U, ?_, ?_, E.X_endpoint, E.Y_endpoint,
    E.perpendicular, hXn, hYn, ?_, ?_, hU, hKU, hRU, hFU,
    C.diskExtremal_extension.2, hi, ?_⟩
  · rw [trace_gram_eq_norm_vectorization_sq, hXn]; norm_num
  · rw [trace_gram_eq_norm_vectorization_sq, hYn]; norm_num
  · exact tensor_endpoint_of_matrix_endpoint (CFC.sqrt H) E.X κ E.X_endpoint
  · simpa only [Complex.ofReal_one, one_smul] using
      tensor_endpoint_of_matrix_endpoint (CFC.sqrt H) E.Y 1
        (by simpa only [one_smul] using E.Y_endpoint)
  · rw [heval]
    exact hi

end CrouzeixHilbert

end

end OAI
