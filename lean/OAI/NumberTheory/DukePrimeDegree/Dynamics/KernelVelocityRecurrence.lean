import OAI.NumberTheory.DukePrimeDegree.Geometry.MatrixCoordinateFrames
import OAI.NumberTheory.DukePrimeDegree.Dynamics.VelocityTransportRank
import OAI.NumberTheory.DukePrimeDegree.Dynamics.FrameSubspaceRecurrence

namespace OAI

/-!
# Diagonal recurrence for actual component velocity spaces

The kernel covariance is the equality supplied by the
normalizer ergodic decomposition. The velocity space and its measurable
frame are constructed from the kernel, rather than supplied as extra
geometric data. Recurrence is applied separately on its measurable rank
events, and gives invariance of the actual velocity space.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma span_columns_mul_le {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ) :
    Submodule.span ℝ (Set.range (B * C).col) ≤
      Submodule.span ℝ (Set.range B.col) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rw [← Matrix.range_mulVecLin]
  exact ⟨C.col j, rfl⟩

lemma diagonal_mem_span_of_frame_invariance {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (a : Fin n → ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ)
    (hBC : Matrix.diagonal a * B = B * C)
    {v : Fin n → ℝ} (hv : v ∈ Submodule.span ℝ (Set.range B.col)) :
    Matrix.diagonal a *ᵥ v ∈ Submodule.span ℝ (Set.range B.col) := by
  have hspan : (Submodule.span ℝ (Set.range B.col)).map
      (Matrix.diagonal a).mulVecLin =
      Submodule.span ℝ (Set.range (Matrix.diagonal a * B).col) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hm := Submodule.mem_map_of_mem (f := (Matrix.diagonal a).mulVecLin) hv
  rw [hspan, hBC] at hm
  exact span_columns_mul_le B C hm

lemma coordinate_velocitySpace_transport {n : ℕ}
    (μ : Measure (X n)) (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) :
    (matrixVelocitySpace (invariantRightSubgroup
      (μ.map (fun x => rightAction x (diagonalOneParameter ell hell (-1)))))).map
        (matrixCoordinateEquiv n).toLinearMap =
      ((matrixVelocitySpace (invariantRightSubgroup μ)).map
        (matrixCoordinateEquiv n).toLinearMap).map
          (Matrix.diagonal (matrixCoordinateWeight ell)).mulVecLin := by
  rw [← map_matrixVelocitySpace_rightAction μ (diagonalOneParameter ell hell (-1)),
    ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext V q
  change matrixCoordinateEquiv n
      ((diagonalOneParameter ell hell (-1))⁻¹.val * V *
        (diagonalOneParameter ell hell (-1)).val) q = _
  have hinv : (diagonalOneParameter ell hell (-1))⁻¹ =
      diagonalOneParameter ell hell 1 := by
    rw [diagonalOneParameter_neg, inv_inv]
  rw [hinv]
  exact congrFun (matrixCoordinateEquiv_diagonal_conjugation ell hell V) q

/-- Covariance under one actual diagonal translation forces the actual
kernel velocity space to be stable under its adjoint map almost surely.
This uses no ergodicity of that individual translation. -/
theorem ae_kernel_velocity_diagonal_stable
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (τ : Measure Z) [IsFiniteMeasure τ]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ]
    (T : Z → Z) (hT : MeasurePreserving T τ τ)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (hcov : ∀ᵐ z ∂τ,
      (κ z).map (fun x => rightAction x (diagonalOneParameter ell hell (-1))) = κ (T z)) :
    ∀ᵐ z ∂τ, ∀ V ∈ matrixVelocitySpace (invariantRightSubgroup (κ z)),
      (diagonalOneParameter ell hell 1).val * V *
        (diagonalOneParameter ell hell (-1)).val ∈
          matrixVelocitySpace (invariantRightSubgroup (κ z)) := by
  classical
  let a := matrixCoordinateWeight ell
  have hcard : ∀ᵐ z ∂τ, velocityFrameCard (κ (T z)) = velocityFrameCard (κ z) := by
    filter_upwards [hcov] with z hz
    rw [← hz]
    exact velocityFrameCard_map_rightAction (κ z) _
  have hframes (k : ℕ) : ∀ᵐ z ∂τ, velocityFrameCard (κ z) = k →
      ∃ C : Matrix (Fin k) (Fin k) ℝ,
        Matrix.diagonal a * coordinateVelocityFrame (κ z) k =
          coordinateVelocityFrame (κ z) k * C := by
    apply ae_frame_diagonal_invariant_on_event τ T hT
      {z | velocityFrameCard (κ z) = k} ?_
      (fun z => coordinateVelocityFrame (κ z) k)
      (measurable_coordinateVelocityFrame_entry κ k) ?_ ?_ a
      (matrixCoordinateWeight_pos ell) ?_
    · exact hcard.mono fun z hz => by change _ = k ↔ _ = k; rw [hz]
    · exact Eventually.of_forall fun z hz => coordinateVelocityFrame_linearIndependent (κ z) hz
    · exact Eventually.of_forall fun z hz => coordinateVelocityFrame_eq_zero (κ z) hz
    · filter_upwards [hcov, hcard] with z hz hc hk
      have hkT : velocityFrameCard (κ (T z)) = k := hc.trans hk
      rw [coordinateVelocityFrame_span (κ (T z)) hkT]
      have hcols : Submodule.span ℝ
          (Set.range (Matrix.diagonal a * coordinateVelocityFrame (κ z) k).col) =
          (Submodule.span ℝ (Set.range (coordinateVelocityFrame (κ z) k).col)).map
            (Matrix.diagonal a).mulVecLin := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      rw [hcols, coordinateVelocityFrame_span (κ z) hk, ← hz]
      exact coordinate_velocitySpace_transport (κ z) ell hell
  filter_upwards [ae_all_iff.mpr hframes] with z hz
  intro V hV
  let k := velocityFrameCard (κ z)
  obtain ⟨C, hC⟩ := hz k rfl
  have hv : matrixCoordinateEquiv n V ∈
      Submodule.span ℝ (Set.range (coordinateVelocityFrame (κ z) k).col) := by
    rw [coordinateVelocityFrame_span (κ z) rfl]
    exact Submodule.mem_map_of_mem hV
  have hD := diagonal_mem_span_of_frame_invariance
    (coordinateVelocityFrame (κ z) k) a C hC hv
  rw [coordinateVelocityFrame_span (κ z) rfl,
    ← matrixCoordinateEquiv_diagonal_conjugation ell hell V] at hD
  obtain ⟨W, hW, hWV⟩ := hD
  have he := (matrixCoordinateEquiv n).injective hWV
  rwa [he] at hW

/-- The preceding recurrence applies to the actual invariant-sigma
conditional measures. Normalizer covariance and preservation of their
base law are the proved decomposition statements, not new hypotheses. -/
theorem ae_conditional_velocity_diagonal_stable
    {n : ℕ} [Nonempty (Fin n)]
    (H : Subgroup (G n)) (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (ha : diagonalOneParameter ell hell (-1) ∈ Subgroup.normalizer (H : Set (G n)))
    (hμ : μ.map (fun x => rightAction x (diagonalOneParameter ell hell (-1))) = μ) :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X n)),
      ∀ V ∈ matrixVelocitySpace (invariantRightSubgroup
        (condExpKernel μ (actionInvariantSigma H (X n)) z)),
      (diagonalOneParameter ell hell 1).val * V *
        (diagonalOneParameter ell hell (-1)).val ∈
          matrixVelocitySpace (invariantRightSubgroup
            (condExpKernel μ (actionInvariantSigma H (X n)) z)) := by
  let m := actionInvariantSigma H (X n)
  let : MeasurableSpace (X n) := xMeasurableSpace n
  have hm : m ≤ xMeasurableSpace n := actionInvariantSigma_le H (X n)
  let τ : @Measure (X n) m := @Measure.trim (X n) m (xMeasurableSpace n) μ hm
  let κ : @Kernel (X n) (X n) m (xMeasurableSpace n) := condExpKernel μ m
  exact @ae_kernel_velocity_diagonal_stable (X n) m n inferInstance
    τ inferInstance κ inferInstance
    (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
    (lattice_normalizer_preserves_invariantSigma H _ ha μ hμ) ell hell
    (lattice_normalizer_component_covariance H _ ha μ hμ)

end DukePrimeDegree

end

end OAI
