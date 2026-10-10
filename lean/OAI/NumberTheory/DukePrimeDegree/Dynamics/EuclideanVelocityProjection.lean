import OAI.NumberTheory.DukePrimeDegree.Dynamics.TransferredVelocity
import OAI.NumberTheory.DukePrimeDegree.Geometry.ProjectionFromDistances
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-!
# Measurable projections onto the actual component velocity spaces

The matrix topology has a concrete Euclidean model. Orthogonal projection
in that model gives a finite, measurably varying spanning family for the
actual stabilizer velocity space of every probability kernel. No choice
of subgroup curves or of a tangent basis is made measurably.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace DukePrimeDegree
open PrimeDegreePackets

abbrev MatrixEuclidean (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

def matrixEuclideanLinearEquiv (n : ℕ) :
    MatrixEuclidean n ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun v i j := v (i, j)
  invFun V := WithLp.toLp 2 (fun p => V p.1 p.2)
  left_inv v := by ext p; rfl
  right_inv V := by ext i j; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matrixEuclideanEquiv (n : ℕ) :
    MatrixEuclidean n ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (matrixEuclideanLinearEquiv n).toContinuousLinearEquiv

@[simp]
lemma matrixEuclideanEquiv_apply (n : ℕ) (v : MatrixEuclidean n) (i j : Fin n) :
    matrixEuclideanEquiv n v i j = v (i, j) := rfl

@[simp]
lemma matrixEuclideanEquiv_symm_apply (n : ℕ)
    (V : Matrix (Fin n) (Fin n) ℝ) (p : Fin n × Fin n) :
    (matrixEuclideanEquiv n).symm V p = V p.1 p.2 := rfl

def euclideanVelocitySpace {n : ℕ} (μ : Measure (X n)) :
    Submodule ℝ (MatrixEuclidean n) :=
  transferredVelocitySpace (matrixEuclideanEquiv n) μ

def componentVelocityProjection {n : ℕ} (μ : Measure (X n)) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (matrixEuclideanEquiv n).toContinuousLinearMap.comp
    ((euclideanVelocitySpace μ).starProjection.comp
      (matrixEuclideanEquiv n).symm.toContinuousLinearMap)

theorem componentVelocityProjection_mem {n : ℕ} (μ : Measure (X n))
    (V : Matrix (Fin n) (Fin n) ℝ) :
    componentVelocityProjection μ V ∈ matrixVelocitySpace (invariantRightSubgroup μ) := by
  exact (euclideanVelocitySpace μ).starProjection_apply_mem
    ((matrixEuclideanEquiv n).symm V)

theorem componentVelocityProjection_eq_self {n : ℕ} (μ : Measure (X n))
    {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ matrixVelocitySpace (invariantRightSubgroup μ)) :
    componentVelocityProjection μ V = V := by
  have hmem : (matrixEuclideanEquiv n).symm V ∈ euclideanVelocitySpace μ := by
    change matrixEuclideanEquiv n ((matrixEuclideanEquiv n).symm V) ∈
      matrixVelocitySpace (invariantRightSubgroup μ)
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hV
  change matrixEuclideanEquiv n
    ((euclideanVelocitySpace μ).starProjection ((matrixEuclideanEquiv n).symm V)) = V
  rw [(euclideanVelocitySpace μ).starProjection_eq_self_iff.mpr hmem]
  exact (matrixEuclideanEquiv n).apply_symm_apply V

theorem measurable_componentVelocityProjection_entry
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ]
    (V : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Measurable (fun z => componentVelocityProjection (κ z) V i j) := by
  have hd := measurable_kernel_transferredVelocity_distance (matrixEuclideanEquiv n) κ
  have hm := measurable_inner_starProjection_of_distances
    (fun z => euclideanVelocitySpace (κ z)) hd
    ((matrixEuclideanEquiv n).symm V)
    (EuclideanSpace.basisFun (Fin n × Fin n) ℝ (i, j))
  simpa only [EuclideanSpace.inner_basisFun_real, componentVelocityProjection,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    matrixEuclideanEquiv_apply] using hm

theorem measurable_componentVelocityProjection
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ]
    (V : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (fun z => componentVelocityProjection (κ z) V) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_componentVelocityProjection_entry κ V i j

theorem componentVelocityProjection_span {n : ℕ} (μ : Measure (X n)) :
    Submodule.span ℝ (Set.range (fun p : Fin n × Fin n =>
      componentVelocityProjection μ (Matrix.single p.1 p.2 1))) =
        matrixVelocitySpace (invariantRightSubgroup μ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact componentVelocityProjection_mem μ _
  · intro V hV
    have hsingle (i j : Fin n) : Matrix.single i j (V i j) =
        V i j • Matrix.single i j (1 : ℝ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    have hdecomp : V = ∑ i, ∑ j, V i j • Matrix.single i j (1 : ℝ) := by
      have h := (Matrix.sum_sum_single V).symm
      have hof : Matrix.of V = V := by ext i j; rfl
      simpa only [hof, hsingle] using h
    have hP : componentVelocityProjection μ V ∈
        Submodule.span ℝ (Set.range (fun p : Fin n × Fin n =>
          componentVelocityProjection μ (Matrix.single p.1 p.2 1))) := by
      rw [hdecomp]
      simp only [map_sum, map_smul]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.sum_mem
      intro j _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
    simpa only [componentVelocityProjection_eq_self μ hV] using hP

end DukePrimeDegree

end

end OAI
