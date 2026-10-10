import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteProjectionFrames

namespace OAI

/-!
# Actual measurable frames for component stabilizers

Projecting the Euclidean coordinate basis and selecting a maximal Gram
minor constructs a frame of each actual stabilizer velocity space. The
frame cardinality and every fixed column are measurable along a Markov
kernel. This supplies the missing measurable input to diagonal recurrence.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace DukePrimeDegree
open PrimeDegreePackets

def euclideanVelocityColumns {n : ℕ} (μ : Measure (X n))
    (p : Fin n × Fin n) : MatrixEuclidean n :=
  (euclideanVelocitySpace μ).starProjection
    (EuclideanSpace.basisFun (Fin n × Fin n) ℝ p)

theorem euclideanVelocityColumns_span {n : ℕ} (μ : Measure (X n)) :
    Submodule.span ℝ (Set.range (euclideanVelocityColumns μ)) =
      euclideanVelocitySpace μ := by
  let b := EuclideanSpace.basisFun (Fin n × Fin n) ℝ
  have hrange : Set.range (euclideanVelocityColumns μ) =
      (euclideanVelocitySpace μ).starProjection '' Set.range b := by
    exact Set.range_comp _ _
  rw [hrange]
  change Submodule.span ℝ
    ((euclideanVelocitySpace μ).starProjection.toLinearMap '' Set.range b) = _
  rw [← Submodule.map_span]
  have hspan : Submodule.span ℝ (Set.range b) = ⊤ := b.toBasis.span_eq
  rw [hspan, Submodule.map_top, Submodule.range_starProjection]

theorem measurable_euclideanVelocityColumns
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ] (p : Fin n × Fin n) :
    Measurable (fun z => euclideanVelocityColumns (κ z) p) := by
  have hcoords : Measurable (fun z =>
      (EuclideanSpace.equiv (Fin n × Fin n) ℝ) (euclideanVelocityColumns (κ z) p)) := by
    apply measurable_pi_iff.mpr
    intro q
    have hm := measurable_inner_starProjection_of_distances
      (fun z => euclideanVelocitySpace (κ z))
      (measurable_kernel_transferredVelocity_distance (matrixEuclideanEquiv n) κ)
      (EuclideanSpace.basisFun (Fin n × Fin n) ℝ p)
      (EuclideanSpace.basisFun (Fin n × Fin n) ℝ q)
    change Measurable (fun z => (euclideanVelocityColumns (κ z) p) q)
    simpa only [EuclideanSpace.inner_basisFun_real, euclideanVelocityColumns] using hm
  convert (EuclideanSpace.equiv (Fin n × Fin n) ℝ).symm.continuous.measurable.comp
    hcoords using 1
  funext z
  exact ((EuclideanSpace.equiv (Fin n × Fin n) ℝ).symm_apply_apply _).symm

def velocityFrameCard {n : ℕ} (μ : Measure (X n)) : ℕ :=
  (maximalGramFrame (euclideanVelocityColumns μ)).card

def velocityFrame {n : ℕ} (μ : Measure (X n)) (j : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  matrixEuclideanEquiv n (selectedFrameVector (euclideanVelocityColumns μ) j)

theorem velocityFrame_linearIndependent {n : ℕ} (μ : Measure (X n)) :
    LinearIndependent ℝ (fun j : Fin (velocityFrameCard μ) => velocityFrame μ j) := by
  exact (selectedFrameVector_linearIndependent (euclideanVelocityColumns μ)).map_injOn
    (matrixEuclideanEquiv n).toLinearMap
    (fun _ _ _ _ h => (matrixEuclideanEquiv n).injective h)

theorem velocityFrame_span {n : ℕ} (μ : Measure (X n)) :
    Submodule.span ℝ (Set.range (fun j : Fin (velocityFrameCard μ) => velocityFrame μ j)) =
      matrixVelocitySpace (invariantRightSubgroup μ) := by
  have hrange : Set.range (fun j : Fin (velocityFrameCard μ) => velocityFrame μ j) =
      matrixEuclideanEquiv n '' Set.range
        (fun j : Fin (velocityFrameCard μ) =>
          selectedFrameVector (euclideanVelocityColumns μ) j) := by
    exact Set.range_comp _ _
  rw [hrange]
  change Submodule.span ℝ ((matrixEuclideanEquiv n).toLinearMap '' Set.range
    (fun j : Fin (velocityFrameCard μ) =>
      selectedFrameVector (euclideanVelocityColumns μ) j)) = _
  rw [← Submodule.map_span]
  have hframe : Submodule.span ℝ (Set.range
      (fun j : Fin (velocityFrameCard μ) =>
        selectedFrameVector (euclideanVelocityColumns μ) j)) =
      Submodule.span ℝ (Set.range (euclideanVelocityColumns μ)) :=
    selectedFrameVector_span (euclideanVelocityColumns μ)
  rw [hframe, euclideanVelocityColumns_span]
  exact Submodule.map_comap_eq_of_surjective (matrixEuclideanEquiv n).surjective _

theorem velocityFrameCard_eq_finrank {n : ℕ} (μ : Measure (X n)) :
    velocityFrameCard μ = Module.finrank ℝ (matrixVelocitySpace (invariantRightSubgroup μ)) := by
  have h := finrank_span_eq_card (velocityFrame_linearIndependent μ)
  rw [velocityFrame_span, Fintype.card_fin] at h
  exact h.symm

theorem measurable_velocityFrameCard
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ] :
    Measurable (fun z => velocityFrameCard (κ z)) :=
  measurable_selectedFrameCard (fun z => euclideanVelocityColumns (κ z))
    (measurable_euclideanVelocityColumns κ)

theorem measurable_velocityFrame
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ] (j : ℕ) :
    Measurable (fun z => velocityFrame (κ z) j) :=
  (matrixEuclideanEquiv n).continuous.measurable.comp
    (measurable_selectedFrameVector (fun z => euclideanVelocityColumns (κ z))
      (measurable_euclideanVelocityColumns κ) j)

end DukePrimeDegree

end

end OAI
