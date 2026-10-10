import OAI.NumberTheory.DukePrimeDegree.Dynamics.StabilizerClosedGraph
import OAI.NumberTheory.DukePrimeDegree.Dynamics.VelocityMembershipMeasurable
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Semicontinuity.Basic

namespace OAI

/-!
# Closed graph of actual component velocities

Exponential recovery and the closed probability-stabilizer graph imply
that the graph of the actual velocity subspace is closed. In particular,
compact restrictions can be projected without making an arbitrary choice
of tangent curves or frames.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology Matrix.Norms.Operator

namespace DukePrimeDegree
open PrimeDegreePackets

theorem isClosed_probability_velocity_graph (n : ℕ) [Nonempty (Fin n)] :
    IsClosed {p : ProbabilityMeasure (X n) × Matrix (Fin n) (Fin n) ℝ |
      p.2 ∈ matrixVelocitySpace (invariantRightSubgroup (p.1 : Measure (X n)))} := by
  have he : {p : ProbabilityMeasure (X n) × Matrix (Fin n) (Fin n) ℝ |
      p.2 ∈ matrixVelocitySpace (invariantRightSubgroup (p.1 : Measure (X n)))} =
      ⋂ q : ℚ, {p : ProbabilityMeasure (X n) × Matrix (Fin n) (Fin n) ℝ |
        ∃ g : G n, g ∈ invariantRightSubgroup (p.1 : Measure (X n)) ∧
          g.val = NormedSpace.exp ((q : ℝ) • p.2)} := by
    ext p
    simp only [mem_iInter, mem_ofPred_eq]
    exact mem_matrixVelocitySpace_iff_rational_exp _ (isClosed_invariantRightSubgroup _) _
  rw [he]
  apply isClosed_iInter
  intro q
  exact (isClosed_probability_matrix_stabilizer n).preimage
    (continuous_fst.prodMk (NormedSpace.exp_continuous.comp
      (continuous_snd.const_smul (q : ℝ))))

/-- Restricting the velocity variable to a fixed compact set gives a
closed event in the space of probabilities. -/
theorem isClosed_probability_velocity_inter_compact (n : ℕ) [Nonempty (Fin n)]
    (K : Set (Matrix (Fin n) (Fin n) ℝ)) (hK : IsCompact K) :
    IsClosed {μ : ProbabilityMeasure (X n) | ∃ V ∈ K,
      V ∈ matrixVelocitySpace (invariantRightSubgroup (μ : Measure (X n)))} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hclosed : IsClosed {p : ProbabilityMeasure (X n) × K |
      p.2.val ∈ matrixVelocitySpace (invariantRightSubgroup (p.1 : Measure (X n)))} :=
    (isClosed_probability_velocity_graph n).preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hproj := isClosedMap_fst_of_compactSpace _ hclosed
  convert hproj using 1
  ext μ
  constructor
  · rintro ⟨V, hVK, hV⟩
    exact ⟨(μ, ⟨V, hVK⟩), hV, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2.val, p.2.property, hp⟩

/-- Distance to the actual velocity subspace, measured using the fixed
matrix norm. -/
def probabilityVelocityDistance (n : ℕ)
    (V : Matrix (Fin n) (Fin n) ℝ) (μ : ProbabilityMeasure (X n)) : ℝ :=
  Metric.infDist V (matrixVelocitySpace (invariantRightSubgroup (μ : Measure (X n))))

/-- A closed graph and finite-dimensional compactness make the distance
to the genuine velocity subspace lower semicontinuous. This is a useful
measurability route that does not select tangent curves. -/
theorem lowerSemicontinuous_probabilityVelocityDistance (n : ℕ)
    [Nonempty (Fin n)] (V : Matrix (Fin n) (Fin n) ℝ) :
    LowerSemicontinuous (probabilityVelocityDistance n V) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  have he : (probabilityVelocityDistance n V) ⁻¹' Iic r =
      {μ : ProbabilityMeasure (X n) | ∃ W ∈ Metric.closedBall V r,
        W ∈ matrixVelocitySpace (invariantRightSubgroup (μ : Measure (X n)))} := by
    ext μ
    change Metric.infDist V
        (matrixVelocitySpace (invariantRightSubgroup (μ : Measure (X n)))) ≤ r ↔ _
    constructor
    · intro h
      obtain ⟨W, hW, hdist⟩ := (isClosed_matrixVelocitySpace
        (invariantRightSubgroup (μ : Measure (X n)))).exists_infDist_eq_dist
          ⟨0, (matrixVelocitySpace (invariantRightSubgroup (μ : Measure (X n)))).zero_mem⟩ V
      exact ⟨W, Metric.mem_closedBall.mpr (by simpa only [dist_comm, hdist] using h), hW⟩
    · rintro ⟨W, hW, hvel⟩
      exact (Metric.infDist_le_dist_of_mem hvel).trans
        (by simpa only [dist_comm] using Metric.mem_closedBall.mp hW)
  rw [he]
  exact isClosed_probability_velocity_inter_compact n _ (isCompact_closedBall V r)

end DukePrimeDegree

end

end OAI
