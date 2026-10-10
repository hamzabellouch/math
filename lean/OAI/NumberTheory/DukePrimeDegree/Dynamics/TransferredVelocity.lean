import OAI.NumberTheory.DukePrimeDegree.Dynamics.KernelVelocityDistance

namespace OAI

/-!
# Changing coordinates in the actual velocity space

Distances may be measured in any finite-dimensional real model of the
matrix space. This allows the subsequent measurable projection argument
to use Euclidean coordinates while the power estimates use an operator
norm. Every subspace here remains the actual stabilizer velocity space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem lowerSemicontinuous_subspace_distance
    {Z E : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (W : Z → Submodule ℝ E)
    (hgraph : IsClosed {p : Z × E | p.2 ∈ W p.1})
    (hclosed : ∀ z, IsClosed (W z : Set E)) (v : E) :
    LowerSemicontinuous (fun z => Metric.infDist v (W z : Set E)) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  let K := Metric.closedBall v r
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall v r)
  have hs : IsClosed {p : Z × K | p.2.val ∈ W p.1} :=
    hgraph.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hp := isClosedMap_fst_of_compactSpace _ hs
  convert hp using 1
  ext z
  constructor
  · intro hz
    change Metric.infDist v (W z : Set E) ≤ r at hz
    obtain ⟨w, hw, hdist⟩ := (hclosed z).exists_infDist_eq_dist ⟨0, (W z).zero_mem⟩ v
    have hwK : w ∈ K := by
      exact Metric.mem_closedBall.mpr (by simpa only [dist_comm, hdist] using hz)
    exact ⟨(z, ⟨w, hwK⟩), hw, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    change p.2.val ∈ W p.1 at hp
    change Metric.infDist v (W p.1 : Set E) ≤ r
    exact (Metric.infDist_le_dist_of_mem hp).trans
      (by simpa only [dist_comm] using Metric.mem_closedBall.mp p.2.property)

def transferredVelocitySpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (e : E ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ)
    (μ : Measure (X n)) : Submodule ℝ E :=
  (matrixVelocitySpace (invariantRightSubgroup μ)).comap e.toLinearMap

theorem isClosed_transferredVelocity_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} [Nonempty (Fin n)] (e : E ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    IsClosed {p : ProbabilityMeasure (X n) × E |
      p.2 ∈ transferredVelocitySpace e (p.1 : Measure (X n))} :=
  (isClosed_probability_velocity_graph n).preimage
    (continuous_fst.prodMk (e.continuous.comp continuous_snd))

theorem lowerSemicontinuous_transferredVelocity_distance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {n : ℕ} [Nonempty (Fin n)]
    (e : E ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ) (v : E) :
    LowerSemicontinuous (fun μ : ProbabilityMeasure (X n) =>
      Metric.infDist v (transferredVelocitySpace e (μ : Measure (X n)) : Set E)) := by
  apply lowerSemicontinuous_subspace_distance _ (isClosed_transferredVelocity_graph e)
  intro μ
  exact (isClosed_matrixVelocitySpace _).preimage e.continuous

theorem measurable_kernel_transferredVelocity_distance
    {Z E : Type*} [MeasurableSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {n : ℕ} [Nonempty (Fin n)]
    (e : E ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ)
    (κ : Kernel Z (X n)) [IsMarkovKernel κ] (v : E) :
    Measurable (fun z => Metric.infDist v (transferredVelocitySpace e (κ z) : Set E)) := by
  let P : Z → ProbabilityMeasure (X n) := fun z => ⟨κ z, inferInstance⟩
  have hκ : @Measurable Z (ProbabilityMeasure (X n)) _
      (borel (ProbabilityMeasure (X n))) P := measurable_kernel_probability_weak κ
  have hd : @Measurable (ProbabilityMeasure (X n)) ℝ
      (borel (ProbabilityMeasure (X n))) inferInstance
      (fun μ => Metric.infDist v (transferredVelocitySpace e (μ : Measure (X n)) : Set E)) := by
    let : MeasurableSpace (ProbabilityMeasure (X n)) := borel (ProbabilityMeasure (X n))
    let : BorelSpace (ProbabilityMeasure (X n)) := ⟨rfl⟩
    exact (lowerSemicontinuous_transferredVelocity_distance e v).measurable
  have hm : Measurable (fun z => Metric.infDist v
      (transferredVelocitySpace e (P z : Measure (X n)) : Set E)) := hd.comp hκ
  simpa only [P, ProbabilityMeasure.coe_mk] using hm

end DukePrimeDegree

end

end OAI
