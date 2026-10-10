import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingMeasureLimits
import OAI.NumberTheory.DukePrimeDegree.Geometry.LatticeGroupDecomposition

namespace OAI

/-!
# Closed graph of the actual probability stabilizer

The probability measure and the group element may both vary. Uniform
translation control of compact observables shows that invariance passes
to the simultaneous limit. This is the topological input for constructing
measurable data from the component stabilizers.
-/

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem isClosed_probability_smul_stabilizer
    {H Y : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [WeaklyLocallyCompactSpace H] [TopologicalSpace Y] [LocallyCompactSpace Y]
    [T2Space Y] [MetrizableSpace Y] [SigmaCompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [MulAction H Y] [ContinuousSMul H Y] :
    IsClosed {p : ProbabilityMeasure Y × H |
      (p.1 : Measure Y).map (fun y => p.2 • y) = (p.1 : Measure Y)} := by
  apply isClosed_iff_forall_filter.mpr
  intro p F hF hset hlim
  let : F.NeBot := hF
  have hμ : Tendsto (fun q : ProbabilityMeasure Y × H => q.1) F (𝓝 p.1) :=
    continuous_fst.continuousAt.tendsto.comp hlim
  have hg : Tendsto (fun q : ProbabilityMeasure Y × H => q.2) F (𝓝 p.2) :=
    continuous_snd.continuousAt.tendsto.comp hlim
  exact map_eq_of_converging_translated_probabilities
    (fun q : ProbabilityMeasure Y × H => q.1) (fun q => q.1) p.1 hμ hμ
    (fun q => q.2) p.2 hg (Filter.le_principal_iff.mp hset)

/-- The actual right stabilizer on the row-lattice quotient has closed
graph in the weak probability topology times the real matrix group. -/
theorem isClosed_probability_right_stabilizer (n : ℕ) :
    IsClosed {p : ProbabilityMeasure (X n) × G n |
      p.2 ∈ invariantRightSubgroup (p.1 : Measure (X n))} := by
  let : MulAction (G n) (X n) :=
    { smul := fun g x => rightAction x g⁻¹
      one_smul := fun x => by
        change rightAction x (1 : G n)⁻¹ = x
        simp only [inv_one, rightAction_one]
      mul_smul := fun a b x => by
        change rightAction x (a * b)⁻¹ = rightAction (rightAction x b⁻¹) a⁻¹
        rw [mul_inv_rev, rightAction_mul] }
  let : ContinuousSMul (G n) (X n) :=
    ⟨(continuous_rightAction_uncurry n).comp
      (continuous_snd.prodMk continuous_fst.inv)⟩
  have h := isClosed_probability_smul_stabilizer (H := G n) (Y := X n)
  have hc : Continuous (fun p : ProbabilityMeasure (X n) × G n => (p.1, p.2⁻¹)) :=
    continuous_fst.prodMk continuous_snd.inv
  convert h.preimage hc using 1
  ext p
  change ((p.1 : Measure (X n)).map (fun x => rightAction x p.2) = p.1) ↔
    ((p.1 : Measure (X n)).map (fun x => rightAction x (p.2⁻¹)⁻¹) = p.1)
  rw [inv_inv]

/-- Passing from an SL element to its actual matrix preserves the
closed stabilizer graph because the determinant-one inclusion is a
closed embedding. -/
theorem isClosed_probability_matrix_stabilizer (n : ℕ) :
    IsClosed {p : ProbabilityMeasure (X n) × Matrix (Fin n) (Fin n) ℝ |
      ∃ g : G n, g ∈ invariantRightSubgroup (p.1 : Measure (X n)) ∧ g.val = p.2} := by
  have hc : Topology.IsClosedEmbedding
      (fun p : ProbabilityMeasure (X n) × G n => (p.1, p.2.val)) :=
    Topology.IsClosedEmbedding.id.prodMap Matrix.SpecialLinearGroup.isClosedEmbedding_val
  have h := hc.isClosedMap _ (isClosed_probability_right_stabilizer n)
  convert h using 1
  ext p
  constructor
  · rintro ⟨g, hg, he⟩
    exact ⟨(p.1, g), hg, Prod.ext rfl he⟩
  · rintro ⟨q, hq, he⟩
    obtain ⟨hμ, hmat⟩ := Prod.mk.inj he
    exact ⟨q.2, hμ ▸ hq, hmat⟩

end DukePrimeDegree

end

end OAI
