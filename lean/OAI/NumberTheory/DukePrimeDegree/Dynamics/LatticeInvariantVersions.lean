import OAI.NumberTheory.DukePrimeDegree.Dynamics.DenseInvariantFunctions
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ExactInvariantFunctions
import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantMeasureGroup
import Mathlib.MeasureTheory.Measure.Haar.Basic

namespace OAI

/-!
# Exact invariant versions for a matrix subgroup

The subgroup itself need not be closed. Its closure preserves the
measure and fixes the same L² vectors. Haar averaging on that closed
subgroup produces a version measurable for the original subgroup's
exact invariant sigma algebra.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem lattice_pointwise_invariant_version
    {n : ℕ} (H : Subgroup (G n))
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ)
    (f : X n → ℝ) (hf : Measurable f) (hfLp : MemLp f 2 μ)
    (hfix : ∀ h : H, (fun x : X n => f (h • x)) =ᵐ[μ] f) :
    ∃ f₀ : X n → ℝ, Measurable[actionInvariantSigma H (X n)] f₀ ∧
      f₀ =ᵐ[μ] f ∧ ∀ (h : H) (x : X n), f₀ (h • x) = f₀ x := by
  let K := H.topologicalClosure
  have hK : K ≤ invariantRightSubgroup μ :=
    H.topologicalClosure_minimal hH (isClosed_invariantRightSubgroup μ)
  let φ : H →* K := H.inclusion H.le_topologicalClosure
  have hdφ : DenseRange φ := by
    exact (denseRange_inclusion_iff H.le_topologicalClosure).mpr subset_rfl
  have hfixK : ∀ k : K, (fun x : X n => f (k • x)) =ᵐ[μ] f :=
    lattice_function_ae_fixed_of_dense K φ hdφ μ hK f hfLp hfix
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : SecondCountableTopology K :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : LocallyCompactSpace K := H.isClosed_topologicalClosure.locallyCompactSpace
  obtain ⟨f₀, hf₀, heq, hpoint⟩ := exists_pointwise_invariant_version_of_haar
    (Measure.haar : Measure K) (NeZero.ne _) μ continuous_smul.measurable f hf hfixK
  have hmeas : Measurable f₀ :=
    hf₀.mono (actionInvariantSigma_le K (X n)) le_rfl
  have hpointH (h : H) (x : X n) : f₀ (h • x) = f₀ x := hpoint (φ h) x
  exact ⟨f₀, measurable_actionInvariantSigma hmeas hpointH, heq, hpointH⟩

end DukePrimeDegree

end

end OAI
