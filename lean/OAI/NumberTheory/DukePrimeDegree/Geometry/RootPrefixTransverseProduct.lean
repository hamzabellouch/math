import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixProductKernel

namespace OAI

/-! # The uncentered product depends projectively only on the transverse point

This removes the sampled-point normalization before selecting measurable
future events with a transverse leaf kernel.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) P T} {g : G (d+1)}

theorem ae_uncenteredIntrinsicProduct_eq_smul_leaf
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ z ∂B.coordinateMeasure μ, ∃ a : ℝ≥0∞,
      a ≠ 0 ∧ a ≠ ∞ ∧ B.uncenteredIntrinsicProduct μ z = a • B.leafMeasure R μ z.1 := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree := ae_upperRoot_stabilizer_trivial d μ hA
  have hs := ae_of_ae_map measurable_fst.aemeasurable (B.ae_leafMeasure_spec R hBR μ hfree)
  filter_upwards [hs, B.ae_mem_leafMeasure_support R hBR μ hfree,
    ae_remainingLeaf_eq_intrinsicProduct d hP c hf C g B R hBR μ] with z hz ht hp
  let ν := B.leafMeasure R μ z.1
  let : IsLocallyFiniteMeasure ν := hz.1
  refine ⟨(c.centeredRemainingMeasure hP hf ν z.2 (c.cube 1))⁻¹,
    ENNReal.inv_ne_zero.mpr (c.centeredRemainingMeasure_unit_lt_top hP hf ν z.2).ne,
    ENNReal.inv_ne_top.mpr (c.centeredRemainingMeasure_unit_pos hP hf ν z.2 ht).ne', ?_⟩
  unfold uncenteredIntrinsicProduct
  rw [← hp]
  exact c.uncenter_basedRemainingGroupMeasure hP hf ν z.2

theorem ae_normalized_uncentered_eq_regularLeaf
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1) :
    ∀ᵐ z ∂B.coordinateMeasure μ, ∀ J : Set c.Time,
      anchorNormalize (B.uncenteredIntrinsicProduct μ z) J =
        anchorNormalize (B.regularLeafKernel R hBR μ hfree z.1) J := by
  have hk := ae_of_ae_map measurable_fst.aemeasurable
    (B.ae_regularLeafKernel_eq R hBR μ hfree)
  filter_upwards [B.ae_uncenteredIntrinsicProduct_eq_smul_leaf R hBR μ, hk] with z hz hk
  obtain ⟨a, ha₀, hatop, ha⟩ := hz
  intro J
  rw [hk, ha]
  exact anchorNormalize_smul _ _ a ha₀ hatop

end RootPrefixBox
end DukePrimeDegree

end

end OAI
