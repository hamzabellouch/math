import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
namespace ScalarConductivity

theorem exists_smooth_cutoff_small_margin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.InnerRegularCompactLTTop μ]
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hμU : μ U ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ χ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ x, χ x ∈ Icc 0 1) ∧ μ {x | x ∈ U ∧ χ x ≠ 1} < ε := by
  obtain ⟨K, hKU, hK, hKμ⟩ := hU.measurableSet.exists_isCompact_sdiff_lt hμU hε
  obtain ⟨χ, hχ₀, hχ₁, hχb⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, E))
    hU.isClosed_compl hK.isClosed (disjoint_left.mpr (fun _ hx hxK => hx (hKU hxK))) (n := ⊤)
  have ht : tsupport (χ : E → ℝ) ⊆ U := by
    intro x hx
    by_contra hxU
    apply (notMem_tsupport_iff_eventuallyEq.mpr
      (hχ₀.filter_mono (nhds_le_nhdsSet hxU))) hx
  refine ⟨χ, contMDiff_iff_contDiff.mp χ.contMDiff,
    (hUb.subset ht).isCompact_closure.of_isClosed_subset (isClosed_tsupport _) subset_closure,
    ht, hχb, ?_⟩
  apply (measure_mono ?_).trans_lt hKμ
  intro x hx
  exact ⟨hx.1, fun hxK => hx.2 ((hχ₁.filter_mono (nhds_le_nhdsSet hxK)).self_of_nhds)⟩

end ScalarConductivity

end

end OAI
