import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.WeakSlices
import OAI.Geometry.CAT0Fillings.Slicing.IntegralBoundary

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter MassMeasure Foundations
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
def IntegralSliceTree : (k : ℕ) → Functional X k → Prop
  | 0, T => IsIntegral 0 T
  | k+1, T => ∃ hT : IsMetricCurrent T, ∃ hB : IsMetricCurrent (boundarySucc T),
      ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
        ∀ᵐ t : ℝ, IntegralSliceTree k (superlevelSlice hT hB u t)

theorem integral_slice_tree_of_bounded_weak_limit {k : ℕ}
    {Ts : ℕ → Functional X k} {T : Functional X k}
    (hTs : ∀ j, IsIntegral k (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundary (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hX : IsCAT0 X) : IntegralSliceTree k T := by
  induction k generalizing M N with
  | zero => exact integral_zero_weak_closed hTs M hM hlim
  | succ k ih =>
    cases k with
    | zero =>
      obtain ⟨hT,hB,_,hS⟩ := ae_integral_zero_slice_of_bounded_weak_limit hTs M N hM hN hlim hX
      exact ⟨hT,hB,hS⟩
    | succ k =>
      obtain ⟨hT,hB⟩ := normal_of_bounded_integral_weak_limit hTs M N hM hN hlim
      refine ⟨hT,hB,?_⟩
      intro u K hK
      have hu : BoundedLip u := boundedLip_of_lipschitz hK
      obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
        exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
          (fun j => (hTs j).2.2.1) M N hM hN hlim (boundarySucc_weak_limit hlim)
      have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) hT
        (fun j => (hTs (ψ j)).2.2.1) hB μs νs μ ν hμs hμ hνs hν hμlim hνlim
        (fun b π => (hlim b π).comp hψ.tendsto_atTop) hu
      choose G H hG hH hG0 hH0 hGI hHI hS using fun j =>
        superlevelSlice_normal_coarea_bound (hTs (ψ j)) hX hK
      have hsum j : Integrable (fun t => G j t + H j t) volume := (hG j).add (hH j)
      have hsum0 j : 0 ≤ᵐ[volume] (fun t => G j t + H j t) :=
        Eventually.of_forall fun t => add_nonneg (hG0 j t) (hH0 j t)
      have hsumI j : (∫ t : ℝ, G j t + H j t) ≤ (K : ℝ)*(M+N) := by
        rw [integral_add (hG j) (hH j),mul_add]
        exact add_le_add ((hGI j).trans (mul_le_mul_of_nonneg_left (hM (ψ j)) K.coe_nonneg))
          ((hHI j).trans (mul_le_mul_of_nonneg_left (hN (ψ j)) K.coe_nonneg))
      have hfat := ae_exists_bounded_subsequence_of_integral_bound volume hsum hsum0
        ((K : ℝ)*(M+N)) hsumI
      filter_upwards [hweak,ae_all_iff.mpr hS,hfat] with t ht hs hf
      obtain ⟨C,χ,hχ,hC⟩ := hf
      let D : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
      let Ss : ℕ → Functional X (k+1) := fun j =>
        superlevelSlice (hTs (ψ (χ j))).1 (hTs (ψ (χ j))).2.2.1 u t
      have hSs j : IsIntegral (k+1) (Ss j) := (hs (χ j)).1
      have hSC j : mass (Ss j) ≤ D :=
        (((hs (χ j)).2.1.trans (le_add_of_nonneg_right (hH0 (χ j) t))).trans (hC j)).trans (le_max_left _ _)
      have hBC j : mass (boundary (Ss j)) ≤ D :=
        (((hs (χ j)).2.2.trans (le_add_of_nonneg_left (hG0 (χ j) t))).trans (hC j)).trans (le_max_left _ _)
      exact ih hSs D D hSC hBC (fun b π => (ht b π).comp hχ.tendsto_atTop)

end CAT0Fillings.Slicing
end

end OAI
