import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.Superlevels
import OAI.Geometry.CAT0Fillings.Currents.WeakMeasures
import OAI.Geometry.CAT0Fillings.Currents.AtomCompactness

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
lemma normal_one_of_bounded_integral_weak_limit
    {Ts : ℕ → Functional X 1} {T : Functional X 1}
    (hTs : ∀ j, IsIntegral 1 (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    IsMetricCurrent T ∧ IsIntegral 0 (boundarySucc T) := by
  exact ⟨metricCurrent_of_bounded_weak_limit (fun j => (hTs j).2.1)
    (fun j => (hTs j).1) (fun j => (hTs j).2.2.1) M N hM hN hlim,
    integral_zero_weak_closed (fun j => (hTs j).2.2) N hN (boundarySucc_weak_limit hlim)⟩

theorem ae_integral_zero_slice_of_bounded_weak_limit
    {Ts : ℕ → Functional X 1} {T : Functional X 1}
    (hTs : ∀ j, IsIntegral 1 (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hX : IsCAT0 X) :
    ∃ hT : IsMetricCurrent T, ∃ hB : IsMetricCurrent (boundarySucc T),
      IsIntegral 0 (boundarySucc T) ∧
      ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
        ∀ᵐ t : ℝ, IsIntegral 0 (superlevelSlice hT hB u t) := by
  obtain ⟨hT,hBI⟩ := normal_one_of_bounded_integral_weak_limit hTs M N hM hN hlim
  refine ⟨hT,hBI.1,hBI,?_⟩
  intro u K hK
  have hu : BoundedLip u := ⟨⟨K,hK⟩,by
    obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuous.continuousOn
    exact ⟨B,fun x => by simpa only [Real.norm_eq_abs] using hB x (mem_univ _)⟩⟩
  obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
    exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
      (fun j => (hTs j).2.2.1) M N hM hN hlim (boundarySucc_weak_limit hlim)
  have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) hT
    (fun j => (hTs (ψ j)).2.2.1) hBI.1 μs νs μ ν hμs hμ hνs hν hμlim hνlim
    (fun b π => (hlim b π).comp hψ.tendsto_atTop) hu
  choose G hG hG0 hGI hS using fun j => superlevelSlice_coarea_bound (hTs (ψ j)) hX hK
  have hGI' j : (∫ t : ℝ, G j t) ≤ (K : ℝ)*M :=
    (hGI j).trans (mul_le_mul_of_nonneg_left (hM (ψ j)) K.coe_nonneg)
  have hfat := ae_exists_bounded_subsequence_of_integral_bound volume hG
    (fun j => Eventually.of_forall (hG0 j)) ((K : ℝ)*M) hGI'
  filter_upwards [hweak,ae_all_iff.mpr hS,hfat] with t ht hs hf
  obtain ⟨C,χ,hχ,hC⟩ := hf
  apply integral_zero_weak_closed (Ts := fun j =>
    superlevelSlice (hTs (ψ (χ j))).1 (hTs (ψ (χ j))).2.2.1 u t)
    (fun j => ⟨(hs (χ j)).1,(hs (χ j)).2.1⟩) C
    (fun j => (hs (χ j)).2.2.trans (hC j))
  intro b π
  exact (ht b π).comp hχ.tendsto_atTop

end CAT0Fillings.Slicing

end

end OAI
