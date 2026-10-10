import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactProbabilityProduct
import Mathlib.MeasureTheory.Integral.Average

namespace OAI

/-! # Choosing deterministic centers for concentrated profile laws -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

/-- The first-moment method chooses one deterministic profile whose mean
error is no larger than the error between two independent profiles. -/
theorem exists_deterministic_profile_centers
    {S Y : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [MeasurableSpace S] [BorelSpace S] [PseudoMetricSpace Y]
    (F : S → Y) (hF : Continuous F) (μ : ℕ → ProbabilityMeasure S) :
    ∃ center : ℕ → S, ∀ n,
      (∫ x, dist (F x) (F (center n)) ∂(μ n : Measure S)) ≤
        ∫ y, ∫ x, dist (F x) (F y) ∂(μ n : Measure S) ∂(μ n : Measure S) := by
  let d : C(S × S, ℝ) := ⟨fun p => dist (F p.2) (F p.1),
    (hF.comp continuous_snd).dist (hF.comp continuous_fst)⟩
  have hmean (n) : Continuous (fun y => ∫ x, dist (F x) (F y) ∂(μ n : Measure S)) :=
    (continuous_integral_compact_function (μ n)).comp d.curry.continuous
  have hex (n) : ∃ y : S,
      (∫ x, dist (F x) (F y) ∂(μ n : Measure S)) ≤
        ∫ z, ∫ x, dist (F x) (F z) ∂(μ n : Measure S) ∂(μ n : Measure S) :=
    exists_le_integral ((hmean n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  choose center hc using hex
  exact ⟨center, hc⟩

/-- Vanishing mean pairwise distance gives deterministic centers with
vanishing mean error. The centers may be selected independently at each scale. -/
theorem exists_deterministic_concentration_centers
    {S Y : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [MeasurableSpace S] [BorelSpace S] [PseudoMetricSpace Y]
    (F : S → Y) (hF : Continuous F) (μ : ℕ → ProbabilityMeasure S)
    (hpair : Tendsto (fun n =>
      ∫ y, ∫ x, dist (F x) (F y) ∂(μ n : Measure S) ∂(μ n : Measure S))
      atTop (𝓝 0)) :
    ∃ center : ℕ → S, Tendsto (fun n =>
      ∫ x, dist (F x) (F (center n)) ∂(μ n : Measure S)) atTop (𝓝 0) := by
  obtain ⟨center, hc⟩ := exists_deterministic_profile_centers F hF μ
  exact ⟨center, squeeze_zero (fun _ => integral_nonneg (fun _ => dist_nonneg)) hc hpair⟩

end PolycyclicRecognition

end

end OAI
