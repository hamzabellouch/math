import OAI.GroupTheory.PolycyclicRecognition.Analysis.DeterministicProfileCenters
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoundedProbabilityMean
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Deterministic approximation by a prescribed set of profiles -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set Metric
open scoped Topology

/-- Pairwise concentration and concentration near a prescribed set give
one deterministic point of that set whose mean approximation error vanishes. -/
theorem exists_set_mean_approximation
    {S Y : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [MeasurableSpace S] [BorelSpace S] [PseudoMetricSpace Y]
    (F : S → Y) (hF : Continuous F) (T : Set Y) (hne : T.Nonempty)
    (μ : ℕ → ProbabilityMeasure S)
    (hpair : Tendsto (fun n => ∫ y, ∫ x, dist (F x) (F y)
      ∂(μ n : Measure S) ∂(μ n : Measure S)) atTop (𝓝 0))
    (hset : Tendsto (fun n => ∫ x, infDist (F x) T ∂(μ n : Measure S)) atTop (𝓝 0)) :
    ∃ c : ℕ → Y, (∀ n, c n ∈ T) ∧
      Tendsto (fun n => ∫ x, dist (F x) (c n) ∂(μ n : Measure S)) atTop (𝓝 0) := by
  let obj n y := (∫ x, dist (F x) (F y) ∂(μ n : Measure S)) + infDist (F y) T
  have hd : Continuous (fun x => infDist (F x) T) := (continuous_infDist_pt T).comp hF
  have ho n : Continuous (obj n) := by
    let d : C(S × S, ℝ) := ⟨fun p => dist (F p.2) (F p.1),
      (hF.comp continuous_snd).dist (hF.comp continuous_fst)⟩
    exact ((continuous_integral_compact_function (μ n)).comp d.curry.continuous).add hd
  have hi n (g : S → ℝ) (hg : Continuous g) : Integrable g (μ n : Measure S) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hex n : ∃ y : S, obj n y ≤
      (∫ z, ∫ x, dist (F x) (F z) ∂(μ n : Measure S) ∂(μ n : Measure S)) +
      ∫ x, infDist (F x) T ∂(μ n : Measure S) := by
    obtain ⟨y, hy⟩ := exists_le_integral (hi n (obj n) (ho n))
    refine ⟨y, hy.trans_eq ?_⟩
    have hc : Continuous (fun y => ∫ x, dist (F x) (F y) ∂(μ n : Measure S)) := by
      have hh := (ho n).sub hd
      change Continuous (fun y => obj n y - infDist (F y) T) at hh
      simpa only [obj, add_sub_cancel_right] using hh
    exact integral_add (hi n _ hc) (hi n _ hd)
  choose y hy using hex
  have ht n : ∃ c ∈ T, dist (F (y n)) c < infDist (F (y n)) T + 1 / ((n : ℝ) + 1) :=
    (infDist_lt_iff hne).mp (lt_add_of_pos_right _ (by positivity))
  choose c hc hdistance using ht
  refine ⟨c, hc, ?_⟩
  have hbound n : (∫ x, dist (F x) (c n) ∂(μ n : Measure S)) ≤
      (∫ z, ∫ x, dist (F x) (F z) ∂(μ n : Measure S) ∂(μ n : Measure S)) +
      (∫ x, infDist (F x) T ∂(μ n : Measure S)) + 1 / ((n : ℝ) + 1) := by
    calc
      _ ≤ ∫ x, dist (F x) (F (y n)) + dist (F (y n)) (c n) ∂(μ n : Measure S) :=
        integral_mono (hi n _ (hF.dist continuous_const))
          (hi n _ ((hF.dist continuous_const).add continuous_const))
          (fun x => dist_triangle (F x) (F (y n)) (c n))
      _ = (∫ x, dist (F x) (F (y n)) ∂(μ n : Measure S)) + dist (F (y n)) (c n) := by
        rw [integral_add (hi n _ (hF.dist continuous_const)) (integrable_const _)]
        simp
      _ ≤ obj n (y n) + 1 / ((n : ℝ) + 1) := by dsimp only [obj]; linarith [hdistance n]
      _ ≤ _ := add_le_add (hy n) le_rfl
  exact squeeze_zero (fun n => integral_nonneg (fun _ => dist_nonneg)) hbound
    (by simpa using (hpair.add hset).add tendsto_one_div_add_atTop_nhds_zero_nat)

/-- On a compact sample space, distance concentration in probability
implies the pairwise first-moment hypothesis used above. -/
theorem pair_mean_tendsto_zero_of_probability
    {S Y : Type*} [TopologicalSpace S] [CompactSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S] [PseudoMetricSpace Y]
    (F : S → Y) (hF : Continuous F) (μ : ℕ → ProbabilityMeasure S)
    (hp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure S).prod (μ n : Measure S) {p | ε ≤ dist (F p.1) (F p.2)})
        atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, ∫ x, dist (F x) (F y)
      ∂(μ n : Measure S) ∂(μ n : Measure S)) atTop (𝓝 0) := by
  let d : S × S → ℝ := fun p => dist (F p.1) (F p.2)
  have hd : Continuous d := (hF.comp continuous_fst).dist (hF.comp continuous_snd)
  obtain ⟨C, hC⟩ := (isCompact_range hd).bddAbove
  let ν : ℕ → ProbabilityMeasure (S × S) := fun n => ⟨(μ n : Measure S).prod (μ n : Measure S), inferInstance⟩
  have hh := bounded_mean_tendsto_zero_of_bad_probabilities ν (fun _ => d)
    (fun _ => hd.measurable) (fun _ p => ⟨dist_nonneg, hC (mem_range_self p)⟩) hp
  have hi n : Integrable d ((μ n : Measure S).prod (μ n : Measure S)) :=
    hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change Tendsto (fun n => ∫ p, d p ∂((μ n : Measure S).prod (μ n : Measure S)))
    atTop (𝓝 0) at hh
  simpa only [integral_prod_symm d (hi _)] using hh

/-- Compactness also bounds the distance to any fixed nonempty target set. -/
theorem set_distance_mean_tendsto_zero_of_probability
    {S Y : Type*} [TopologicalSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] [PseudoMetricSpace Y]
    (F : S → Y) (hF : Continuous F) (T : Set Y)
    (μ : ℕ → ProbabilityMeasure S)
    (hp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure S) {x | ε ≤ infDist (F x) T}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, infDist (F x) T ∂(μ n : Measure S)) atTop (𝓝 0) := by
  have hd : Continuous (fun x => infDist (F x) T) := (continuous_infDist_pt T).comp hF
  obtain ⟨C, hC⟩ := (isCompact_range hd).bddAbove
  exact bounded_mean_tendsto_zero_of_bad_probabilities μ _ (fun _ => hd.measurable)
    (fun _ x => ⟨infDist_nonneg, hC (mem_range_self x)⟩) hp

end PolycyclicRecognition

end

end OAI
