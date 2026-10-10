import Mathlib
import OAI.Analysis.IrrationalRotation.Product.IndependentAngles
import OAI.Analysis.IrrationalRotation.Analysis.ModuloIntervalMeasure

namespace OAI

open MeasureTheory Filter
open scoped Topology

namespace Invariant233.ProductPhases

theorem threshold_fiber_countable {k : ℝ} (hk : k ≠ 0) (c : ℝ) :
    Set.Countable {x : ℝ | 1 - Int.fract (k * x) = c} := by
  apply (Set.countable_range (fun n : ℤ => ((n : ℝ) + 1 - c) / k)).mono
  intro x hx
  refine ⟨Int.floor (k * x), ?_⟩
  apply (div_eq_iff hk).mpr
  change 1 - (k * x - (Int.floor (k * x) : ℝ)) = c at hx
  nlinarith

theorem ae_threshold_ne (μ : Measure ℝ) [NullSingletonClass μ]
    {k : ℝ} (hk : k ≠ 0) (c : ℝ) :
    ∀ᵐ x ∂μ, 1 - Int.fract (k * x) ≠ c :=
  (threshold_fiber_countable hk c).ae_notMem μ

theorem threshold_Ioo_ae_eq_Icc (μ : Measure ℝ) [NullSingletonClass μ]
    {k : ℝ} (hk : k ≠ 0) (b : ℝ) :
    {x : ℝ | 1 - Int.fract (k * x) ∈ Set.Ioo b (1 - b)} =ᵐ[μ]
      {x : ℝ | 1 - Int.fract (k * x) ∈ Set.Icc b (1 - b)} := by
  apply eventuallyEqSet_iff.mpr
  filter_upwards [ae_threshold_ne μ hk b, ae_threshold_ne μ hk (1 - b)]
    with x hlo hhi
  change (b < 1 - Int.fract (k * x) ∧ 1 - Int.fract (k * x) < 1 - b) ↔
    (b ≤ 1 - Int.fract (k * x) ∧ 1 - Int.fract (k * x) ≤ 1 - b)
  constructor
  · exact fun h => ⟨h.1.le, h.2.le⟩
  · exact fun h => ⟨lt_of_le_of_ne h.1 hlo.symm, lt_of_le_of_ne h.2 hhi⟩

theorem uniform_angle_strict_threshold_miss_le {N k b : ℝ} (hN : 0 < N)
    (hk : N / 4 ≤ |k|) (hb : 0 ≤ b) :
    (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))).real
      {x : ℝ | 1 - Int.fract (k * x) ∉ Set.Ioo b (1 - b)} ≤ 10 * b := by
  let μ : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))
  let : NullSingletonClass μ :=
    InvariantProjection.IndependentAngles.intervalLaw_nullSingletonClass _ _
  have hk0 : k ≠ 0 := by
    intro h
    simp only [h, abs_zero] at hk
    linarith
  have heq := threshold_Ioo_ae_eq_Icc μ hk0 b
  have hcomp : {x : ℝ | 1 - Int.fract (k * x) ∉ Set.Ioo b (1 - b)} =ᵐ[μ]
      {x : ℝ | 1 - Int.fract (k * x) ∉ Set.Icc b (1 - b)} := by
    filter_upwards [heq] with x hx
    exact congrArg Not hx
  rw [measureReal_congr hcomp]
  exact Invariant233.ModuloIntervalMeasure.uniform_angle_threshold_miss_le hN hk hb

theorem continuousAt_threshold_of_mem_Ioo {b k x : ℝ} (hb : 0 < b)
    (hx : 1 - Int.fract (k * x) ∈ Set.Ioo b (1 - b)) :
    ContinuousAt (fun y : ℝ => 1 - Int.fract (k * y)) x := by
  have hnotint : k * x ≠ (Int.floor (k * x) : ℝ) := by
    intro he
    have hf : Int.fract (k * x) = 0 := by exact sub_eq_zero.mpr he
    rw [hf] at hx
    have := hx.2
    linarith
  exact continuousAt_const.sub ((continuousAt_fract hnotint).comp
    (continuous_const.mul continuous_id).continuousAt)

theorem eventually_threshold_mem_Ioo {b k x : ℝ} (hb : 0 < b)
    (hx : 1 - Int.fract (k * x) ∈ Set.Ioo b (1 - b)) :
    ∀ᶠ y in 𝓝 x, 1 - Int.fract (k * y) ∈ Set.Ioo b (1 - b) :=
  (continuousAt_threshold_of_mem_Ioo hb hx).eventually_mem (isOpen_Ioo.mem_nhds hx)

theorem eventually_finite_phase_tests {ι : Type*} (powers : Finset ℤ)
    (witness : ℤ → Finset ι) (θ : ι → ℝ) {b : ℝ} (hb : 0 < b)
    (hgood : ∀ k ∈ powers, ∀ i ∈ witness k,
      1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Ioo b (1 - b)) :
    ∀ᶠ φ in 𝓝 θ, ∀ k ∈ powers, ∀ i ∈ witness k,
      1 - Int.fract ((k : ℝ) * φ i) ∈ Set.Ioo b (1 - b) := by
  apply (Filter.eventually_all_finset powers).mpr
  intro k hk
  apply (Filter.eventually_all_finset (witness k)).mpr
  intro i hi
  exact (continuous_apply i).continuousAt.eventually
    (eventually_threshold_mem_Ioo hb (hgood k hk i hi))

end Invariant233.ProductPhases

end OAI
