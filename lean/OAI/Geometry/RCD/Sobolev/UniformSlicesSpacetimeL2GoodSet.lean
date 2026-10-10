import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Strong spacetime convergence with bounds at good times

A single countable exceptional time set is null for Lebesgue measure.
The amplitude bound is needed only at good interior times; values on the
exceptional set and outside the time cylinder are unrestricted.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem uniform_slices_spacetime_L2_on_good_times
    {Y : Type*} [MeasurableSpace Y] [PseudoMetricSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {δ M : ℝ}
    (f : ℕ → ℝ → Y → ℝ) (g : ℝ → Y → ℝ)
    (hf : ∀ k, Measurable (Function.uncurry (f k)))
    (hg : Measurable (Function.uncurry g))
    (hb : ∀ k t, t ∈ Ioo δ 1 → ∀ x, |f k t x| ≤ M)
    (N : Set ℝ) (hN : N.Countable)
    (hgb : ∀ t ∈ Ioo δ 1, t ∉ N → ∀ x, |g t x| ≤ M)
    (hl : ∀ t ∈ Ioo δ 1, t ∉ N → TendstoUniformly (fun k => f k t) (g t) atTop) :
    Tendsto (fun k => ∫ q : ℝ × Y, (f k q.1 q.2-g q.1 q.2)^2
      ∂(volume.restrict (Ioo δ 1)).prod μ) atTop (𝓝 0) := by
  let ν := (volume.restrict (Ioo δ 1)).prod μ
  have hgood : ∀ᵐ t ∂volume.restrict (Ioo δ 1), t ∈ Ioo δ 1 ∧ t ∉ N :=
    (ae_restrict_mem measurableSet_Ioo).and (ae_restrict_of_ae (hN.ae_notMem volume))
  have hpair : ∀ᵐ q ∂ν, q.1 ∈ Ioo δ 1 ∧ q.1 ∉ N :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hgood
  have hlim : ∀ᵐ q ∂ν, Tendsto (fun k => (f k q.1 q.2-g q.1 q.2)^2) atTop (𝓝 0) := by
    filter_upwards [hpair] with q hq
    have hh := (((hl q.1 hq.1 hq.2).tendsto_at q.2).sub_const (g q.1 q.2)).pow 2
    simpa only [sub_self,zero_pow (by norm_num : 2 ≠ 0)] using hh
  have hdom (k : ℕ) : ∀ᵐ q ∂ν, ‖(f k q.1 q.2-g q.1 q.2)^2‖ ≤ 4*M^2 := by
    filter_upwards [hpair] with q hq
    have habs : |f k q.1 q.2-g q.1 q.2| ≤ 2*M :=
      (abs_sub _ _).trans (by linarith [hb k q.1 hq.1 q.2,hgb q.1 hq.1 hq.2 q.2])
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _ = |f k q.1 q.2-g q.1 q.2|^2 := (sq_abs _).symm
      _ ≤ (2*M)^2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = _ := by ring
  have hh := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => 4*M^2)
    (fun k => (((hf k).sub hg).pow_const 2).aestronglyMeasurable)
    (integrable_const _) hdom hlim
  simp only [integral_zero] at hh
  exact hh

end RegularPointCoordinates

end

end OAI
