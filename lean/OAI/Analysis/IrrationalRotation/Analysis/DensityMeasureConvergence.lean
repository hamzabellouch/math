import Mathlib

namespace OAI

open MeasureTheory Filter Set BoundedContinuousFunction
open scoped Topology ENNReal

namespace Invariant233.GraphMeasureConvergence

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem tendsto_of_density_L1
    (μ : FiniteMeasure X) (ν : ℕ → FiniteMeasure X) (ρ : ℕ → X → ℝ)
    (hρ : ∀ n, Integrable (ρ n) (μ : Measure X))
    (hnonneg : ∀ n, 0 ≤ᵐ[(μ : Measure X)] ρ n)
    (hν : ∀ n, (ν n : Measure X) =
      (μ : Measure X).withDensity (fun x => ENNReal.ofReal (ρ n x)))
    (hL1 : Tendsto (fun n => ∫ x, ‖ρ n x - 1‖ ∂(μ : Measure X)) atTop (𝓝 0)) :
    Tendsto ν atTop (𝓝 μ) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have heq (n : ℕ) : (∫ x, f x ∂(ν n : Measure X)) -
      (∫ x, f x ∂(μ : Measure X)) =
      ∫ x, (ρ n x - 1) * f x ∂(μ : Measure X) := by
    rw [hν n, integral_withDensity_eq_integral_toReal_smul₀
      (hρ n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hprod : Integrable (fun x => ρ n x * f x) (μ : Measure X) :=
      (hρ n).mul_bdd f.continuous.measurable.aestronglyMeasurable
        (Eventually.of_forall fun x => f.norm_coe_le_norm x)
    have hi : (∫ x, (ENNReal.ofReal (ρ n x)).toReal • f x ∂(μ : Measure X)) =
        ∫ x, ρ n x * f x ∂(μ : Measure X) := by
      apply integral_congr_ae
      filter_upwards [hnonneg n] with x hx
      simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]
    rw [hi, ← integral_sub hprod (f.integrable _)]
    congr 1
    funext x
    ring
  have hbound (n : ℕ) :
      ‖(∫ x, f x ∂(ν n : Measure X)) - (∫ x, f x ∂(μ : Measure X))‖ ≤
      (∫ x, ‖ρ n x - 1‖ ∂(μ : Measure X)) * ‖f‖ := by
    rw [heq]
    calc
      ‖∫ x, (ρ n x - 1) * f x ∂(μ : Measure X)‖ ≤
          ∫ x, ‖ρ n x - 1‖ * ‖f‖ ∂(μ : Measure X) := by
        apply norm_integral_le_of_norm_le (((hρ n).sub (integrable_const 1)).norm.mul_const ‖f‖)
        exact Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)
      _ = (∫ x, ‖ρ n x - 1‖ ∂(μ : Measure X)) * ‖f‖ := integral_mul_const _ _
  have hdiff := squeeze_zero_norm hbound (by simpa only [zero_mul] using hL1.mul_const ‖f‖)
  have hsum := hdiff.add (tendsto_const_nhds (x := ∫ x, f x ∂(μ : Measure X)))
  simpa only [sub_add_cancel, zero_add] using hsum

theorem tendsto_of_density_L2
    (μ : FiniteMeasure X) [IsProbabilityMeasure (μ : Measure X)]
    (ν : ℕ → FiniteMeasure X) (ρ : ℕ → X → ℝ)
    (hρ : ∀ n, MemLp (ρ n) 2 (μ : Measure X))
    (hnonneg : ∀ n, 0 ≤ᵐ[(μ : Measure X)] ρ n)
    (hν : ∀ n, (ν n : Measure X) =
      (μ : Measure X).withDensity (fun x => ENNReal.ofReal (ρ n x)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x => ρ n x - 1) 2 (μ : Measure X))
      atTop (𝓝 0)) : Tendsto ν atTop (𝓝 μ) := by
  apply tendsto_of_density_L1 μ ν ρ (fun n => (hρ n).integrable (by norm_num)) hnonneg hν
  have he (n : ℕ) : MemLp (fun x => ρ n x - 1) 2 (μ : Measure X) :=
    (hρ n).sub (memLp_const 1)
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n => ?_) (by simpa only [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL2)
  rw [integral_norm_eq_lintegral_enorm (he n).aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm (he n).aestronglyMeasurable]
  exact ENNReal.toReal_mono (he n).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

end Invariant233.GraphMeasureConvergence

end OAI
