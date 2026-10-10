import OAI.Analysis.IrrationalRotation.Model.ProductScaleSampling
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingAsymptotics
import OAI.Analysis.IrrationalRotation.Sampling.ProductInfiniteSamplingMoments

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233.ProductScaleData

def samplingMomentBudget (p : ProductScaleData) (s : ℕ → Finset ℕ)
    (c : ℝ) (n : ℕ) : ℝ :=
  (c * (p.m n : ℝ) ^ (3 / 5 : ℝ) * Real.log (p.m n : ℝ)) ^
      p.prefixCount (n + 1) / ((s n).card : ℝ) +
    3 * ((p.prefixCount (n + 1) : ℝ) * (c * (p.m n : ℝ) ^ (-50 : ℝ)) *
      (1 + c * (p.m n : ℝ) ^ (-6 / 5 : ℝ) +
        c * (p.m n : ℝ) ^ (-50 : ℝ)) ^ (p.prefixCount (n + 1) - 1))

end Invariant233.ProductScaleData

namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem summable_samplingMomentBudget (s : ℕ → Finset ℕ)
    (hs : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (s n))
    (c : ℝ) (hc : 0 ≤ c) : Summable (p.samplingMomentBudget s c) := by
  have hm : ∀ n, (2 : ℝ) ^ n ≤ (p.m n : ℝ) := by
    intro n
    exact_mod_cast hp.m_ge_pow_self n
  have hmTop : Tendsto (fun n => (p.m n : ℝ)) atTop atTop :=
    tendsto_atTop_mono hm (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hb := hmTop.eventually (ProductSampling.eventually_exact_second_moment_le c hc)
  apply (ProductSampling.sampling_error_majorant_summable hm
    ((303 / 100 : ℝ) * c * Real.exp ((101 / 50 : ℝ) * c))).of_norm_bounded_eventually_nat
  filter_upwards [hb, hs] with n hn hsn
  have hm1 : (1 : ℝ) ≤ p.m n := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 100) (hp.m_ge_100 n))
  have hlog : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg hm1
  have hnonneg : 0 ≤ p.samplingMomentBudget s c n := by
    dsimp [ProductScaleData.samplingMomentBudget]
    positivity
  rw [Real.norm_of_nonneg hnonneg]
  exact hn _ _ (hp.prefix_count_succ_le n) hsn.cardinality

theorem ae_sampling_l2_convergence
    {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Countable ι]
    {μ : Measure Ω} {ν : Measure X} [SFinite μ] [SFinite ν]
    (s : ℕ → Finset ℕ)
    (hs : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (s n))
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    {F : ι → ℕ → Ω → X → ℝ}
    (hF : ∀ i n, MemLp (Function.uncurry (F i n)) 2 (μ.prod ν))
    (hbound : ∀ i, ∀ᶠ n in atTop,
      (∫ ω, ∫ x, (F i n ω x) ^ 2 ∂ν ∂μ) ≤ p.samplingMomentBudget s (c i) n) :
    ∀ᵐ ω ∂μ, ∀ i, ∃ hf : ∀ n, MemLp (F i n ω) 2 ν,
      Summable (fun n => ∫ x, (F i n ω x) ^ 2 ∂ν) ∧
      Tendsto (fun n => ‖(hf n).toLp (F i n ω)‖) atTop (𝓝 0) := by
  exact ProductSampling.ae_all_memLp_and_tendsto_norm_of_eventually_expected_sq
    F (fun i => p.samplingMomentBudget s (c i))
    (fun i n => (hF i n).aestronglyMeasurable)
    (fun i n => (hF i n).integrable_sq) hbound
    (fun i => hp.summable_samplingMomentBudget s hs (c i) (hc i))

end Invariant233.ProductScaleLaws

end

end OAI
