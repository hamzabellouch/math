import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTestIntegrability
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingNumericalMajorant
import OAI.Analysis.IrrationalRotation.Sampling.ProductInfiniteSamplingMoments

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

def sourceTestedError (p : ProductScaleData) (N : ℕ → Finset ℕ)
    (endpoint : Bool) (I : Finset ℕ) (E F : ℕ → Set ℝ)
    (n : ℕ) (θ : ℕ → ℝ) (x : Base) : ℝ :=
  ((N n).card : ℝ)⁻¹ * (∑ k ∈ N n,
    testedProduct endpoint (Finset.range (p.prefixCount (n + 1))) I
      ((p.m n : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m n : ℝ) ^ 2) E F θ k x) -
    testedIdeal endpoint (Finset.range (p.prefixCount (n + 1))) I
      ((p.m n : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m n : ℝ) ^ 2) E F x

theorem memLp_sourceTestedError_pair {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (endpoint : Bool) (I : Finset ℕ) (E F : ℕ → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] (n : ℕ) :
    MemLp (fun z : (ℕ → ℝ) × Base => sourceTestedError p N endpoint I E F n z.1 z.2)
      2 (ν.prod baseMeasure) := by
  have hm : 0 < (p.m n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 100) (hp.m_ge_100 n))
  exact memLp_testedAverageError_pair endpoint (Finset.range (p.prefixCount (n + 1))) I
    (N n) (Real.rpow_pos_of_pos hm _) (by positivity) E F
    (fun i _ => hE i) (fun i _ => hF i) ν

theorem ae_sourceTestedError_of_moment_bound
    {p : ProductScaleData} (hp : ProductScaleLaws p) (N : ℕ → Finset ℕ)
    (hN : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (N n))
    (endpoint : Bool) (I : Finset ℕ) (E F : ℕ → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] (c : ℝ) (hc : 0 ≤ c)
    (herror : ∀ᶠ n in atTop,
      (∫ θ, ∫ x, (sourceTestedError p N endpoint I E F n θ x) ^ 2 ∂baseMeasure ∂ν) ≤
        (c * (p.m n : ℝ) ^ (3 / 5 : ℝ) * Real.log (p.m n)) ^
            (p.prefixCount (n + 1)) / ((N n).card : ℝ) +
          3 * ((p.prefixCount (n + 1) : ℝ) * (c * (p.m n : ℝ) ^ (-50 : ℝ)) *
            (1 + c * (p.m n : ℝ) ^ (-(6 / 5 : ℝ)) +
              c * (p.m n : ℝ) ^ (-50 : ℝ)) ^ (p.prefixCount (n + 1) - 1))) :
    ∀ᵐ θ ∂ν, ∃ hf : ∀ n, MemLp (sourceTestedError p N endpoint I E F n θ) 2 baseMeasure,
      Summable (fun n => ∫ x, (sourceTestedError p N endpoint I E F n θ x) ^ 2 ∂baseMeasure) ∧
      Tendsto (fun n => ‖(hf n).toLp (sourceTestedError p N endpoint I E F n θ)‖)
        atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun n =>
    ∫ θ, ∫ x, (sourceTestedError p N endpoint I E F n θ x) ^ 2 ∂baseMeasure ∂ν
  have he : ∀ n, 0 ≤ e n := fun n =>
    integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))
  have hsum : Summable e :=
    hp.summable_sampling_error_of_moment_bound N hN c hc e he herror
  exact ProductSampling.ae_memLp_and_tendsto_norm_of_summable_expected_sq
    (sourceTestedError p N endpoint I E F) e
    (fun n => (memLp_sourceTestedError_pair hp N endpoint I E F hE hF ν n).aestronglyMeasurable)
    (fun n => (memLp_sourceTestedError_pair hp N endpoint I E F hE hF ν n).integrable_sq)
    (fun _ => le_rfl) hsum

theorem ae_all_sourceTestedError_of_moment_bound
    {ι : Type*} [Countable ι] {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (hN : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (N n))
    (endpoint : ι → Bool) (I : ι → Finset ℕ) (E F : ι → ℕ → Set ℝ)
    (hE : ∀ j i, MeasurableSet (E j i)) (hF : ∀ j i, MeasurableSet (F j i))
    (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j)
    (herror : ∀ j, ∀ᶠ n in atTop,
      (∫ θ, ∫ x, (sourceTestedError p N (endpoint j) (I j) (E j) (F j) n θ x) ^ 2
        ∂baseMeasure ∂ν) ≤
        (c j * (p.m n : ℝ) ^ (3 / 5 : ℝ) * Real.log (p.m n)) ^
            (p.prefixCount (n + 1)) / ((N n).card : ℝ) +
          3 * ((p.prefixCount (n + 1) : ℝ) * (c j * (p.m n : ℝ) ^ (-50 : ℝ)) *
            (1 + c j * (p.m n : ℝ) ^ (-(6 / 5 : ℝ)) +
              c j * (p.m n : ℝ) ^ (-50 : ℝ)) ^ (p.prefixCount (n + 1) - 1))) :
    ∀ᵐ θ ∂ν, ∀ j, ∃ hf : ∀ n,
      MemLp (sourceTestedError p N (endpoint j) (I j) (E j) (F j) n θ) 2 baseMeasure,
      Summable (fun n => ∫ x,
        (sourceTestedError p N (endpoint j) (I j) (E j) (F j) n θ x) ^ 2 ∂baseMeasure) ∧
      Tendsto (fun n => ‖(hf n).toLp
        (sourceTestedError p N (endpoint j) (I j) (E j) (F j) n θ)‖) atTop (𝓝 0) := by
  exact ae_all_iff.mpr fun j => ae_sourceTestedError_of_moment_bound hp N hN
    (endpoint j) (I j) (E j) (F j) (hE j) (hF j) ν (c j) (hc j) (herror j)

end Invariant233.ProductModel.SamplingWeights

end

end OAI
