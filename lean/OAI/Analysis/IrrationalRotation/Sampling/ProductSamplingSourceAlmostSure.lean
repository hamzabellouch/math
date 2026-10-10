import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingExpectedTransport
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingCoordinateScales

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.ProductModel.SamplingWeights

theorem ae_all_sourceTestedError_of_coordinate_scale_bounds
    {ι : Type*} [Countable ι] {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (hN : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (N n))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hSle : ∀ n i, i < p.prefixCount (n + 1) → S i ≤ p.N n)
    (endpoint : ι → Bool) (I : ι → Finset ℕ) (a b c d : ι → ℕ → ℝ) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i =>
      ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i))),
      ∀ q, ∃ hf : ∀ n,
        MemLp (sourceTestedError p N (endpoint q) (I q)
          (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ)
          2 baseMeasure,
        Summable (fun n => ∫ x,
          (sourceTestedError p N (endpoint q) (I q)
            (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ x)^2
          ∂baseMeasure) ∧
        Tendsto (fun n => ‖(hf n).toLp (sourceTestedError p N (endpoint q) (I q)
          (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ)‖)
          atTop (𝓝 0) := by
  let μ : ℕ → Measure ℝ := fun i =>
    ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i))
  let (i : ℕ) : IsProbabilityMeasure (μ i) := by
    dsimp [μ]
    rw [← UniformIntervalPhase.lambdaLaw_eq_cond (S i) (hS i)]
    exact UniformIntervalPhase.lambdaLaw_probability (S i) (hS i)
  have hmTop : Tendsto (fun n => (p.m n : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => show (2 : ℝ)^n ≤ (p.m n : ℝ) from by
      exact_mod_cast hp.m_ge_pow_self n)
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hmEv : ∀ᶠ n in atTop, 200 ≤ p.m n := by
    filter_upwards [hmTop.eventually_ge_atTop 200] with n hn
    exact_mod_cast hn
  apply ae_all_sourceTestedError_of_moment_bound hp N hN endpoint I
    (fun q i => Ico (a q i) (b q i)) (fun q i => Ico (c q i) (d q i))
    (fun _ _ => measurableSet_Ico) (fun _ _ => measurableSet_Ico)
    (Measure.infinitePi μ) (fun _ => 8) (fun _ => by norm_num)
  intro q
  filter_upwards [hN, hmEv] with n hn hm
  simpa only [μ, neg_div] using sourceTestedError_expected_le_common hp N hm hn S hS (hSle n)
    (endpoint q) (I q) (a q) (b q) (c q) (d q)

theorem ae_all_sourceTestedError
    {ι : Type*} [Countable ι] {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (hN : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (N n))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ s, ∀ i ∈ ProductPhases.consecutiveBlock p.m s,
      S i = (p.m s : ℝ) * p.K s)
    (endpoint : ι → Bool) (I : ι → Finset ℕ) (a b c d : ι → ℕ → ℝ) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i =>
      ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i))),
      ∀ q, ∃ hf : ∀ n,
        MemLp (sourceTestedError p N (endpoint q) (I q)
          (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ)
          2 baseMeasure,
        Summable (fun n => ∫ x,
          (sourceTestedError p N (endpoint q) (I q)
            (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ x)^2
          ∂baseMeasure) ∧
        Tendsto (fun n => ‖(hf n).toLp (sourceTestedError p N (endpoint q) (I q)
          (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ)‖)
          atTop (𝓝 0) :=
  ae_all_sourceTestedError_of_coordinate_scale_bounds hp N hN S hS
    (fun n _ hi => (hp.coordinate_scale_bounds S hblock n hi).2) endpoint I a b c d

end Invariant233.ProductModel.SamplingWeights

end

end OAI
