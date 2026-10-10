import OAI.Analysis.IrrationalRotation.Sampling.ProductInfiniteSamplingMoments
import OAI.Analysis.IrrationalRotation.Model.ProductSampling

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace Invariant233.ProductSampling

theorem exists_uniform_norm_bound_of_error_tendsto
    {E : Type*} [SeminormedAddCommGroup E] (f z : ℕ → E)
    {C : ℝ} (hz : ∀ n, ‖z n‖ ≤ C)
    (herr : Tendsto (fun n => ‖f n - z n‖) atTop (𝓝 0)) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ n, ‖f n‖ ≤ H := by
  obtain ⟨K, hK⟩ := herr.bddAbove_range
  refine ⟨max 0 (K + C), le_max_left _ _, fun n => ?_⟩
  calc
    ‖f n‖ ≤ ‖f n - z n‖ + ‖z n‖ := norm_le_norm_sub_add _ _
    _ ≤ K + C := add_le_add (hK (Set.mem_range_self n)) (hz n)
    _ ≤ max 0 (K + C) := le_max_right _ _

theorem sqrt_integral_sq_eq_toLp_norm
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : X → ℝ} (hf : MemLp f 2 ν) :
    Real.sqrt (∫ x, (f x) ^ 2 ∂ν) = ‖hf.toLp f‖ := by
  have heq : ‖hf.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂ν := by
    rw [InvariantRotation.SamplingMomentBounds.l2_norm_sq_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  rw [← heq, Real.sqrt_sq (norm_nonneg _)]

theorem tendsto_norm_toLp_sub_of_integral_sq
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (f z : ℕ → X → ℝ) (hf : ∀ n, MemLp (f n) 2 ν)
    (hz : ∀ n, MemLp (z n) 2 ν)
    (herr : Tendsto (fun n => ∫ x, (f n x - z n x) ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ‖(hf n).toLp (f n) - (hz n).toLp (z n)‖) atTop (𝓝 0) := by
  have hnorm (n : ℕ) : Real.sqrt (∫ x, (f n x - z n x) ^ 2 ∂ν) =
      ‖(hf n).toLp (f n) - (hz n).toLp (z n)‖ := by
    rw [← MemLp.toLp_sub]
    exact sqrt_integral_sq_eq_toLp_norm ((hf n).sub (hz n))
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp herr
  simpa only [Function.comp_def, hnorm, Real.sqrt_zero] using h

theorem exists_uniform_toLp_norm_bound_of_energy
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (f z : ℕ → X → ℝ) (hf : ∀ n, MemLp (f n) 2 ν)
    (hz : ∀ n, MemLp (z n) 2 ν)
    {C : ℝ} (hideal : ∀ n, (∫ x, (z n x) ^ 2 ∂ν) ≤ C)
    (herr : Tendsto (fun n => ∫ x, (f n x - z n x) ^ 2 ∂ν) atTop (𝓝 0)) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ n, ‖(hf n).toLp (f n)‖ ≤ H := by
  apply exists_uniform_norm_bound_of_error_tendsto
    (fun n => (hf n).toLp (f n)) (fun n => (hz n).toLp (z n))
  · intro n
    rw [← sqrt_integral_sq_eq_toLp_norm (hz n)]
    exact Real.sqrt_le_sqrt (hideal n)
  · exact tendsto_norm_toLp_sub_of_integral_sq f z hf hz herr

end Invariant233.ProductSampling

namespace Invariant233.ProductModel

theorem hasUniformL2Marginals_of_energy_convergence
    (η : ℕ → Measure EndpointPair) (f g z w : ℕ → Base → ℝ)
    (hf : ∀ n, MemLp (f n) 2 baseMeasure)
    (hg : ∀ n, MemLp (g n) 2 baseMeasure)
    (hz : ∀ n, MemLp (z n) 2 baseMeasure)
    (hw : ∀ n, MemLp (w n) 2 baseMeasure)
    (hfnn : ∀ n, ∀ᵐ x ∂baseMeasure, 0 ≤ f n x)
    (hgnn : ∀ n, ∀ᵐ x ∂baseMeasure, 0 ≤ g n x)
    (hfirst : ∀ n, (η n).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (f n x)))
    (hsecond : ∀ n, (η n).map Prod.snd =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (g n x)))
    {C D : ℝ} (hzbound : ∀ n, (∫ x, (z n x) ^ 2 ∂baseMeasure) ≤ C)
    (hwbound : ∀ n, (∫ x, (w n x) ^ 2 ∂baseMeasure) ≤ D)
    (herrf : Tendsto (fun n => ∫ x, (f n x - z n x) ^ 2 ∂baseMeasure)
      atTop (𝓝 0))
    (herrg : Tendsto (fun n => ∫ x, (g n x - w n x) ^ 2 ∂baseMeasure)
      atTop (𝓝 0)) :
    HasUniformL2Marginals η := by
  obtain ⟨Hf, hHf, hfbound⟩ :=
    ProductSampling.exists_uniform_toLp_norm_bound_of_energy f z hf hz hzbound herrf
  obtain ⟨Hg, hHg, hgbound⟩ :=
    ProductSampling.exists_uniform_toLp_norm_bound_of_energy g w hg hw hwbound herrg
  refine ⟨max Hf Hg, hHf.trans (le_max_left _ _), fun n =>
    ⟨(hf n).toLp (f n), (hg n).toLp (g n), ?_, ?_, ?_, ?_,
      (hfbound n).trans (le_max_left _ _), (hgbound n).trans (le_max_right _ _)⟩⟩
  · filter_upwards [(hf n).coeFn_toLp, hfnn n] with x hx hnx
    rwa [hx]
  · filter_upwards [(hg n).coeFn_toLp, hgnn n] with x hx hnx
    rwa [hx]
  · rw [hfirst n]
    apply withDensity_congr_ae
    exact (hf n).coeFn_toLp.symm.fun_comp ENNReal.ofReal
  · rw [hsecond n]
    apply withDensity_congr_ae
    exact (hg n).coeFn_toLp.symm.fun_comp ENNReal.ofReal

end Invariant233.ProductModel

namespace Invariant233.ProductModel

theorem ae_hasUniformL2Marginals_of_summable_expected_errors
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    (η : Ω → ℕ → Measure EndpointPair)
    (f g z w : ℕ → Ω → Base → ℝ)
    (hz : ∀ a n, MemLp (z n a) 2 baseMeasure)
    (hw : ∀ a n, MemLp (w n a) 2 baseMeasure)
    (hfnn : ∀ a n, ∀ᵐ x ∂baseMeasure, 0 ≤ f n a x)
    (hgnn : ∀ a n, ∀ᵐ x ∂baseMeasure, 0 ≤ g n a x)
    (hfirst : ∀ a n, (η a n).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (f n a x)))
    (hsecond : ∀ a n, (η a n).map Prod.snd =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (g n a x)))
    (C D : Ω → ℝ)
    (hzbound : ∀ a n, (∫ x, (z n a x) ^ 2 ∂baseMeasure) ≤ C a)
    (hwbound : ∀ a n, (∫ x, (w n a x) ^ 2 ∂baseMeasure) ≤ D a)
    (hmeasf : ∀ n, AEStronglyMeasurable
      (fun p : Ω × Base => f n p.1 p.2 - z n p.1 p.2) (μ.prod baseMeasure))
    (hmeasg : ∀ n, AEStronglyMeasurable
      (fun p : Ω × Base => g n p.1 p.2 - w n p.1 p.2) (μ.prod baseMeasure))
    (hsqf : ∀ n, Integrable
      (fun p : Ω × Base => (f n p.1 p.2 - z n p.1 p.2) ^ 2) (μ.prod baseMeasure))
    (hsqg : ∀ n, Integrable
      (fun p : Ω × Base => (g n p.1 p.2 - w n p.1 p.2) ^ 2) (μ.prod baseMeasure))
    (b c : ℕ → ℝ)
    (hbf : ∀ᶠ n in atTop,
      (∫ a, ∫ x, (f n a x - z n a x) ^ 2 ∂baseMeasure ∂μ) ≤ b n)
    (hbg : ∀ᶠ n in atTop,
      (∫ a, ∫ x, (g n a x - w n a x) ^ 2 ∂baseMeasure ∂μ) ≤ c n)
    (hb : Summable b) (hc : Summable c) :
    ∀ᵐ a ∂μ, HasUniformL2Marginals (η a) := by
  have hef := ProductSampling.ae_memLp_and_tendsto_norm_of_eventually_expected_sq
    (fun n a x => f n a x - z n a x) b hmeasf hsqf hbf hb
  have heg := ProductSampling.ae_memLp_and_tendsto_norm_of_eventually_expected_sq
    (fun n a x => g n a x - w n a x) c hmeasg hsqg hbg hc
  filter_upwards [hef, heg] with a ha ha'
  obtain ⟨hef, hsf, _⟩ := ha
  obtain ⟨heg, hsg, _⟩ := ha'
  have hf (n : ℕ) : MemLp (f n a) 2 baseMeasure := by
    have h : MemLp ((f n a - z n a) + z n a) 2 baseMeasure := (hef n).add (hz a n)
    simpa only [sub_add_cancel] using h
  have hg (n : ℕ) : MemLp (g n a) 2 baseMeasure := by
    have h : MemLp ((g n a - w n a) + w n a) 2 baseMeasure := (heg n).add (hw a n)
    simpa only [sub_add_cancel] using h
  exact hasUniformL2Marginals_of_energy_convergence (η a)
    (fun n => f n a) (fun n => g n a) (fun n => z n a) (fun n => w n a)
    hf hg (hz a) (hw a) (hfnn a) (hgnn a) (hfirst a) (hsecond a)
    (hzbound a) (hwbound a) hsf.tendsto_atTop_zero hsg.tendsto_atTop_zero

end Invariant233.ProductModel

end

end OAI
