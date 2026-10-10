import OAI.MeasureTheory.Falconer.Estimates.MonotoneLowpass
import OAI.MeasureTheory.Falconer.Measures.DistributionAbsoluteContinuity

namespace OAI

/-!
# Monotone scalar shell reconstruction

This is the analytic reconstruction needed in all dimensions. The measures
remain one-dimensional original-distance pushforwards. Decreasing measures
may approach their limit arbitrarily slowly; only the approximating shell
errors and shell energies are summable.
-/

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

noncomputable def movingShellL1Error (α τ : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    Lp (α := ℝ) ℂ 1 volume :=
  shellL1Error (α n) τ n

theorem movingShellL1Error_norm_summable (α τ : ℕ → FiniteMeasure ℝ)
    (h : Summable (fun n => (variationDistance (α n) (τ (n+1))).toReal)) :
    Summable (fun n => ‖movingShellL1Error α τ n‖) := by
  exact (h.mul_right (∫ x, ‖sourceShellKernel 0 x‖)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => shellL1Error_norm_le (α n) τ n)

noncomputable def monotoneVariationTerm (α : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    Lp (α := ℝ) ℂ 1 volume :=
  dyadicLowTerm (n+1) ⟨(α n : Measure ℝ) - α (n+1), inferInstance⟩ -
  dyadicLowTerm 0 ⟨(α n : Measure ℝ) - α (n+1), inferInstance⟩

/-- Distributional limit of the shells of the varying monotone measures. -/
theorem monotone_shell_tests_tendsto (α : ℕ → FiniteMeasure ℝ)
    (τ : FiniteMeasure ℝ) (hα : Antitone (fun n => (α n : Measure ℝ)))
    (hle : ∀ n, (τ : Measure ℝ) ≤ α n)
    (hmass : Tendsto (fun n => ((α n : Measure ℝ) - τ).real univ) atTop (𝓝 0))
    (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun M => ∑ j ∈ Finset.range M,
      ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel j) (α j) x) atTop
      (𝓝 (schwartzLpTest 1 φ (∑' n, monotoneVariationTerm α n) +
        ((∫ x, φ x ∂(τ : Measure ℝ)) - schwartzLpTest 1 φ (dyadicLowTerm 0 τ)))) := by
  have hz : Summable (monotoneVariationTerm α) :=
    (summable_dyadicLowTerm_decrements α hα).of_norm
  have hvar := schwartzLpTest_sum_tendsto 1 φ (monotoneVariationTerm α) hz
  have herr := (dyadicLowTerm_tail_tendsto α τ hle hmass id).sub
    (dyadicLowTerm_tail_tendsto α τ hle hmass (fun _ => 0))
  simp only [sub_self] at herr
  have htesterr := (schwartzLpTest 1 φ).continuous.tendsto 0 |>.comp herr
  simp only [map_zero] at htesterr
  have hlast := ((dyadicLowTerm_test_tendsto τ φ).sub_const
    (schwartzLpTest 1 φ (dyadicLowTerm 0 τ))).add htesterr
  simp only [add_zero] at hlast
  have hlast' : Tendsto (fun M => schwartzLpTest 1 φ
      (dyadicLowTerm M (α M) - dyadicLowTerm 0 (α M))) atTop
      (𝓝 ((∫ x, φ x ∂(τ : Measure ℝ)) -
        schwartzLpTest 1 φ (dyadicLowTerm 0 τ))) := by
    convert hlast using 1
    funext M
    simp only [Function.comp_apply, map_sub, id_eq]
    abel
  have htotal := hvar.add hlast'
  convert htotal using 1
  funext M
  rw [← map_sum, ← map_add]
  change _ = schwartzLpTest 1 φ
    ((∑ n ∈ Finset.range M,
      (dyadicLowTerm (n+1) ⟨(α n : Measure ℝ) - α (n+1), inferInstance⟩ -
      dyadicLowTerm 0 ⟨(α n : Measure ℝ) - α (n+1), inferInstance⟩)) +
      (dyadicLowTerm M (α M) - dyadicLowTerm 0 (α M)))
  rw [← dyadicLowTerm_summation_by_parts α hα M, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (dyadicLowTerm_band_test j (α j) φ).symm

/-- The monotone shell criterion for the positive approximants used in the
manuscript. The hypotheses are summability and mass convergence, with no
rate imposed on the monotone limit. -/
theorem monotone_shell_criterion (α τ : ℕ → FiniteMeasure ℝ)
    (μ : FiniteMeasure ℝ) (hα : Antitone (fun n => (α n : Measure ℝ)))
    (hle : ∀ n, (μ : Measure ℝ) ≤ α n)
    (hmass : Tendsto (fun n => ((α n : Measure ℝ) - μ).real univ) atTop (𝓝 0))
    (herror : Summable (fun n => (variationDistance (α n) (τ (n+1))).toReal))
    (hshell : Summable (fun n => ‖shellL2Term τ n‖)) :
    (μ : Measure ℝ) ≪ volume := by
  have he := (movingShellL1Error_norm_summable α τ herror).of_norm
  have hz := (summable_dyadicLowTerm_decrements α hα).of_norm
  let a : Lp (α := ℝ) ℂ 1 volume :=
    dyadicLowTerm 0 μ + ∑' n, movingShellL1Error α τ n - ∑' n, monotoneVariationTerm α n
  let b : Lp (α := ℝ) ℂ 2 volume := ∑' n, shellL2Term τ n
  have htests (φ : 𝓢(ℝ, ℂ)) :
      schwartzLpTest 1 φ a + schwartzLpTest 2 φ b = ∫ x, φ x ∂(μ : Measure ℝ) := by
    have hsum := (schwartzLpTest_sum_tendsto 1 φ _ he).add
      (schwartzLpTest_sum_tendsto 2 φ _ hshell.of_norm)
    have hsame (M : ℕ) :
        (∑ j ∈ Finset.range M, schwartzLpTest 1 φ (movingShellL1Error α τ j)) +
        (∑ j ∈ Finset.range M, schwartzLpTest 2 φ (shellL2Term τ j)) =
        ∑ j ∈ Finset.range M,
          ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel j) (α j) x := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact schwartzLpTest_shell_recombine (α j) τ φ j
    simp_rw [hsame] at hsum
    have huniq := tendsto_nhds_unique hsum (monotone_shell_tests_tendsto α μ hα hle hmass φ)
    dsimp [a, b]
    simp only [map_sub, map_add]
    change _ = _ at huniq
    linear_combination huniq
  let f : ℝ → ℂ := fun x => a x + b x
  have hf : LocallyIntegrable f volume :=
    ((Lp.memLp a).locallyIntegrable (by norm_num)).add
      ((Lp.memLp b).locallyIntegrable (by norm_num))
  apply absolutelyContinuous_of_smooth_test_density μ f hf
  intro g hg hc
  let φ : 𝓢(ℝ, ℂ) := (hc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg)
  have ht := htests φ
  rw [schwartzLpTest_apply, schwartzLpTest_apply] at ht
  have ha := (φ.memLp_top volume).integrable_mul (Lp.memLp a)
  have hb := (φ.memLp 2 volume).integrable_mul (Lp.memLp b)
  change Integrable (fun x => φ x * a x) at ha
  change Integrable (fun x => φ x * b x) at hb
  change (∫ x, φ x ∂(μ : Measure ℝ)) = ∫ x, g x • f x
  rw [← ht, ← integral_add ha hb]
  apply integral_congr_ae
  filter_upwards with x
  change φ x * a x + φ x * b x = _
  simp only [φ, f, Complex.real_smul, mul_add]
  rfl

/-- The power-decay form used by the distance measures. Finite
initial scales do not affect the conclusion. -/
theorem monotone_shell_criterion_of_power_bounds (α τ : ℕ → FiniteMeasure ℝ)
    (μ : FiniteMeasure ℝ) (hα : Antitone (fun n => (α n : Measure ℝ)))
    (hle : ∀ n, (μ : Measure ℝ) ≤ α n)
    (hmass : Tendsto (fun n => ((α n : Measure ℝ) - μ).real univ) atTop (𝓝 0))
    {η γ Ctv Cshell : ℝ} (hη : 0 < η) (hγ : 0 < γ)
    (hCtv : 0 < Ctv) (hCshell : 0 < Cshell) (N₀ : ℕ)
    (herror : ∀ n ≥ N₀, variationDistance (α n) (τ (n+1)) ≤
      ENNReal.ofReal (Ctv * (2 : ℝ)^(-η * (n : ℝ))))
    (hshell : ∀ N ≥ N₀, shellEnergy (τ N) N ≤ Cshell * (2 : ℝ)^(-γ * (N : ℝ))) :
    (μ : Measure ℝ) ≪ volume := by
  apply monotone_shell_criterion α τ μ hα hle hmass
  · apply ((summable_dyadic_decay hη).mul_left Ctv).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop N₀] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (herror n hn)
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    exact hh
  · exact shellL2Term_norm_summable τ hγ hCshell N₀ hshell

end PlanarFalconer

end OAI
