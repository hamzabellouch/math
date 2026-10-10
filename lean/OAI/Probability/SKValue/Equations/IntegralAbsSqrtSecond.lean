import Mathlib
import OAI.Probability.SKValue.Processes.Measurable

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma integral_abs_le_sqrt_second {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂μ)≤Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  have hab : MemLp (fun ω ↦ |f ω|) 2 μ := by simpa only [Real.norm_eq_abs] using hf.norm
  have hv := variance_nonneg (fun ω ↦ |f ω|) μ
  rw [variance_eq_sub hab] at hv
  simp only [Pi.pow_apply,sq_abs] at hv
  apply (Real.le_sqrt (integral_nonneg (fun _ ↦ abs_nonneg _)) (integral_nonneg (fun _ ↦ sq_nonneg _))).mpr
  linarith

lemma IsDiffusion.L1_terminal {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    Tendsto (fun t ↦ ∫ ω, |X t ω-X 1 ω| ∂W.μ) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  apply squeeze_zero' (Eventually.of_forall (fun t ↦ integral_nonneg (fun _ ↦ abs_nonneg _))) ?_
    (by simpa only [Real.sqrt_zero,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hX.L2_terminal)
  filter_upwards [eventually_time_mem] with t ht
  exact integral_abs_le_sqrt_second ((hX.memLp ht (by norm_num)).sub
    (hX.memLp (by norm_num : (1 : ℝ)∈Icc (0 : ℝ) 1) (by norm_num)))

lemma IsDiffusion.phi_integrable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    Integrable (fun ω ↦ phi W γ t (X t ω)) W.μ := by
  have hi := (hX.memLp ht (p := 1) (by norm_num)).integrable le_rfl
  apply (hi.abs.add (integrable_const (terminalError γ t))).mono'
    (((phi_lipschitz W γ ht).continuous.measurable.comp (hX.measurable ht)).aestronglyMeasurable)
  filter_upwards [] with ω
  dsimp only [Function.comp_apply,Pi.add_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg ((abs_nonneg _).trans (phi_lower W γ ht (X t ω)))]
  have h := (phi_terminal_bound W γ ht (X t ω)).2
  change _≤terminalError γ t at h
  linarith

lemma IsDiffusion.phi_expectation_terminal {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    Tendsto (fun t ↦ ∫ ω, phi W γ t (X t ω) ∂W.μ) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ ω, |X 1 ω| ∂W.μ)) := by
  have h1 : Integrable (X 1) W.μ := (hX.memLp (by norm_num) (p := 1) (by norm_num)).integrable le_rfl
  have hb : ∀ t∈Icc (0 : ℝ) 1,
      |(∫ ω, phi W γ t (X t ω) ∂W.μ)-(∫ ω, |X 1 ω| ∂W.μ)|≤
      terminalError γ t+(∫ ω, |X t ω-X 1 ω| ∂W.μ) := by
    intro t ht
    have hp := hX.phi_integrable ht
    have hi : Integrable (X t) W.μ := (hX.memLp ht (p := 1) (by norm_num)).integrable le_rfl
    have hdiff : Integrable (fun ω ↦ |X t ω-X 1 ω|) W.μ := (hi.sub h1).abs
    calc
      _ = |∫ ω, (phi W γ t (X t ω)-|X 1 ω|) ∂W.μ| := by rw [integral_sub hp h1.abs]
      _ ≤ ∫ ω, |phi W γ t (X t ω)-(|X 1 ω|)| ∂W.μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, terminalError γ t+|X t ω-X 1 ω| ∂W.μ := by
        apply integral_mono (hp.sub h1.abs).abs ((integrable_const _).add (hi.sub h1).abs)
        intro ω
        dsimp only [Pi.add_apply,Pi.sub_apply]
        have hphi := phi_terminal_bound W γ ht (X t ω)
        have hz : |phi W γ t (X t ω)-(|X t ω|)|≤terminalError γ t := by
          rw [abs_of_nonneg hphi.1]
          exact hphi.2
        have he : phi W γ t (X t ω)-|X 1 ω| =
            (phi W γ t (X t ω)-|X t ω|)+(|X t ω|-|X 1 ω|) := by ring
        rw [he]
        exact (abs_add_le _ _).trans (add_le_add hz (abs_abs_sub_abs_le_abs_sub _ _))
      _ = _ := by
        rw [integral_add (integrable_const (terminalError γ t)) hdiff, integral_const]
        simp
  have he : Tendsto (fun t ↦ terminalError γ t) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [terminalError_one] using ((terminalError_continuous γ).tendsto 1).mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun t ↦ |(∫ ω, phi W γ t (X t ω) ∂W.μ)-(∫ ω, |X 1 ω| ∂W.μ)|)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _))
      (eventually_time_mem.mono (fun t ht ↦ hb t ht)) (by simpa only [add_zero] using he.add hX.L1_terminal)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hh)

lemma IsDiffusion.terminal_gradient_product {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {U : W.Ω → ℝ}
    (hd : ∀ᵐ ω ∂W.μ, ∀ᶠ t in 𝓝[<] (1 : ℝ), DifferentiableAt ℝ (phi W γ t) (X t ω))
    (hU : ∀ᵐ ω ∂W.μ, Tendsto (fun t ↦ gradient W γ t (X t ω)) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) :
    ∀ᵐ ω ∂W.μ, U ω*X 1 ω=|X 1 ω| := by
  filter_upwards [hX.ae_tendsto,hd,hU] with ω hXω hdω hUω
  by_cases hz : X 1 ω=0
  · simp [hz]
  have hs := gradient_terminal_tendsto W γ id (fun t ↦ X t ω)
    (tendsto_id.mono_left nhdsWithin_le_nhds) eventually_time_mem hXω hz hdω
  have hu : U ω=Real.sign (X 1 ω) := tendsto_nhds_unique hUω hs
  rw [hu]
  rcases lt_or_gt_of_ne hz with hn | hp
  · simp [Real.sign_of_neg hn,abs_of_neg hn]
  · simp [Real.sign_of_pos hp,abs_of_pos hp]

end SKValue

end

end OAI
