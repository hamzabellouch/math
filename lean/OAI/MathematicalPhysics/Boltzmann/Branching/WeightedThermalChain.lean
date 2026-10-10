import OAI.MathematicalPhysics.Boltzmann.Branching.ControlledParameterPath
import OAI.MathematicalPhysics.Boltzmann.Branching.SupportedTensorConvergence
import OAI.MathematicalPhysics.Boltzmann.Jets.ThermalParameterChain

namespace OAI

section

/-! # Multiplicative state restrictions along a finite collision path -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

def statePathWeight (next : ℕ → State → StageControls → State)
    (weight : ℕ → State → ℝ≥0∞) (controls : ℕ → StageControls)
    (i n : ℕ) (z : State) : ℝ≥0∞ :=
  ∏ j : Fin n, weight (i+j.val) (controlledPath next controls i z (j.val+1))

theorem statePathWeight_le_one (next : ℕ → State → StageControls → State)
    (weight : ℕ → State → ℝ≥0∞) (hw : ∀ i z, weight i z ≤ 1)
    (controls : ℕ → StageControls) (i n : ℕ) (z : State) :
    statePathWeight next weight controls i n z ≤ 1 :=
  Finset.prod_le_one (fun j _ => hw (i+j.val) _)

attribute [local irreducible] controlledPath

theorem chainIntegrand_weighted (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞)
    (weight : ℕ → State → ℝ≥0∞) (g : State → ℝ≥0∞)
    (controls : ℕ → StageControls) (i n : ℕ) (z : State) :
    chainIntegrand next (fun i z p => density i z p*weight i (next i z p)) g i n z
        (fun j => controls (i+j.val)) =
      statePathWeight next weight controls i n z *
        chainIntegrand next density g i n z (fun j => controls (i+j.val)) := by
  rw [chainIntegrand_eq_pathProduct,chainIntegrand_eq_pathProduct]
  have hstep (j : Fin n) :
      next (i+j.val) (controlledPath next controls i z j.val) (controls (i+j.val)) =
        controlledPath next controls i z (j.val+1) := by
    rw [controlledPath]
  simp only [hstep,Finset.prod_mul_distrib,statePathWeight]
  ring

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Compact velocity-pair tests with a bounded space-time multiplier -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

variable {X Y Z : Type*} [MeasurableSpace X] [MetricSpace Y] [MetricSpace Z]
  [SecondCountableTopology Z]
  [MeasurableSpace Y] [MeasurableSpace Z] [BorelSpace Y] [BorelSpace Z]

private theorem weighted_test_integrable (μ : Measure (X × (Y × Z))) [IsFiniteMeasure μ]
    {θ : X → ℝ} (hθ : Measurable θ) {B : ℝ} (hB : ∀ x, |θ x| ≤ B)
    (f : C(Y × Z, ℝ)) (hf : HasCompactSupport f) :
    Integrable (fun p => θ p.1*f p.2) μ := by
  obtain ⟨C,hC⟩ := f.continuous.bounded_above_of_compact_support hf
  apply Integrable.of_bound
    ((hθ.comp measurable_fst).mul (f.continuous.measurable.comp measurable_snd)).aestronglyMeasurable (|B| *|C|)
  exact ae_of_all _ (fun p => by
    change ‖θ p.1*f p.2‖ ≤ |B| * |C|
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul ((hB _).trans (le_abs_self B)) ((hC _).trans (le_abs_self C))
      (abs_nonneg _) (abs_nonneg _))

private theorem weighted_integral_error (μ : Measure (X × (Y × Z))) [IsFiniteMeasure μ]
    {θ : X → ℝ} (hθ : Measurable θ) {B : ℝ} (hB : ∀ x, |θ x| ≤ B)
    (f g : C(Y × Z, ℝ)) (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    {δ : ℝ} (hδ : ∀ p, |f p-g p| ≤ δ) :
    |(∫ p, θ p.1*f p.2 ∂μ)-(∫ p, θ p.1*g p.2 ∂μ)| ≤ (|B| *δ)*μ.real univ := by
  rw [← integral_sub (weighted_test_integrable μ hθ hB f hf)
    (weighted_test_integrable μ hθ hB g hg),← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  exact ae_of_all _ (fun p => by
    rw [← mul_sub,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul ((hB _).trans (le_abs_self B)) (hδ _) (abs_nonneg _) (abs_nonneg _))

theorem weighted_supported_integral_tendsto_of_tensor_tests
    [LocallyCompactSpace Y] [LocallyCompactSpace Z]
    {μ : ℕ → Measure (X × (Y × Z))} {ν : Measure (X × (Y × Z))}
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    {θ : X → ℝ} (hθ : Measurable θ) {B : ℝ} (hB : ∀ x, |θ x| ≤ B)
    {C : ℝ} (hC : 0 ≤ C) (hμ : ∀ᶠ n in atTop, (μ n).real univ ≤ C)
    (h : ∀ f : C(Y, ℝ), ∀ g : C(Z, ℝ), HasCompactSupport f → HasCompactSupport g →
      Tendsto (fun n => ∫ p, θ p.1*(f p.2.1*g p.2.2) ∂μ n) atTop
        (𝓝 (∫ p, θ p.1*(f p.2.1*g p.2.2) ∂ν)))
    (f : C(Y × Z, ℝ)) (hf : HasCompactSupport f) :
    Tendsto (fun n => ∫ p, θ p.1*f p.2 ∂μ n) atTop (𝓝 (∫ p, θ p.1*f p.2 ∂ν)) := by
  have hsum : ∀ g : C(Y × Z, ℝ), IsSupportedTensorSum g →
      Tendsto (fun n => ∫ p, θ p.1*g p.2 ∂μ n) atTop (𝓝 (∫ p, θ p.1*g p.2 ∂ν)) := by
    intro g hg
    induction hg with
    | zero => simpa only [ContinuousMap.zero_apply,mul_zero,integral_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    | tensor g k hg hk => exact h g k hg hk
    | @add g k hg hk ihg ihk =>
      simpa only [ContinuousMap.add_apply,mul_add,
        integral_add (weighted_test_integrable _ hθ hB g hg.hasCompactSupport)
          (weighted_test_integrable _ hθ hB k hk.hasCompactSupport)] using ihg.add ihk
    | @smul r g hg ih =>
      have he (p : X × (Y × Z)) : θ p.1*((r • g) p.2) = r*(θ p.1*g p.2) := by
        simp only [ContinuousMap.smul_apply,smul_eq_mul]
        ring
      simpa only [he,integral_const_mul] using ih.const_mul r
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let D := ν.real univ
  have hD : 0 ≤ D := measureReal_nonneg
  let δ := ε/(3*(|B| *(C+D)+1))
  have hden : 0 < 3*(|B| *(C+D)+1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have he : δ*(3*(|B| *(C+D)+1)) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨g,hg,hfg⟩ := exists_supported_tensorSum_uniform f hf hδ
  have hmid := Metric.tendsto_nhds.mp (hsum g hg) (ε/3) (by positivity)
  filter_upwards [hμ,hmid] with n hn hgn
  rw [Real.dist_eq] at hgn ⊢
  have hleft := (weighted_integral_error (μ n) hθ hB f g hf hg.hasCompactSupport
    (fun p => by rw [abs_sub_comm]; exact (hfg p).le)).trans
      (mul_le_mul_of_nonneg_left hn (mul_nonneg (abs_nonneg _) hδ.le))
  have hright := weighted_integral_error ν hθ hB g f hg.hasCompactSupport hf
    (fun p => (hfg p).le)
  have ht₁ := abs_sub_le (∫ p, θ p.1*f p.2 ∂μ n) (∫ p, θ p.1*g p.2 ∂μ n)
    (∫ p, θ p.1*f p.2 ∂ν)
  have ht₂ := abs_sub_le (∫ p, θ p.1*g p.2 ∂μ n) (∫ p, θ p.1*g p.2 ∂ν)
    (∫ p, θ p.1*f p.2 ∂ν)
  change |(∫ p, θ p.1*g p.2 ∂ν)-(∫ p, θ p.1*f p.2 ∂ν)| ≤ (|B| *δ)*D at hright
  nlinarith

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Actual physical core chains with spatial and velocity restrictions -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap

namespace BoltzmannNonuniqueness.JetCoreSheet

def weightedCoreChain (r η K α γ q a : ℝ) (μ d : ℕ → ℝ) (colors : ℕ → Bool)
    (weight : ℕ → Published.KineticPhase → ℝ≥0∞)
    (f : Published.KineticPhase → ℝ≥0∞) (i : ℕ) : ℕ → Published.KineticPhase → ℝ≥0∞
  | 0 => f
  | n+1 => PositiveIteration.step a (dilatedFreeKernel r η K α γ (r*μ i) (d i) q (colors i))
      (fun z => weight i z * weightedCoreChain r η K α γ q a μ d colors weight f (i+1) n z)

theorem weightedCoreChain_measurable (r η K α γ q a : ℝ) (μ d : ℕ → ℝ) (colors : ℕ → Bool)
    {weight : ℕ → Published.KineticPhase → ℝ≥0∞} (hw : ∀ i, Measurable (weight i))
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) :
    Measurable (weightedCoreChain r η K α γ q a μ d colors weight f i n) := by
  induction n generalizing i with
  | zero => exact hf
  | succ n ih => exact PositiveIteration.step_measurable a _ ((hw i).mul (ih (i+1)))

theorem weightedCoreChain_eq_parameters {r α γ a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 ≤ a) (η K q : ℝ)
    (μ d : ℕ → ℝ) (colors : ℕ → Bool) (hμ : ∀ i, 0 < μ i) (hd : ∀ i, 0 < d i)
    {weight : ℕ → Published.KineticPhase → ℝ≥0∞} (hw : ∀ i, Measurable (weight i))
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) (z : State) :
    weightedCoreChain r η K α γ q a μ d colors weight f i n (toKinetic z) =
      parameterChain (fun i => coreNext α γ (μ i) (d i) (colors i))
        (fun i z p => coreDensity r η K α γ (μ i) (d i) q a (colors i) z p *
          weight i (toKinetic (coreNext α γ (μ i) (d i) (colors i) z p)))
        (fun z => f (toKinetic z)) i n z := by
  induction n generalizing i z with
  | zero => rfl
  | succ n ih =>
    change PositiveIteration.step a _ _ (toKinetic z) = _
    rw [step_eq_parameter_block (f := fun y => weight i y *
      weightedCoreChain r η K α γ q a μ d colors weight f (i+1) n y)
      hr hα hγ (hμ i) (hd i) ha η K q (colors i) z
      ((hw i).mul (weightedCoreChain_measurable r η K α γ q a μ d colors hw hf (i+1) n))]
    simp only [parameterChain]
    apply lintegral_congr
    intro p
    rw [ih,mul_assoc]

theorem weightedCoreChain_product_integral {r α γ a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 ≤ a) (η K q : ℝ)
    (μ d : ℕ → ℝ) (colors : ℕ → Bool) (hμ : ∀ i, 0 < μ i) (hd : ∀ i, 0 < d i)
    {weight : ℕ → Published.KineticPhase → ℝ≥0∞} (hw : ∀ i, Measurable (weight i))
    (hwfin : ∀ i z, weight i z ≠ ∞)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) (z : State) :
    weightedCoreChain r η K α γ q a μ d colors weight f i n (toKinetic z) =
      ∫⁻ p : Fin n → StageControls,
        chainIntegrand (fun i => coreNext α γ (μ i) (d i) (colors i))
          (fun i z p => coreDensity r η K α γ (μ i) (d i) q a (colors i) z p *
            weight i (toKinetic (coreNext α γ (μ i) (d i) (colors i) z p)))
          (fun z => f (toKinetic z)) i n z p := by
  rw [weightedCoreChain_eq_parameters hr hα hγ ha η K q μ d colors hμ hd hw hf]
  apply parameterChain_eq_product
  · exact fun i => coreNext_measurable hα hγ (hμ i) (d i) (colors i)
  · intro i
    exact (coreDensity_measurable hr hα hγ (hμ i) η K (d i) q a (colors i)).mul
      ((hw i).comp (toKinetic.measurable.comp (coreNext_measurable hα hγ (hμ i) (d i) (colors i))))
  · exact fun i z p => ENNReal.mul_ne_top
      (coreDensity_ne_top r η K α γ (μ i) (d i) q a (colors i) z p) (hwfin i _)
  · exact hf.comp toKinetic.measurable

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
