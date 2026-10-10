import OAI.MathematicalPhysics.Boltzmann.Branching.FiveGainPullback
import OAI.MathematicalPhysics.Boltzmann.Branching.RescaledParameterSlab
import OAI.MathematicalPhysics.Boltzmann.Branching.StageParameterIntegration
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteParameterChain
import OAI.MathematicalPhysics.Boltzmann.Jets.CoreJointParameterDensity

namespace OAI

section

/-! # The actual positive core step in thermal collision coordinates -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.FiveGainMap

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem flight_toKinetic (z : State) (t : ℝ) :
    PositiveIteration.flight (toKinetic z) t =
      toKinetic (t,z.2.1-(z.1-t) • z.2.2,z.2.2) := rfl

theorem toKinetic_thermalStep (α γ μ d t : ℝ) (color : Bool) (w L : V) (z : State) :
    toKinetic (thermalStep (JetPrototype.sign color) α γ μ d t L w z) =
      ((t,WithLp.toLp 2 (z.2.1-(z.1-t) • z.2.2)),
        parameterPoint α γ μ d t color (jetPosition (z.2.1-(z.1-t) • z.2.2))
          (WithLp.toLp 2 z.2.2) w L) := by
  rw [thermalStep_eq_parameterPoint]
  rfl

theorem dilatedFreeKernel_parameter_integral {r α γ μ d : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hd : 0 < d)
    (η K q : ℝ) (color : Bool) (z : State) (ht : 0 ≤ z.1)
    (hv : transverse (WithLp.toLp 2 z.2.2) ≠ 0)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂dilatedFreeKernel r η K α γ (r*μ) d q color (toKinetic z)) =
      ∫⁻ w : V, ∫⁻ L : V,
        rescaledParameterDensity r η K α γ μ d z.1 q color
          (jetPosition z.2.1) (WithLp.toLp 2 z.2.2) w L *
          f (parameterPoint α γ μ d z.1 color (jetPosition z.2.1)
            (WithLp.toLp 2 z.2.2) w L) := by
  rw [dilatedFreeKernel_eq_rescaled hr]
  have hdiv : r*μ/r = μ := by field_simp
  rw [hdiv]
  exact rescaledCoreMeasure_parameter_integral hr hα hγ hμ hd ht η K q color
    (jetPosition z.2.1) (WithLp.toLp 2 z.2.2) hv hf

theorem step_thermal_core {r α γ μ d a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hd : 0 < d) (ha : 0 ≤ a)
    (η K q : ℝ) (color : Bool) (z : State)
    (hv : transverse (WithLp.toLp 2 z.2.2) ≠ 0)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    PositiveIteration.step a (dilatedFreeKernel r η K α γ (r*μ) d q color) f (toKinetic z) =
      ∫⁻ t in Ioc a z.1, ∫⁻ w : V, ∫⁻ L : V,
        rescaledParameterDensity r η K α γ μ d t q color
          (jetPosition (z.2.1-(z.1-t) • z.2.2)) (WithLp.toLp 2 z.2.2) w L *
          f (toKinetic (thermalStep (JetPrototype.sign color) α γ μ d t L w z)) := by
  unfold PositiveIteration.step
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [flight_toKinetic]
  have he := dilatedFreeKernel_parameter_integral hr hα hγ hμ hd η K q color
    (t,z.2.1-(z.1-t) • z.2.2,z.2.2) (ha.trans ht.1.le) hv
    (f := fun ξ => f ((t,WithLp.toLp 2 (z.2.1-(z.1-t) • z.2.2)),ξ))
    (hf.comp (measurable_const.prodMk measurable_id))
  refine he.trans ?_
  apply lintegral_congr
  intro w
  apply lintegral_congr
  intro L
  rw [toKinetic_thermalStep]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Measurable time and collision parameters for one actual positive core gain -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

def stageArguments (z : State) (p : StageControls) : ParameterArguments :=
  ((p.1.1,jetPosition (z.2.1-(z.1-max 0 p.1.1) • z.2.2)),
    (WithLp.toLp 2 z.2.2,(p.2,p.1.2)))

def coreNext (α γ μ d : ℝ) (color : Bool) (z : State) (p : StageControls) : State :=
  (max 0 p.1.1,z.2.1-(z.1-max 0 p.1.1) • z.2.2,
    WithLp.ofLp (parameterPoint α γ μ d (max 0 p.1.1) color
      (stageArguments z p).1.2 (stageArguments z p).2.1 p.2 p.1.2))

def validStage (a : ℝ) : Set (State × StageControls) :=
  {p | a < p.2.1.1 ∧ p.2.1.1 ≤ p.1.1 ∧ transverse (WithLp.toLp 2 p.1.2.2) ≠ 0}

def coreDensity (r η K α γ μ d q a : ℝ) (color : Bool)
    (z : State) (p : StageControls) : ℝ≥0∞ :=
  (validStage a).indicator (fun u : State × StageControls =>
    rescaledParameterDensity r η K α γ μ d (max 0 u.2.1.1) q color
      (stageArguments u.1 u.2).1.2 (stageArguments u.1 u.2).2.1 u.2.2 u.2.1.2) (z,p)

theorem stageArguments_measurable :
    Measurable (fun p : State × StageControls => stageArguments p.1 p.2) := by
  unfold stageArguments jetPosition transverse
  fun_prop

theorem validStage_measurable (a : ℝ) : MeasurableSet (validStage a) := by
  have h₁ : MeasurableSet {p : State × StageControls | a < p.2.1.1} :=
    measurableSet_lt measurable_const (by fun_prop)
  have h₂ : MeasurableSet {p : State × StageControls | p.2.1.1 ≤ p.1.1} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have h₃ : MeasurableSet {p : State × StageControls |
      transverse (WithLp.toLp 2 p.1.2.2) ≠ 0} :=
    (measurableSet_eq_fun (by unfold transverse; fun_prop) measurable_const).compl
  exact h₁.inter (h₂.inter h₃)

theorem coreNext_measurable {α γ μ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ)
    (d : ℝ) (color : Bool) :
    Measurable (fun p : State × StageControls => coreNext α γ μ d color p.1 p.2) := by
  have hp := (clamped_parameterPoint_measurable hα hγ hμ d color).comp stageArguments_measurable
  have hv : Measurable (fun p : State × StageControls =>
      WithLp.ofLp (parameterPoint α γ μ d (max 0 p.2.1.1) color
        (stageArguments p.1 p.2).1.2 (stageArguments p.1 p.2).2.1 p.2.2 p.2.1.2)) :=
    (MeasurableEquiv.toLp 2 V).symm.measurable.comp hp
  exact (by fun_prop : Measurable (fun p : State × StageControls => max 0 p.2.1.1)).prodMk
    ((by fun_prop : Measurable (fun p : State × StageControls =>
      p.1.2.1-(p.1.1-max 0 p.2.1.1) • p.1.2.2)).prodMk hv)

theorem coreDensity_measurable {r α γ μ : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (η K d q a : ℝ) (color : Bool) :
    Measurable (fun p : State × StageControls => coreDensity r η K α γ μ d q a color p.1 p.2) :=
  ((clamped_rescaledParameterDensity_measurable hr hα hγ hμ η K d q color).comp
    stageArguments_measurable).indicator (validStage_measurable a)

theorem coreNext_eq_thermalStep {α γ μ d : ℝ} (color : Bool) (z : State)
    (p : StageControls) (ht : 0 ≤ p.1.1) :
    coreNext α γ μ d color z p =
      thermalStep (JetPrototype.sign color) α γ μ d p.1.1 p.1.2 p.2 z := by
  rw [thermalStep_eq_parameterPoint]
  unfold coreNext stageArguments
  rw [max_eq_right ht]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Exact identification of the positive physical step with a parameter block -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem coreDensity_ne_top (r η K α γ μ d q a : ℝ) (color : Bool)
    (z : State) (p : StageControls) : coreDensity r η K α γ μ d q a color z p ≠ ∞ := by
  unfold coreDensity
  by_cases h : (z,p) ∈ validStage a
  · rw [indicator_of_mem h]
    unfold rescaledParameterDensity parameterDensity
    have hn (x : ℝ) : RedundantPlane.normalDensity x ≠ ∞ :=
      ne_top_of_le_ne_top (by norm_num) (RedundantPlane.normalDensity_le_one x)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) (hn _)) ENNReal.ofReal_ne_top)
  · rw [indicator_of_notMem h]
    exact ENNReal.zero_ne_top

theorem step_eq_parameter_block {r α γ μ d a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hd : 0 < d) (ha : 0 ≤ a)
    (η K q : ℝ) (color : Bool) (z : State)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    PositiveIteration.step a (dilatedFreeKernel r η K α γ (r*μ) d q color) f (toKinetic z) =
      ∫⁻ p : StageControls, coreDensity r η K α γ μ d q a color z p *
        f (toKinetic (coreNext α γ μ d color z p)) := by
  have hD : Measurable (fun p : StageControls => coreDensity r η K α γ μ d q a color z p) :=
    (coreDensity_measurable hr hα hγ hμ η K d q a color).comp measurable_prodMk_left
  have hN : Measurable (fun p : StageControls => coreNext α γ μ d color z p) :=
    (coreNext_measurable hα hγ hμ d color).comp measurable_prodMk_left
  have hF : Measurable (fun p : StageControls => coreDensity r η K α γ μ d q a color z p *
      f (toKinetic (coreNext α γ μ d color z p))) :=
    hD.mul (hf.comp (toKinetic.measurable.comp hN))
  by_cases hv : transverse (WithLp.toLp 2 z.2.2) = 0
  · have hzero (p : StageControls) : coreDensity r η K α γ μ d q a color z p = 0 := by
      apply indicator_of_notMem
      intro h
      exact h.2.2 hv
    have hkernel (t : ℝ) :
        dilatedFreeKernel r η K α γ (r*μ) d q color (PositiveIteration.flight (toKinetic z) t) = 0 := by
      apply ChartKernel.offAxis_axis
      exact hv
    simp only [PositiveIteration.step,hkernel,lintegral_zero_measure,lintegral_zero,hzero,zero_mul]
  · rw [step_thermal_core hr hα hγ hμ hd ha η K q color z hv hf,lintegral_stage hF]
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ Ioc a z.1
    · rw [indicator_of_mem ht]
      apply lintegral_congr
      intro w
      apply lintegral_congr
      intro L
      have hvalid : (z,((t,L),w)) ∈ validStage a := ⟨ht.1,ht.2,hv⟩
      rw [coreDensity,indicator_of_mem hvalid,coreNext_eq_thermalStep color z _ (ha.trans ht.1.le)]
      dsimp only [stageArguments]
      rw [max_eq_right (ha.trans ht.1.le)]
    · rw [indicator_of_notMem ht]
      symm
      have hz (w L : FiveGainMap.V) :
          coreDensity r η K α γ μ d q a color z ((t,L),w) = 0 := by
        apply indicator_of_notMem
        intro h
        exact ht ⟨h.1,h.2.1⟩
      simp only [hz,zero_mul,lintegral_zero]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Exact finite-chain parameter formula for the physical dilated core kernels -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap

namespace BoltzmannNonuniqueness.JetCoreSheet

def actualCoreChain (r η K α γ q a : ℝ) (μ d : ℕ → ℝ) (colors : ℕ → Bool)
    (f : Published.KineticPhase → ℝ≥0∞) (i : ℕ) : ℕ → Published.KineticPhase → ℝ≥0∞
  | 0 => f
  | n+1 => PositiveIteration.step a (dilatedFreeKernel r η K α γ (r*μ i) (d i) q (colors i))
      (actualCoreChain r η K α γ q a μ d colors f (i+1) n)

theorem actualCoreChain_measurable (r η K α γ q a : ℝ) (μ d : ℕ → ℝ) (colors : ℕ → Bool)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) :
    Measurable (actualCoreChain r η K α γ q a μ d colors f i n) := by
  induction n generalizing i with
  | zero => exact hf
  | succ n ih => exact PositiveIteration.step_measurable a _ (ih (i+1))

theorem actualCoreChain_eq_parameters {r α γ a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 ≤ a) (η K q : ℝ)
    (μ d : ℕ → ℝ) (colors : ℕ → Bool) (hμ : ∀ i, 0 < μ i) (hd : ∀ i, 0 < d i)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) (z : State) :
    actualCoreChain r η K α γ q a μ d colors f i n (toKinetic z) =
      parameterChain (fun i => coreNext α γ (μ i) (d i) (colors i))
        (fun i => coreDensity r η K α γ (μ i) (d i) q a (colors i))
        (fun z => f (toKinetic z)) i n z := by
  induction n generalizing i z with
  | zero => rfl
  | succ n ih =>
    change PositiveIteration.step a _ _ (toKinetic z) = _
    rw [step_eq_parameter_block hr hα hγ (hμ i) (hd i) ha η K q (colors i) z
      (actualCoreChain_measurable r η K α γ q a μ d colors hf (i+1) n)]
    simp only [parameterChain]
    apply lintegral_congr
    intro p
    rw [ih]

theorem actualCoreChain_product_integral {r α γ a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 ≤ a) (η K q : ℝ)
    (μ d : ℕ → ℝ) (colors : ℕ → Bool) (hμ : ∀ i, 0 < μ i) (hd : ∀ i, 0 < d i)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) (z : State) :
    actualCoreChain r η K α γ q a μ d colors f i n (toKinetic z) =
      ∫⁻ p : Fin n → StageControls,
        chainIntegrand (fun i => coreNext α γ (μ i) (d i) (colors i))
          (fun i => coreDensity r η K α γ (μ i) (d i) q a (colors i))
          (fun z => f (toKinetic z)) i n z p := by
  rw [actualCoreChain_eq_parameters hr hα hγ ha η K q μ d colors hμ hd hf]
  exact parameterChain_eq_product _ _
    (fun i => coreNext_measurable hα hγ (hμ i) (d i) (colors i))
    (fun i => coreDensity_measurable hr hα hγ (hμ i) η K (d i) q a (colors i))
    (fun i => coreDensity_ne_top r η K α γ (μ i) (d i) q a (colors i))
    (hf.comp toKinetic.measurable) i n z

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
