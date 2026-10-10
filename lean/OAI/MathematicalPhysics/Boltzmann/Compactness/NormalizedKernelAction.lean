import OAI.MathematicalPhysics.Boltzmann.Branching.AverageMajorant
import OAI.MathematicalPhysics.Boltzmann.Branching.ChartPointLift
import OAI.MathematicalPhysics.Boltzmann.Branching.HotQuadraticGain
import OAI.MathematicalPhysics.Boltzmann.Branching.NonnegativeGainCongruence
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.Probability.Kernel.MeasurableLIntegral

namespace OAI

section

/-! # The normalized Carleman gain as a measurable velocity kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

def coordinateKernel (c : Kernel X Velocity) (q : ℝ) : Kernel (X × Velocity) Coordinates :=
  ((c.comap Prod.fst measurable_fst) ×ₖ
    Kernel.const (X × Velocity) ((volume : Measure ℝ).prod volume)).withDensity
      (fun z y => density (fun ξ => ENNReal.ofReal (H q ξ/H q z.2)) z.2 y)

instance coordinateKernel_sFinite (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) :
    IsSFiniteKernel (coordinateKernel c q) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => by
    unfold density
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top)

theorem coordinateKernel_apply (c : Kernel X Velocity) [IsSFiniteKernel c]
    (q : ℝ) (z : X × Velocity) :
    coordinateKernel c q z = normalizedMeasure (c z.1) q z.2 := by
  rw [coordinateKernel,Kernel.withDensity_apply _ (measurable_lifted_density q),Kernel.prod_apply]
  rfl

def inputMeasure (c : Kernel X Velocity) (q : ℝ) (z : X × Velocity) : Measure Velocity :=
  (coordinateKernel c q z).map (fun y => PlaneChart.chart z.2 y.1 y.2.1 y.2.2)

theorem inputMeasure_measurable (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) :
    Measurable (inputMeasure c q) := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hi := (((measurable_const : Measurable (fun _ : Velocity => (1 : ℝ≥0∞))).indicator hs).comp
      (measurable_lifted_point (X := X))).lintegral_kernel_prod_right'
      (κ := coordinateKernel c q)
    convert hi using 1
    funext z
    unfold inputMeasure
    rw [Measure.map_apply (measurable_point z.2) hs]
    dsimp only [Function.comp_def]
    change _ = ∫⁻ y, ((fun y : Coordinates =>
      PlaneChart.chart z.2 y.1 y.2.1 y.2.2) ⁻¹' s).indicator
      (fun _ => (1 : ℝ≥0∞)) y ∂coordinateKernel c q z
    simpa only [one_mul] using
      (lintegral_indicator_const (μ := coordinateKernel c q z)
        (hs.preimage (measurable_point z.2)) (1 : ℝ≥0∞)).symm

def inputKernel (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) :
    Kernel (X × Velocity) Velocity where
  toFun := inputMeasure c q
  measurable' := inputMeasure_measurable c q

theorem inputKernel_mass (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) (z : X × Velocity) :
    inputKernel c q z univ = normalizedChartGain (c z.1) q z.2 := by
  change ((coordinateKernel c q z).map (fun y => PlaneChart.chart z.2 y.1 y.2.1 y.2.2)) univ = _
  rw [Measure.map_apply (measurable_point z.2) MeasurableSet.univ]
  simp only [preimage_univ,coordinateKernel_apply,normalized_total_eq]

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # S-finiteness and integration for the normalized gain input kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

theorem inputKernel_eq_map (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) :
    inputKernel c q = (Kernel.id ×ₖ coordinateKernel c q).map
      (fun p : (X × Velocity) × Coordinates =>
        PlaneChart.chart p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  apply Kernel.ext
  intro z
  rw [Kernel.map_apply _ (measurable_lifted_point (X := X)),Kernel.prod_apply,
    Kernel.id_apply,Measure.dirac_prod,
    Measure.map_map (measurable_lifted_point (X := X)) measurable_prodMk_left]
  rfl

instance inputKernel_sFinite (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) :
    IsSFiniteKernel (inputKernel c q) := by
  rw [inputKernel_eq_map]
  infer_instance

theorem lintegral_inputKernel (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ)
    (z : X × Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ v, f v ∂inputKernel c q z) =
      ∫⁻ y, f (PlaneChart.chart z.2 y.1 y.2.1 y.2.2)
        ∂normalizedMeasure (c z.1) q z.2 := by
  change (∫⁻ v, f v ∂(coordinateKernel c q z).map
    (fun y => PlaneChart.chart z.2 y.1 y.2.1 y.2.2)) = _
  rw [lintegral_map hf (measurable_point z.2),coordinateKernel_apply]

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Integrating an input against the normalized collision kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

theorem measure_weighted (c : Measure Velocity) {h f : Velocity → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) (v : Velocity) :
    (measure c h v).withDensity (fun y => f (PlaneChart.chart v y.1 y.2.1 y.2.2)) =
      measure c (fun ξ => h ξ*f ξ) v := by
  have ht : Measurable (fun y : Coordinates => f (PlaneChart.chart v y.1 y.2.1 y.2.2)) :=
    hf.comp (measurable_point v)
  rw [measure,← withDensity_mul _ (measurable_density hh v) ht]
  congr 1
  funext y
  unfold density
  exact mul_assoc _ _ _

theorem lintegral_normalized (c : Measure Velocity) (q : ℝ) (v : Velocity)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f (PlaneChart.chart v y.1 y.2.1 y.2.2) ∂normalizedMeasure c q v) =
      chartGain c (fun ξ => ENNReal.ofReal (H q ξ/H q v)*f ξ) v := by
  have hh := ((measurable_H q).div_const (H q v)).ennreal_ofReal
  calc
    _ = ((measure c (fun ξ => ENNReal.ofReal (H q ξ/H q v)) v).withDensity
        (fun y => f (PlaneChart.chart v y.1 y.2.1 y.2.2))) univ := by
      rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      rfl
    _ = (measure c (fun ξ => ENNReal.ofReal (H q ξ/H q v)*f ξ) v) univ :=
      congrArg (fun μ : Measure Coordinates => μ univ) (measure_weighted c hh hf v)
    _ = _ := (total_eq c (hh.mul hf) v).symm

theorem lintegral_inputKernel_eq_gain {X : Type*} [MeasurableSpace X]
    (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) (z : X × Velocity)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂inputKernel c q z) =
      chartGain (c z.1) (fun ξ => ENNReal.ofReal (H q ξ/H q z.2)*f ξ) z.2 := by
  rw [lintegral_inputKernel c q z hf,lintegral_normalized (c z.1) q z.2 hf]

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Collision identity and representative invariance of normalized gain -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem chartGain_const_mul_right (c : Measure Velocity) (a : ℝ≥0∞) (ha : a ≠ ∞)
    (h : Velocity → ℝ≥0∞) (v : Velocity) :
    chartGain c (fun ξ => a*h ξ) v = a*chartGain c h v := by
  unfold chartGain
  simp_rw [lintegral_const_mul' a _ ha,
    show ∀ p : Velocity,
      ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹)*
        (a*∫⁻ z : ℝ, ∫⁻ s : ℝ, h (PlaneChart.chart v p z s)) =
      a*(ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹)*
        ∫⁻ z : ℝ, ∫⁻ s : ℝ, h (PlaneChart.chart v p z s)) by intro p; ac_rfl]
  rw [lintegral_const_mul' a _ ha]
  ac_rfl

theorem normalized_integral_eq (c : Measure Velocity) (q : ℝ)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) (v : Velocity) :
    (∫⁻ y, f (PlaneChart.chart v y.1 y.2.1 y.2.2) ∂ChartKernel.normalizedMeasure c q v) =
      ENNReal.ofReal ((H q v)⁻¹)*
        chartGain c (fun ξ => ENNReal.ofReal (H q ξ)*f ξ) v := by
  rw [ChartKernel.lintegral_normalized c q v hf]
  have he : (fun ξ => ENNReal.ofReal (H q ξ/H q v)*f ξ) =
      fun ξ => ENNReal.ofReal ((H q v)⁻¹)*(ENNReal.ofReal (H q ξ)*f ξ) := by
    funext ξ
    rw [div_eq_mul_inv,ENNReal.ofReal_mul (H_nonneg q ξ)]
    ac_rfl
  rw [he,chartGain_const_mul_right c _ ENNReal.ofReal_ne_top]

theorem normalized_integral_congr_ae (hcarleman : Published.GPV2009CarlemanInput)
    {c f g : Velocity → ℝ≥0∞} (hc : Measurable c) (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[volume] g) (q : ℝ) :
    (fun v => ∫⁻ y, f (PlaneChart.chart v y.1 y.2.1 y.2.2)
      ∂ChartKernel.normalizedMeasure (volume.withDensity c) q v) =ᵐ[volume]
    (fun v => ∫⁻ y, g (PlaneChart.chart v y.1 y.2.1 y.2.2)
      ∂ChartKernel.normalizedMeasure (volume.withDensity c) q v) := by
  have hH := (ChartKernel.measurable_H q).ennreal_ofReal
  have he : (fun ξ => ENNReal.ofReal (H q ξ)*f ξ) =ᵐ[volume]
      (fun ξ => ENNReal.ofReal (H q ξ)*g ξ) :=
    hfg.mono (fun ξ hξ => congrArg (fun u => ENNReal.ofReal (H q ξ)*u) hξ)
  have hh := nonnegativeGain_congr_ae (Filter.EventuallyEq.refl _ c) he
  filter_upwards [hcarleman c _ hc (hH.mul hf),hcarleman c _ hc (hH.mul hg),hh] with v hcf hcg hfgv
  rw [normalized_integral_eq _ q hf v,normalized_integral_eq _ q hg v]
  exact congrArg (fun z => ENNReal.ofReal ((H q v)⁻¹)*z) (hcf.symm.trans (hfgv.trans hcg))

end BoltzmannNonuniqueness

end

end

section

/-! # Conditional tensor products controlled by a single mass marginal -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

def normalizedTensor (d : X → ℝ) (f g : X × Y → ℝ) (z : X × (Y × Y)) : ℝ :=
  f (z.1,z.2.1)*g (z.1,z.2.2)/(1+d z.1)

theorem normalizedTensor_measurable {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hf : Measurable f) (hg : Measurable g) :
    Measurable (normalizedTensor d f g) := by
  unfold normalizedTensor
  fun_prop

omit [MeasurableSpace X] in
theorem normalizedTensor_fiber_integral {d : X → ℝ} {f g : X × Y → ℝ} (x : X) :
    (∫ y, normalizedTensor d f g (x,y) ∂ν.prod ν) =
      (∫ v, f (x,v) ∂ν)*(∫ w, g (x,w) ∂ν)/(1+d x) := by
  simp only [normalizedTensor,integral_div]
  rw [integral_prod_mul (fun v => f (x,v)) (fun w => g (x,w))]

theorem normalizedTensor_integrable {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (hfi : Integrable f (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (hfd : ∀ᵐ x ∂μ, (∫ v, f (x,v) ∂ν) ≤ d x) :
    Integrable (normalizedTensor d f g) (μ.prod (ν.prod ν)) := by
  have hnon (z : X × (Y × Y)) : 0 ≤ normalizedTensor d f g z :=
    div_nonneg (mul_nonneg (hf _) (hg _)) (by linarith [hd0 z.1])
  have hnorm x : (∫ y, ‖normalizedTensor d f g (x,y)‖ ∂ν.prod ν) =
      (∫ v, f (x,v) ∂ν)*(∫ w, g (x,w) ∂ν)/(1+d x) := by
    simp only [Real.norm_of_nonneg (hnon _)]
    exact normalizedTensor_fiber_integral x
  apply (integrable_prod_iff (normalizedTensor_measurable hd hfm hgm).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hfi.prod_right_ae,hgi.prod_right_ae] with x hfx hgx
    exact (hfx.mul_prod hgx).div_const (1+d x)
  · apply hgi.integral_prod_left.mono'
      ((normalizedTensor_measurable hd hfm hgm).norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    filter_upwards [hfd] with x hx
    rw [hnorm,Real.norm_of_nonneg (div_nonneg
      (mul_nonneg (integral_nonneg (μ := ν) (f := fun v => f (x,v)) (fun v => hf (x,v))) (integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v))))
      (by linarith [hd0 x]))]
    apply (div_le_iff₀ (by linarith [hd0 x] : 0 < 1+d x)).mpr
    nlinarith [integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v)),
      mul_le_mul_of_nonneg_right hx (integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v)))]

theorem normalizedTensor_L1_le {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (hfi : Integrable f (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (hfd : ∀ᵐ x ∂μ, (∫ v, f (x,v) ∂ν) ≤ d x) :
    eLpNorm (normalizedTensor d f g) 1 (μ.prod (ν.prod ν)) ≤ eLpNorm g 1 (μ.prod ν) := by
  have ht := normalizedTensor_integrable hd hd0 hfm hgm hf hg hfi hgi hfd
  rw [eLpNorm_one_eq_lintegral_enorm ht.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm ht,
    eLpNorm_one_eq_lintegral_enorm hgi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hgi]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_prod _ ht.norm,integral_prod _ hgi.norm]
  apply integral_mono_ae ht.integral_norm_prod_left hgi.integral_norm_prod_left
  filter_upwards [hfd] with x hx
  have hgn := integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v))
  have hfn := integral_nonneg (μ := ν) (f := fun v => f (x,v)) (fun v => hf (x,v))
  have hn y : 0 ≤ normalizedTensor d f g (x,y) :=
    div_nonneg (mul_nonneg (hf _) (hg _)) (by linarith [hd0 x])
  simp only [Real.norm_of_nonneg (hn _),Real.norm_of_nonneg (hg _)]
  rw [normalizedTensor_fiber_integral]
  apply (div_le_iff₀ (by linarith [hd0 x] : 0 < 1+d x)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hx hgn]

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # The normalized gain of the fixed velocity weight -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

theorem normalized_weight_gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∀ᵐ v : Velocity, normalizedChartGain
      (volume.withDensity (fun p => ENNReal.ofReal (H q p))) q v ≤
        ENNReal.ofReal (HotApplication.realBound q) := by
  filter_upwards [hcarleman _ _ (measurable_H q).ennreal_ofReal (measurable_H q).ennreal_ofReal,
    HotApplication.quadratic_gain_le_constant hcarleman hq₁ hq₂] with v hc hb
  rw [hc,SheetApplication.gain_H_eq, mul_comm (HotApplication.realBound q),
    ENNReal.ofReal_mul (H_nonneg q v)] at hb
  exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr (H_pos q v))) ENNReal.ofReal_ne_top).mp hb

theorem normalized_weight_scaled_bound (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (a : ℝ≥0∞) :
    ∀ᵐ v : Velocity, normalizedChartGain
      (a • volume.withDensity (fun p => ENNReal.ofReal (H q p))) q v ≤
        a*ENNReal.ofReal (HotApplication.realBound q) := by
  filter_upwards [normalized_weight_gain_bound hcarleman hq₁ hq₂] with v hv
  change chartGain _ _ _ ≤ _
  rw [chartGain_smul_measure]
  exact mul_le_mul' le_rfl hv

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Products of velocity averages normalized by their mass density -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem tendstoInMeasure_continuous_comp {f : ℕ → X → ℝ} {g : X → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (h : TendstoInMeasure μ f atTop g) {P : ℝ → ℝ} (hP : Continuous P) :
    TendstoInMeasure μ (fun n x => P (f n x)) atTop (fun x => P (g x)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => hP.comp_aestronglyMeasurable (hfm n))).mpr
  intro ns hns
  obtain ⟨i,hi,hfi⟩ := (h.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨i,hi,?_⟩
  filter_upwards [hfi] with x hx
  exact hP.continuousAt.tendsto.comp hx

theorem normalized_product_bound {a b r C D : ℝ} (hr : 0 ≤ r)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : |a| ≤ C*r) (hb : |b| ≤ D*r) :
    |a*b/(1+|r|)| ≤ C*D*r := by
  rw [abs_div,abs_mul,abs_of_pos (by positivity : 0 < 1+|r|),abs_of_nonneg hr]
  apply (div_le_iff₀ (by positivity : 0 < 1+r)).mpr
  calc
    |a| * |b| ≤ (C*r)*(D*r) := mul_le_mul ha hb (abs_nonneg _) (mul_nonneg hC hr)
    _ ≤ C*D*r*(1+r) := by nlinarith [mul_nonneg (mul_nonneg hC hD) hr]

theorem tendsto_L1_normalized_product
    {a b r : ℕ → X → ℝ} {A B R : X → ℝ} {C D : ℝ}
    (ham : ∀ n, AEStronglyMeasurable (a n) μ)
    (hbm : ∀ n, AEStronglyMeasurable (b n) μ)
    (hrm : ∀ n, Measurable (r n))
    (ha : Tendsto (fun n => eLpNorm (fun x => a n x-A x) 1 μ) atTop (𝓝 0))
    (hb : Tendsto (fun n => eLpNorm (fun x => b n x-B x) 1 μ) atTop (𝓝 0))
    (hr : Tendsto (fun n => eLpNorm (fun x => r n x-R x) 1 μ) atTop (𝓝 0))
    (hri : UniformIntegrable r 1 μ)
    (hr0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ r n x) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hab : ∀ n, ∀ᵐ x ∂μ, |a n x| ≤ C*r n x)
    (hbb : ∀ n, ∀ᵐ x ∂μ, |b n x| ≤ D*r n x) :
    Tendsto (fun n => eLpNorm (fun x =>
      a n x*b n x/(1+|r n x|)-A x*B x/(1+|R x|)) 1 μ) atTop (𝓝 0) := by
  have hma := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0) ha
  have hmb := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0) hb
  have hmr := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0) hr
  have hc : Continuous (fun y : ℝ => (1+|y|)⁻¹) := by
    apply Continuous.inv₀ (continuous_const.add continuous_abs)
    intro y
    exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg y))
  have hmr' := tendstoInMeasure_continuous_comp (fun n => (hrm n).aestronglyMeasurable) hmr hc
  have hmp := tendstoInMeasure_mul ham hbm hma hmb
  have hmp' := tendstoInMeasure_mul (fun n => (ham n).mul (hbm n))
    (fun n => hc.comp_aestronglyMeasurable (hrm n).aestronglyMeasurable) hmp hmr'
  have hui : UniformIntegrable (fun n x => (C*D)*r n x) 1 μ :=
    uniformIntegrable_of_varying_multiplier (a := fun (_ : ℕ) (_ : X) => C*D) hri
      (fun _ => measurable_const) (⟨C*D,mul_nonneg hC hD⟩ : ℝ≥0)
      (fun _ _ => le_of_eq (abs_of_nonneg (mul_nonneg hC hD)))
  have hnm n : AEStronglyMeasurable (fun x => a n x*b n x/(1+|r n x|)) μ := by
    have hm := ((ham n).mul (hbm n)).mul
      (hc.comp_aestronglyMeasurable (hrm n).aestronglyMeasurable)
    change AEStronglyMeasurable (fun x => a n x*b n x*(1+|r n x|)⁻¹) μ at hm
    simpa only [div_eq_mul_inv] using hm
  have hnorm n : ∀ᵐ x ∂μ, ‖a n x*b n x/(1+|r n x|)‖ₑ ≤ ‖(C*D)*r n x‖ₑ := by
    filter_upwards [hr0 n,hab n,hbb n] with x hx hax hbx
    apply enorm_le_iff_norm_le.mpr
    rw [Real.norm_eq_abs,Real.norm_of_nonneg (mul_nonneg (mul_nonneg hC hD) hx)]
    exact normalized_product_bound hx hC hD hax hbx
  obtain ⟨hui',K,hK⟩ := hui
  have hni : UniformIntegrable (fun n x => a n x*b n x/(1+|r n x|)) 1 μ :=
    ⟨hui'.ae_mono hnm hnorm,K,fun n => (eLpNorm_mono_enorm_ae (hnm n) (hnorm n)).trans (hK n)⟩
  have hm : TendstoInMeasure μ (fun n x => a n x*b n x/(1+|r n x|)) atTop
      (fun x => A x*B x/(1+|R x|)) := by
    change TendstoInMeasure μ (fun n x => a n x*b n x*(1+|r n x|)⁻¹) atTop
      (fun x => A x*B x*(1+|R x|)⁻¹) at hmp'
    simpa only [div_eq_mul_inv] using hmp'
  exact tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by norm_num) hnm
    (hni.memLp_of_tendstoInMeasure hm) hni.1 hm

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Truncating a mass-normalized velocity pair costs only its L1 tail -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

def fiberMass (ν : Measure Y) (f : X × Y → ℝ) (x : X) : ℝ := ∫ v, f (x,v) ∂ν

def normalizedPair (ν : Measure Y) (f : X × Y → ℝ) : X × (Y × Y) → ℝ :=
  normalizedTensor (fiberMass ν f) f f

theorem fiberMass_measurable {f : X × Y → ℝ} (hf : Measurable f) :
    Measurable (fiberMass ν f) := hf.stronglyMeasurable.integral_prod_right'.measurable

theorem normalizedTensor_norm_swap {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (normalizedTensor d f g) 1 (μ.prod (ν.prod ν)) =
      eLpNorm (normalizedTensor d g f) 1 (μ.prod (ν.prod ν)) := by
  have hp := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := ν))
  calc
    _ = eLpNorm ((normalizedTensor d g f) ∘ (fun z : X × (Y × Y) => (z.1,z.2.2,z.2.1)))
        1 (μ.prod (ν.prod ν)) := by
      congr 1
      funext z
      dsimp only [normalizedTensor,Function.comp_apply]
      rw [mul_comm]
    _ = _ := eLpNorm_comp_measurePreserving
      (normalizedTensor_measurable hd hg hf).aestronglyMeasurable hp

theorem normalizedPair_integrable {f : X × Y → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) (hfi : Integrable f (μ.prod ν)) :
    Integrable (normalizedPair ν f) (μ.prod (ν.prod ν)) :=
  normalizedTensor_integrable (fiberMass_measurable hfm)
    (fun x => integral_nonneg (fun v => hf (x,v))) hfm hfm hf hf hfi hfi
    (ae_of_all _ (fun _ => le_rfl))

theorem normalizedPair_truncation_error {f u : X × Y → ℝ}
    (hfm : Measurable f) (hum : Measurable u)
    (hf : ∀ z, 0 ≤ f z) (hu : ∀ z, 0 ≤ u z) (huf : ∀ z, u z ≤ f z)
    (hfi : Integrable f (μ.prod ν)) (hui : Integrable u (μ.prod ν)) :
    eLpNorm (fun z => normalizedPair ν f z-
      normalizedTensor (fiberMass ν f) u u z) 1 (μ.prod (ν.prod ν)) ≤
      2*eLpNorm (fun z => f z-u z) 1 (μ.prod ν) := by
  have hm := fiberMass_measurable (ν := ν) hfm
  have hn x : 0 ≤ fiberMass ν f x := integral_nonneg (fun v => hf (x,v))
  have hd : ∀ᵐ x ∂μ, (∫ v, f (x,v) ∂ν) ≤ fiberMass ν f x := ae_of_all _ (fun _ => le_rfl)
  have hud : ∀ᵐ x ∂μ, (∫ v, u (x,v) ∂ν) ≤ fiberMass ν f x := by
    filter_upwards [hfi.prod_right_ae,hui.prod_right_ae] with x hfx hux
    exact integral_mono hux hfx (fun v => huf (x,v))
  have hsub z : 0 ≤ f z-u z := sub_nonneg.mpr (huf z)
  have hA := normalizedTensor_L1_le hm hn hfm (hfm.sub hum) hf hsub hfi (hfi.sub hui) hd
  have hB := normalizedTensor_L1_le hm hn hum (hfm.sub hum) hu hsub hui (hfi.sub hui) hud
  have he : (fun z => normalizedPair ν f z-normalizedTensor (fiberMass ν f) u u z) =
      normalizedTensor (fiberMass ν f) f (f-u)+normalizedTensor (fiberMass ν f) (f-u) u := by
    funext z
    dsimp only [normalizedPair,normalizedTensor,Pi.add_apply,Pi.sub_apply]
    ring
  rw [he]
  calc
    _ ≤ eLpNorm (normalizedTensor (fiberMass ν f) f (f-u)) 1 (μ.prod (ν.prod ν))+
        eLpNorm (normalizedTensor (fiberMass ν f) (f-u) u) 1 (μ.prod (ν.prod ν)) :=
      eLpNorm_add_le (by norm_num)
    _ = eLpNorm (normalizedTensor (fiberMass ν f) f (f-u)) 1 (μ.prod (ν.prod ν))+
        eLpNorm (normalizedTensor (fiberMass ν f) u (f-u)) 1 (μ.prod (ν.prod ν)) := by
      rw [normalizedTensor_norm_swap hm (hfm.sub hum) hum]
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add hA hB

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # The normalized gain action respects spacetime representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

def action (K : Kernel (X × Velocity) Velocity) (f : X × Velocity → ℝ≥0∞)
    (z : X × Velocity) : ℝ≥0∞ := ∫⁻ v, f (z.1,v) ∂K z

theorem action_measurable (K : Kernel (X × Velocity) Velocity) [IsSFiniteKernel K]
    {f : X × Velocity → ℝ≥0∞} (hf : Measurable f) : Measurable (action K f) := by
  have h : Measurable (fun p : (X × Velocity) × Velocity => f (p.1.1,p.2)) :=
    hf.comp (measurable_fst.fst.prodMk measurable_snd)
  exact h.lintegral_kernel_prod_right'

theorem action_normalized_congr_ae (hcarleman : Published.GPV2009CarlemanInput)
    (μ : Measure X) [SFinite μ] (c : Kernel X Velocity) [IsSFiniteKernel c]
    {r : X × Velocity → ℝ≥0∞} (hr : Measurable r)
    (hc : ∀ x, c x = volume.withDensity (fun v => r (x,v))) (q : ℝ)
    {f g : X × Velocity → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[μ.prod volume] g) :
    action (inputKernel c q) f =ᵐ[μ.prod volume] action (inputKernel c q) g := by
  apply (ae_prod_iff_ae_ae
    (measurableSet_eq_fun (action_measurable _ hf) (action_measurable _ hg))).mpr
  filter_upwards [ae_ae_of_ae_prod hfg] with x hx
  have hrx : Measurable (fun v => r (x,v)) := hr.comp (measurable_const.prodMk measurable_id)
  have hfx : Measurable (fun v => f (x,v)) := hf.comp (measurable_const.prodMk measurable_id)
  have hgx : Measurable (fun v => g (x,v)) := hg.comp (measurable_const.prodMk measurable_id)
  filter_upwards [normalized_integral_congr_ae hcarleman hrx hfx hgx hx q] with v hv
  unfold action
  rw [lintegral_inputKernel c q (x,v) hfx,lintegral_inputKernel c q (x,v) hgx,hc x]
  exact hv

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
