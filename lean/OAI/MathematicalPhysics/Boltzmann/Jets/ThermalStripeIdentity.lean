import OAI.MathematicalPhysics.Boltzmann.Collision.TransverseStripeWeak
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFamilyBounds

namespace OAI

section

/-! # Weak averaging after the Gaussian thermal mixture -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

def thermalStripeCentered (p d t : ℝ) (a : Bool) (y : Transverse) : ℝ :=
  ∫ w : Transverse × ℝ, centeredStripe p (t*d*w.1 0) a (y 0)*
    JetThermalKernel.J (SheetMeasures.join w) ∂(volume : Measure Transverse).prod volume

theorem thermalStripeCentered_bound (p d t : ℝ) (a : Bool) (y : Transverse) :
    |thermalStripeCentered p d t a y| ≤ 1 :=
  JetCoreDensity.masked_thermal_bound (fun w => centeredStripe_bound p (t*d*w.1 0) a (y 0))

theorem thermalStripeCentered_measurable (p d t : ℝ) (a : Bool) :
    Measurable (thermalStripeCentered p d t a) := by
  have hm : Measurable (fun z : Transverse × (Transverse × ℝ) =>
      centeredStripe p (t*d*z.2.1 0) a (z.1 0)) :=
    ((measurable_const.indicator (stripeLine_measurable p a)).comp
      (by fun_prop)).sub_const (1/4)
  exact (hm.mul ((JetThermalKernel.J_smooth.continuous.measurable.comp
    SheetMeasures.join.measurable).comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

theorem thermalStripeCentered_weakStar {p : ℕ → ℝ} (hp : ∀ n, 0 < p n)
    (hplim : Tendsto p atTop (𝓝 0)) (d : ℕ → ℝ) (t : ℝ) (a : Bool) :
    Compactness.WeakStarLInfConverges (volume : Measure Transverse)
      (fun n => thermalStripeCentered (p n) (d n) t a) (fun _ => 0) := by
  let ν := (volume : Measure Transverse).prod (volume : Measure ℝ)
  let J : Transverse × ℝ → ℝ := fun w => JetThermalKernel.J (SheetMeasures.join w)
  let g : ℕ → Transverse × (Transverse × ℝ) → ℝ :=
    fun n z => centeredStripe (p n) (t*d n*z.2.1 0) a (z.1 0)
  have hw := centeredStripe_fiber_weakStar ν hp hplim
    (d := fun n (w : Transverse × ℝ) => t*d n*w.1 0) (by intro n; fun_prop) a
  have hJ : Integrable J ν := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  have hgm (n) : Measurable (g n) :=
    ((measurable_const.indicator (stripeLine_measurable (p n) a)).comp
      (by fun_prop)).sub_const (1/4)
  refine ⟨measurable_const,?_⟩
  intro ψ hψ
  have hi (n) : Integrable (fun z : Transverse × (Transverse × ℝ) =>
      (ψ z.1*J z.2)*g n z) ((volume : Measure Transverse).prod ν) := by
    exact ((hψ.mul_prod hJ).bdd_mul (hgm n).aestronglyMeasurable
      (ae_of_all _ (fun z => centeredStripe_bound (p n) (t*d n*z.2.1 0) a (z.1 0)))).congr
        (ae_of_all _ (fun z => mul_comm _ _))
  have heq (n) : (∫ z, (ψ z.1*J z.2)*g n z ∂(volume : Measure Transverse).prod ν) =
      ∫ y, ψ y*thermalStripeCentered (p n) (d n) t a y := by
    rw [integral_prod _ (hi n)]
    apply integral_congr_ae
    filter_upwards [] with y
    unfold thermalStripeCentered
    rw [← integral_const_mul]
    congr 1
    funext w
    change (ψ y*J w)*g n (y,w) = ψ y*(g n (y,w)*J w)
    ring
  have ht := hw.2 (fun z => ψ z.1*J z.2) (hψ.mul_prod hJ)
  simp only [mul_zero,integral_zero] at ht ⊢
  change Tendsto (fun n => ∫ z, (ψ z.1*J z.2)*g n z
    ∂(volume : Measure Transverse).prod ν) atTop (𝓝 0) at ht
  simpa only [heq] using ht

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # The physical stripe and its centered Gaussian mixture -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem stripe_dilated_indicator {r : ℝ} (hr : 0 < r) (s : ℝ) (a : Bool) (y : Transverse) :
    (stripe s a).indicator (fun _ => (1:ℝ)) (r • y) =
      (stripeLine (r*(s/r)^2) a).indicator (fun _ => (1:ℝ)) (y 0) := by
  classical
  have hi := stripe_dilation hr (s/r) a y
  rw [mul_div_cancel₀ _ hr.ne'] at hi
  rw [stripeAtPeriod_mem_iff] at hi
  by_cases hy : r • y ∈ stripe s a
  · rw [indicator_of_mem hy,indicator_of_mem (hi.mp hy)]
  · rw [indicator_of_notMem hy,indicator_of_notMem (mt hi.mpr hy)]

theorem thermalStripeCentered_eq {r : ℝ} (hr : 0 < r) (s d t : ℝ) (a : Bool)
    (y : Transverse) :
    thermalStripeCentered (r*(s/r)^2) d t a y =
      (∫ w : Transverse × ℝ, (stripe s a).indicator (fun _ => (1:ℝ))
        (r • (y-t • (d • w.1)))*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)-1/4 := by
  let ν := (volume : Measure Transverse).prod (volume : Measure ℝ)
  let χ : Transverse × ℝ → ℝ := fun w =>
    (stripe s a).indicator (fun _ => (1:ℝ)) (r • (y-t • (d • w.1)))
  let J : Transverse × ℝ → ℝ := fun w => JetThermalKernel.J (SheetMeasures.join w)
  have hJ : Integrable J ν := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  have hχm : Measurable χ :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_stripe s a)).comp (by fun_prop)
  have hχ (w) : |χ w| ≤ 1 := by
    classical
    by_cases hw : r • (y-t • (d • w.1)) ∈ stripe s a <;> simp [χ,hw]
  have hi := hJ.bdd_mul hχm.aestronglyMeasurable (ae_of_all _ hχ)
  have heq (w : Transverse × ℝ) :
      centeredStripe (r*(s/r)^2) (t*d*w.1 0) a (y 0) = χ w-1/4 := by
    dsimp only [centeredStripe,χ]
    rw [stripe_dilated_indicator hr]
    congr 2
    change y 0-t*d*w.1 0 = y 0-t*(d*w.1 0)
    ring
  unfold thermalStripeCentered
  simp_rw [heq,sub_mul]
  rw [integral_sub hi (hJ.const_mul (1/4)),integral_const_mul,JetCoreDensity.thermal_integral_one,mul_one]

end BoltzmannNonuniqueness.JetGeometry

end

end

end OAI
