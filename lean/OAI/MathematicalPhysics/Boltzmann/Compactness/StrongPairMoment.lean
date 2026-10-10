import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedPairUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedKernelAction
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace OAI

section

/-! # Measurable strong L¹ limits are integrable -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Published

theorem integrable_of_strong_limit {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ᶠ n in atTop, Integrable (f n) μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 1 μ) atTop (𝓝 0)) :
    Integrable g μ := by
  have he := hlim.eventually (eventually_lt_nhds (show (0:ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top))
  obtain ⟨n,hfn,hn⟩ := (hf.and he).exists
  have hd : Integrable (fun x => f n x-g x) μ :=
    memLp_one_iff_integrable.mp hn
  exact (hfn.sub hd).congr (ae_of_all _ (fun x => by simp))

theorem WeakL1Converges.eq_of_strong_limit {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ℕ → X → ℝ} {g A : X → ℝ}
    (h : WeakL1Converges μ f g) (hf : ∀ᶠ n in atTop, Integrable (f n) μ)
    (hstrong : Tendsto (fun n => eLpNorm (fun x => f n x-A x) 1 μ) atTop (𝓝 0)) :
    A =ᵐ[μ] g :=
  h.eq_of_strong_eventually hf (integrable_of_strong_limit hf hstrong) hstrong

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Bounded families of strong L1 fibers converge on the product -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [IsFiniteMeasure ν]

theorem strongL1_of_strong_fibers {u : ℕ → X × Y → ℝ}
    (hm : ∀ n, Measurable (u n)) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hb : ∀ n, ∀ᵐ y ∂ν, eLpNorm (fun x => u n (x,y)) 1 μ ≤ B)
    (ht : ∀ᵐ y ∂ν, Tendsto (fun n => eLpNorm (fun x => u n (x,y)) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n) 1 (μ.prod ν)) atTop (𝓝 0) := by
  have he n y : eLpNorm (fun x => u n (x,y)) 1 μ = ∫⁻ x, ‖u n (x,y)‖ₑ ∂μ :=
    eLpNorm_one_eq_lintegral_enorm ((hm n).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hme n : Measurable (fun y => eLpNorm (fun x => u n (x,y)) 1 μ) := by
    simp_rw [he]
    exact (hm n).enorm.lintegral_prod_left'
  have hi : (∫⁻ _ : Y, B ∂ν) ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top hB (measure_ne_top _ _)
  have h := tendsto_lintegral_of_dominated_convergence (fun _ : Y => B) hme hb hi ht
  simp only [lintegral_zero] at h
  have hp n : eLpNorm (u n) 1 (μ.prod ν) =
      ∫⁻ y, eLpNorm (fun x => u n (x,y)) 1 μ ∂ν := by
    rw [eLpNorm_one_eq_lintegral_enorm (hm n).aestronglyMeasurable,
      lintegral_prod_symm _ (hm n).enorm.aemeasurable]
    simp_rw [he]
  simpa only [hp] using h

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Strong L1 products with bounded, strongly convergent coefficients -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strong_bounded_product {f a : ℕ → X → ℝ} {g b : X → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g) (hgi : Integrable g μ)
    (ham : ∀ n, Measurable (a n)) (hbm : Measurable b)
    (C : ℝ≥0) (ha : ∀ n x, |a n x| ≤ C) (hb : ∀ x, |b x| ≤ C)
    (hf : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 1 μ) atTop (𝓝 0))
    (ha0 : Tendsto (fun n => eLpNorm (fun x => a n x-b x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x*f n x-b x*g x) 1 μ) atTop (𝓝 0) := by
  have hfirst := tendsto_L1_bounded_mul_zero
    (fun n => ((hfm n).sub hgm).aestronglyMeasurable)
    (fun n => (ham n).aestronglyMeasurable) hf C.coe_nonneg
    (Eventually.of_forall (fun n => ae_of_all _ (ha n)))
  have hconst : UniformIntegrable (fun _ : ℕ => g) 1 μ :=
    uniformIntegrable_const (by norm_num) (by norm_num) (memLp_one_iff_integrable.mpr hgi)
  have hlast := tendsto_L1_mul_uniformIntegrable hconst (fun _ => hgm)
    (fun n => (ham n).sub hbm) ha0 (C+C)
    (fun n x => (abs_sub (a n x) (b x)).trans (add_le_add (ha n x) (hb x)))
  have ht := hfirst.add hlast
  simp only [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  change eLpNorm (fun x => a n x*f n x-b x*g x) 1 μ ≤
    eLpNorm (fun x => a n x*(f n x-g x)) 1 μ+
      eLpNorm (fun x => (a n x-b x)*g x) 1 μ
  have he : (fun x => a n x*f n x-b x*g x) =
      (fun x => a n x*(f n x-g x))+(fun x => (a n x-b x)*g x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact eLpNorm_add_le (by norm_num)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Strong velocity averages extend to bounded measurable kernel families -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable {μ : Measure X} {ν : Measure Y} {τ : Measure Z}
variable [SFinite μ] [SFinite ν] [IsFiniteMeasure τ]

theorem strong_bounded_kernel_averages
    {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hb : ∀ n, eLpNorm (f n) 1 (μ.prod ν) ≤ B)
    {k : Z × Y → ℝ} (hk : Measurable k) {C : ℝ} (hC : ∀ p, |k p| ≤ C)
    (ha : ∀ z, Tendsto (fun n => eLpNorm (fun x =>
      (∫ y, k (z,y)*f n (x,y) ∂ν)-(∫ y, k (z,y)*g (x,y) ∂ν)) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun p : X × Z =>
      (∫ y, k (p.2,y)*f n (p.1,y) ∂ν)-(∫ y, k (p.2,y)*g (p.1,y) ∂ν))
      1 (μ.prod τ)) atTop (𝓝 0) := by
  have hm (u : X × Y → ℝ) (hu : Measurable u) :
      Measurable (fun p : X × Z => ∫ y, k (p.2,y)*u (p.1,y) ∂ν) := by
    have hh : Measurable (fun p : (X × Z) × Y => k (p.1.2,p.2)*u (p.1.1,p.2)) := by
      fun_prop
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  apply strongL1_of_strong_fibers (fun n => (hm _ (hfm n)).sub (hm _ hgm))
    (B := ENNReal.ofReal C*(B+eLpNorm g 1 (μ.prod ν)))
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hB,(memLp_one_iff_integrable.mpr hgi).eLpNorm_ne_top⟩)
  · intro n
    apply ae_of_all
    intro z
    apply (weighted_average_difference_le (hfm n) hgm
      (hk.comp (measurable_const.prodMk measurable_snd)) (hfi n) hgi (fun p => hC (z,p.2))).trans
    apply mul_le_mul' le_rfl
    exact (eLpNorm_sub_le (by norm_num)).trans (add_le_add (hb n) le_rfl)
  · exact ae_of_all _ ha

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Removing a patch multiplier where it stays away from zero -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strong_on_patch_of_weighted {a : ℕ → X → ℝ} {b χ : X → ℝ}
    (ha : ∀ n, Measurable (a n)) (hb : Measurable b)
    {s : Set X} (hs : MeasurableSet s) {δ : ℝ} (hδ : 0 < δ)
    (hχ : ∀ x ∈ s, δ ≤ |χ x|)
    (hc : Tendsto (fun n => eLpNorm (fun x => χ x*a n x-χ x*b x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x-b x) 1 (μ.restrict s)) atTop (𝓝 0) := by
  have hbound n : eLpNorm (fun x => a n x-b x) 1 (μ.restrict s) ≤
      ENNReal.ofReal δ⁻¹*eLpNorm (fun x => χ x*a n x-χ x*b x) 1 μ := by
    calc
      _ ≤ ENNReal.ofReal δ⁻¹*eLpNorm (fun x => χ x*a n x-χ x*b x) 1 (μ.restrict s) := by
        apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((ha n).sub hb).aestronglyMeasurable
        filter_upwards [ae_restrict_mem hs] with x hx
        have hle := mul_le_mul_of_nonneg_right (hχ x hx) (abs_nonneg (a n x-b x))
        calc
          ‖a n x-b x‖ ≤ ‖χ x*a n x-χ x*b x‖/δ := by
            apply (le_div_iff₀ hδ).mpr
            simp only [Real.norm_eq_abs]
            rw [← mul_sub,abs_mul]
            nlinarith [hle]
          _ = δ⁻¹*‖χ x*a n x-χ x*b x‖ := by ring
      _ ≤ _ := mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have ht := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal δ⁻¹) hc (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le) hbound

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # A strong product of averages identifies the weak tensor moment -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Published

theorem weak_pair_moment_of_strong_product {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {f : ℕ → X × Y → ℝ} {W : X × (Y × Y) → ℝ}
    (hW : WeakL1Converges (μ.prod (ν.prod ν))
      (fun n z => f n (z.1,z.2.1)*f n (z.1,z.2.2)) W)
    (hpi : ∀ᶠ n in atTop, Integrable
      (fun z : X × (Y × Y) => f n (z.1,z.2.1)*f n (z.1,z.2.2)) (μ.prod (ν.prod ν)))
    {k l : X × Y → ℝ} (hk : Measurable k) (hl : Measurable l)
    (C D : ℝ) (hC : ∀ z, |k z| ≤ C) (hD : ∀ z, |l z| ≤ D)
    {A : X → ℝ}
    (hstrong : Tendsto (fun n => eLpNorm (fun x =>
      (∫ v, k (x,v)*f n (x,v) ∂ν)*(∫ w, l (x,w)*f n (x,w) ∂ν)-A x) 1 μ)
      atTop (𝓝 0)) :
    (fun x => ∫ y : Y × Y, (k (x,y.1)*l (x,y.2))*W (x,y) ∂ν.prod ν) =ᵐ[μ] A := by
  let kl : X × (Y × Y) → ℝ := fun z => k (z.1,z.2.1)*l (z.1,z.2.2)
  have hm : Measurable kl :=
    (hk.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hl.comp (measurable_fst.prodMk measurable_snd.snd))
  have hb z : |kl z| ≤ |C| * |D| := by
    dsimp only [kl]
    rw [abs_mul]
    exact mul_le_mul ((hC _).trans (le_abs_self C)) ((hD _).trans (le_abs_self D))
      (abs_nonneg _) (abs_nonneg _)
  have hw := hW.marginal_eventually hpi hm (|C| * |D|) hb
  have he n x : (∫ y : Y × Y, kl (x,y)*(f n (x,y.1)*f n (x,y.2)) ∂ν.prod ν) =
      (∫ v, k (x,v)*f n (x,v) ∂ν)*(∫ w, l (x,w)*f n (x,w) ∂ν) := by
    rw [← integral_prod_mul]
    congr 1
    funext y
    dsimp only [kl]
    ring
  have hi : ∀ᶠ n in atTop, Integrable
      (fun x => ∫ y : Y × Y, kl (x,y)*(f n (x,y.1)*f n (x,y.2)) ∂ν.prod ν) μ := by
    filter_upwards [hpi] with n hn
    exact (hn.bdd_mul hm.aestronglyMeasurable (ae_of_all _ hb)).integral_prod_left
  simp_rw [he] at hw hi
  exact (hw.eq_of_strong_limit hi hstrong).symm

end BoltzmannNonuniqueness.Published

end

end

end OAI
