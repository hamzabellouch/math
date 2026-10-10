import OAI.MathematicalPhysics.Boltzmann.Branching.AverageMajorant
import OAI.MathematicalPhysics.Boltzmann.Branching.ProductionDualLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.VaryingBoundedMultiplier
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongPairMoment
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

section

/-! # The weak-star cold / strong-L1 hot product passage -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

def WeakStarLInfConverges {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a : ℕ → X → ℝ) (b : X → ℝ) : Prop :=
  Measurable b ∧ ∀ ψ : X → ℝ, Integrable ψ μ →
    Tendsto (fun n => ∫ x, ψ x*a n x ∂μ) atTop (𝓝 (∫ x, ψ x*b x ∂μ))

theorem WeakStarLInfConverges.strong_product
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a f : ℕ → X → ℝ} {b g : X → ℝ} (ha : WeakStarLInfConverges μ a b)
    (ham : ∀ n, Measurable (a n)) (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hgi : Integrable g μ)
    (hf : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 1 μ) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C)
    (haC : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |a n x| ≤ C)
    (hbC : ∀ᵐ x ∂μ, |b x| ≤ C) :
    Published.WeakL1Converges μ (fun n x => a n x*f n x) (fun x => b x*g x) := by
  refine ⟨ha.1.mul hgm,hgi.bdd_mul ha.1.aestronglyMeasurable hbC,?_⟩
  intro ψ hψ hψB
  obtain ⟨D,hD⟩ := hψB
  have hD' (x) : |ψ x| ≤ |D| := (hD x).trans (le_abs_self D)
  have hψg : Integrable (fun x => ψ x*g x) μ :=
    hgi.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hD')
  have hsecond := ha.2 (fun x => ψ x*g x) hψg
  have helimit : (fun x => (ψ x*g x)*b x) = (fun x => ψ x*(b x*g x)) := by
    funext x
    ring
  rw [helimit] at hsecond
  have hsmall := tendsto_L1_bounded_mul_zero
    (fun n => ((hfm n).sub hgm).aestronglyMeasurable)
    (fun n => (ham n).aestronglyMeasurable) hf hC haC
  have hε := tendsto_L1_bounded_mul_zero
    (fun n => ((ham n).mul ((hfm n).sub hgm)).aestronglyMeasurable)
    (fun _ => hψ.aestronglyMeasurable) hsmall (abs_nonneg D)
    (Filter.Eventually.of_forall (fun _ => ae_of_all _ hD'))
  change Tendsto (fun n => eLpNorm (fun x => ψ x*(a n x*(f n x-g x))) 1 μ) atTop (𝓝 0) at hε
  have hεi : ∀ᶠ n in atTop,
      Integrable (fun x => ψ x*(a n x*(f n x-g x))) μ :=
    (hε.eventually (eventually_lt_nhds (show (0:ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top))).mono
      (fun _ hn => memLp_one_iff_integrable.mp hn)
  have hfirst : Tendsto (fun n => ∫ x, ψ x*(a n x*(f n x-g x)) ∂μ) atTop (𝓝 0) := by
    simpa only [sub_zero,integral_zero] using
      tendsto_integral_of_L1' (fun _ : X => (0:ℝ)) hεi (by simpa only [Pi.sub_def,sub_zero] using hε)
  have hlim := hfirst.add hsecond
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [haC,hεi] with n han hεn
  have hprod : Integrable (fun x => (ψ x*g x)*a n x) μ := by
    apply (hψg.bdd_mul (ham n).aestronglyMeasurable han).congr
    exact ae_of_all _ (fun x => mul_comm _ _)
  rw [← integral_add hεn hprod]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Bounded weak-star limits extend across an almost-everywhere exhaustion -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

private theorem pairing_restrict_error {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f a : X → ℝ} (hf : Integrable f μ) (ha : Measurable a)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, |a x| ≤ C) {s : Set X} (hs : MeasurableSet s) :
    |(∫ x, f x*a x ∂μ)-(∫ x in s, f x*a x ∂μ)| ≤ C*(∫ x in sᶜ, |f x| ∂μ) := by
  have hi : Integrable (fun x => f x*a x) μ :=
    (hf.bdd_mul ha.aestronglyMeasurable hC).congr (ae_of_all _ (fun x => mul_comm _ _))
  rw [← setIntegral_compl hs hi]
  have hb := norm_integral_le_of_norm_le (μ := μ.restrict sᶜ) (f := fun x => f x*a x)
    (hf.restrict.abs.const_mul C) ?_
  · simpa only [Real.norm_eq_abs,integral_const_mul] using hb
  · filter_upwards [ae_restrict_of_ae hC] with x hx
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans_eq (mul_comm _ _)

theorem weakStar_of_exhaustion {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a : ℕ → X → ℝ} {b : X → ℝ} (ham : ∀ n, Measurable (a n)) (hbm : Measurable b)
    {C : ℝ}
    (hab : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |a n x| ≤ C) (hbb : ∀ᵐ x ∂μ, |b x| ≤ C)
    (s : ℕ → Set X) (hs : ∀ m, MeasurableSet (s m))
    (hcover : ∀ᵐ x ∂μ, ∀ᶠ m in atTop, x ∈ s m)
    (hlocal : ∀ m, WeakStarLInfConverges (μ.restrict (s m)) a b) :
    WeakStarLInfConverges μ a b := by
  refine ⟨hbm,fun f hf => ?_⟩
  have htail : Tendsto (fun m => ∫ x in (s m)ᶜ, |f x| ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (f := fun _ : X => (0:ℝ))
      (fun x => |f x|) (fun m => hf.abs.aestronglyMeasurable.indicator (hs m).compl) hf.abs
      (fun m => ae_of_all _ (fun x => by
        by_cases hx : x ∈ (s m)ᶜ <;> simp [hx])) ?_
    · simpa only [integral_indicator (hs _).compl,integral_zero] using ht
    · filter_upwards [hcover] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with m hm
      simp only [mem_compl_iff,hm,not_true_eq_false,not_false_eq_true,indicator_of_notMem]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : Tendsto (fun m => (2*C)*(∫ x in (s m)ᶜ, |f x| ∂μ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using htail.const_mul (2*C)
  obtain ⟨m,hm⟩ := (hsmall.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))).exists
  have hmid := Metric.tendsto_nhds.mp ((hlocal m).2 f hf.restrict) (ε/2) (by positivity)
  filter_upwards [hab,hmid] with n han hmn
  rw [Real.dist_eq] at hmn ⊢
  have hleft := pairing_restrict_error hf (ham n) han (hs m)
  have hright := pairing_restrict_error hf hbm hbb (hs m)
  have htri₁ := abs_sub_le (∫ x, f x*a n x ∂μ) (∫ x in s m, f x*a n x ∂μ) (∫ x, f x*b x ∂μ)
  have htri₂ := abs_sub_le (∫ x in s m, f x*a n x ∂μ) (∫ x in s m, f x*b x ∂μ) (∫ x, f x*b x ∂μ)
  rw [abs_sub_comm (∫ x in s m, f x*b x ∂μ)] at htri₂
  linarith

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Extending bounded cold-average convergence to all L1 tests -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Compactness

private theorem bounded_pairing_error {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g a : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (ha : Measurable a) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hab : ∀ᵐ x ∂μ, |a x| ≤ C)
    (hdiff : eLpNorm (f-g) 1 μ ≤ ENNReal.ofReal δ) :
    |(∫ x, f x*a x ∂μ)-(∫ x, g x*a x ∂μ)| ≤ C*δ := by
  have hfg := hf.sub hg
  have hfa : Integrable (fun x => f x*a x) μ :=
    (hf.bdd_mul ha.aestronglyMeasurable hab).congr (ae_of_all _ (fun x => mul_comm _ _))
  have hga : Integrable (fun x => g x*a x) μ :=
    (hg.bdd_mul ha.aestronglyMeasurable hab).congr (ae_of_all _ (fun x => mul_comm _ _))
  have hi : (∫ x, ‖f x-g x‖ ∂μ) ≤ δ := by
    apply (ENNReal.ofReal_le_ofReal_iff hδ).mp
    change ENNReal.ofReal (∫ x, ‖(f-g) x‖ ∂μ) ≤ ENNReal.ofReal δ
    rw [ofReal_integral_norm_eq_lintegral_enorm hfg]
    rwa [eLpNorm_one_eq_lintegral_enorm hfg.aestronglyMeasurable] at hdiff
  rw [← integral_sub hfa hga,← Real.norm_eq_abs]
  have he : (fun x => f x*a x-g x*a x) = (fun x => (f x-g x)*a x) := by
    funext x
    ring
  rw [he]
  apply (norm_integral_le_of_norm_le (hfg.norm.const_mul C) ?_).trans
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hi hC
  · filter_upwards [hab] with x hx
    change ‖(f x-g x)*a x‖ ≤ C*‖f x-g x‖
    rw [norm_mul,Real.norm_eq_abs (a x)]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem weakStar_of_continuous_compact_tests
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [μ.Regular]
    {a : ℕ → X → ℝ} {b : X → ℝ}
    (ham : ∀ n, Measurable (a n)) (hbm : Measurable b)
    {C : ℝ} (hC : 0 ≤ C)
    (hab : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |a n x| ≤ C)
    (hbb : ∀ᵐ x ∂μ, |b x| ≤ C)
    (htest : ∀ g : X → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun n => ∫ x, g x*a n x ∂μ) atTop (𝓝 (∫ x, g x*b x ∂μ))) :
    WeakStarLInfConverges μ a b := by
  refine ⟨hbm,fun f hf => Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  let δ := ε/(3*(2*C+1))
  have hden : 0 < 3*(2*C+1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ*(3*(2*C+1)) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨g,hgc,hfg,hg,hgm⟩ :=
    (memLp_one_iff_integrable.mpr hf).exists_hasCompactSupport_eLpNorm_sub_le
      (by norm_num : (1:ℝ≥0∞) ≠ ⊤) (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))
  have hgi : Integrable g μ := memLp_one_iff_integrable.mp hgm
  have hmid := Metric.tendsto_nhds.mp (htest g hg hgc) (ε/3) (by positivity)
  filter_upwards [hab,hmid] with n han hgn
  rw [Real.dist_eq] at hgn ⊢
  have hleft := bounded_pairing_error hf hgi (ham n) hC hδ.le han hfg
  have hright := bounded_pairing_error hf hgi hbm hC hδ.le hbb hfg
  have htri₁ := abs_sub_le (∫ x, f x*a n x ∂μ) (∫ x, g x*a n x ∂μ) (∫ x, f x*b x ∂μ)
  have htri₂ := abs_sub_le (∫ x, g x*a n x ∂μ) (∫ x, g x*b x ∂μ) (∫ x, f x*b x ∂μ)
  rw [abs_sub_comm (∫ x, g x*b x ∂μ)] at htri₂
  nlinarith

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Integrating bounded weak-star limits over additional variables -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

theorem weakStar_zero_of_fibers
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {g : ℕ → X × Y → ℝ} (hm : ∀ n, Measurable (g n))
    (hb : ∀ n z, |g n z| ≤ 1)
    (hf : ∀ y, WeakStarLInfConverges μ (fun n x => g n (x,y)) (fun _ => 0)) :
    WeakStarLInfConverges (μ.prod ν) g (fun _ => 0) := by
  refine ⟨measurable_const,?_⟩
  intro ψ hψ
  have hi (n) : Integrable (fun z => ψ z*g n z) (μ.prod ν) := by
    exact (hψ.bdd_mul (hm n).aestronglyMeasurable (ae_of_all _ (hb n))).congr
      (ae_of_all _ (fun z => mul_comm _ _))
  have ht := tendsto_integral_of_dominated_convergence
    (μ := ν) (F := fun n y => ∫ x, ψ (x,y)*g n (x,y) ∂μ)
    (f := fun _ => (0:ℝ)) (fun y => ∫ x, ‖ψ (x,y)‖ ∂μ)
    (fun n => (hi n).integral_prod_right.aestronglyMeasurable)
    hψ.integral_norm_prod_right ?_ ?_
  · simp only [mul_zero,integral_zero] at ht ⊢
    convert ht using 1
    funext n
    exact integral_prod_symm _ (hi n)
  · intro n
    filter_upwards [hψ.prod_left_ae] with y hy
    apply norm_integral_le_of_norm_le hy.norm
    filter_upwards [] with x
    rw [norm_mul,Real.norm_eq_abs (g n (x,y))]
    exact (mul_le_mul_of_nonneg_left (hb n (x,y)) (norm_nonneg _)).trans_eq (mul_one _)
  · filter_upwards [hψ.prod_left_ae] with y hy
    simpa only [mul_zero,integral_zero] using (hf y).2 (fun x => ψ (x,y)) hy

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # A bounded strongly convergent coefficient times a uniformly integrable weak limit -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.varying_bounded_mul
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f a : ℕ → X → ℝ} {g b : X → ℝ}
    (hw : WeakL1Converges μ f g) (hu : UniformIntegrable f 1 μ)
    (hfm : ∀ n, Measurable (f n)) (ham : ∀ n, Measurable (a n)) (hbm : Measurable b)
    (C : ℝ≥0) (ha : ∀ n x, |a n x| ≤ C) (hb : ∀ x, |b x| ≤ C)
    (hs : Tendsto (fun n => eLpNorm (fun x => a n x-b x) 1 μ) atTop (𝓝 0)) :
    WeakL1Converges μ (fun n x => a n x*f n x) (fun x => b x*g x) := by
  have he := Compactness.tendsto_L1_mul_uniformIntegrable hu hfm
    (fun n => (ham n).sub hbm) hs (C+C) (fun n x => by
      exact (abs_sub (a n x) (b x)).trans (add_le_add (ha n x) (hb x)))
  apply (hw.bounded_mul hbm C hb).of_eLpNorm_sub
  · exact fun n => (memLp_one_iff_integrable.mp (hu.memLp n)).bdd_mul
      hbm.aestronglyMeasurable (ae_of_all μ hb)
  · exact fun n => (memLp_one_iff_integrable.mp (hu.memLp n)).bdd_mul
      (ham n).aestronglyMeasurable (ae_of_all μ (ha n))
  · convert he using 1
    ext n
    congr 1
    funext x
    simp only [Pi.sub_apply]
    ring

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak-star convergence under measure-preserving coordinates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Compactness

theorem WeakStarLInfConverges.comp_measurableEquiv {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) {f : ℕ → Y → ℝ} {g : Y → ℝ}
    (h : WeakStarLInfConverges ν f g) :
    WeakStarLInfConverges μ (fun n => f n ∘ e) (g ∘ e) := by
  refine ⟨h.1.comp e.measurable,?_⟩
  intro ψ hψ
  have hi := (MeasurePreserving.symm e he).integrable_comp_of_integrable hψ
  have ht := h.2 (ψ ∘ e.symm) hi
  have hid (k : Y → ℝ) :
      (∫ y, (ψ ∘ e.symm) y*k y ∂ν) = ∫ x, ψ x*(k ∘ e) x ∂μ := by
    rw [← he.integral_comp' (fun y => (ψ ∘ e.symm) y*k y)]
    simp only [Function.comp_apply,MeasurableEquiv.symm_apply_apply]
  simpa only [hid] using ht

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Localizing bounded weak-star convergence -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Compactness

theorem WeakStarLInfConverges.restrict {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a : ℕ → X → ℝ} {b : X → ℝ}
    (h : WeakStarLInfConverges μ a b) {s : Set X} (hs : MeasurableSet s) :
    WeakStarLInfConverges (μ.restrict s) a b := by
  refine ⟨h.1,?_⟩
  intro ψ hψ
  have ht := h.2 (s.indicator ψ) ((integrable_indicator_iff hs).mpr hψ)
  have heq (f : X → ℝ) : (∫ x, s.indicator ψ x*f x ∂μ) = ∫ x, ψ x*f x ∂μ.restrict s := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ s <;> simp [hx]
  simpa only [heq] using ht

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Factorization of weak pair moments from strong velocity averages -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem weak_pair_moment_factorization {μ : Measure X} {ν : Measure Y}
    [IsFiniteMeasure μ] [SFinite ν]
    {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ} {W : X × (Y × Y) → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hfi : ∀ n, Integrable (f n) (μ.prod ν))
    (hpi : ∀ n, Integrable (fun z : X × (Y × Y) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) (μ.prod (ν.prod ν)))
    (hg : WeakL1Converges (μ.prod ν) f g)
    (hW : WeakL1Converges (μ.prod (ν.prod ν))
      (fun n z => f n (z.1,z.2.1)*f n (z.1,z.2.2)) W)
    {k l : X × Y → ℝ} (hk : Measurable k) (hl : Measurable l)
    (C D : ℝ) (hC : ∀ z, |k z| ≤ C) (hD : ∀ z, |l z| ≤ D)
    {A B : X → ℝ} (hAi : Integrable A μ) (hBi : Integrable B μ)
    (hA : Tendsto (fun n => eLpNorm (fun x => (∫ v, k (x,v)*f n (x,v) ∂ν)-A x) 1 μ)
      atTop (𝓝 0))
    (hB : Tendsto (fun n => eLpNorm (fun x => (∫ v, l (x,v)*f n (x,v) ∂ν)-B x) 1 μ)
      atTop (𝓝 0))
    (hui : UniformIntegrable (fun n x => (∫ v, k (x,v)*f n (x,v) ∂ν)*
      (∫ w, l (x,w)*f n (x,w) ∂ν)) 1 μ) :
    (fun x => ∫ y : Y × Y, (k (x,y.1)*l (x,y.2))*W (x,y) ∂ν.prod ν) =ᵐ[μ]
      (fun x => (∫ v, k (x,v)*g (x,v) ∂ν)*(∫ w, l (x,w)*g (x,w) ∂ν)) := by
  have hki (n) := ((hfi n).bdd_mul hk.aestronglyMeasurable (ae_of_all _ hC)).integral_prod_left
  have hli (n) := ((hfi n).bdd_mul hl.aestronglyMeasurable (ae_of_all _ hD)).integral_prod_left
  have hkg := (hg.marginal hfi hk C hC).eq_of_strong hki hAi hA
  have hlg := (hg.marginal hfi hl D hD).eq_of_strong hli hBi hB
  let kl : X × (Y × Y) → ℝ := fun z => k (z.1,z.2.1)*l (z.1,z.2.2)
  have hkl : Measurable kl := by dsimp [kl]; fun_prop
  have hklB : ∀ z, |kl z| ≤ |C| * |D| := by
    intro z
    dsimp [kl]
    rw [abs_mul]
    exact mul_le_mul ((hC _).trans (le_abs_self C)) ((hD _).trans (le_abs_self D))
      (abs_nonneg _) (abs_nonneg _)
  have hwp := hW.marginal hpi hkl (|C| * |D|) hklB
  have he (n) (x) : (∫ y : Y × Y, kl (x,y)*(f n (x,y.1)*f n (x,y.2)) ∂ν.prod ν) =
      (∫ v, k (x,v)*f n (x,v) ∂ν)*(∫ w, l (x,w)*f n (x,w) ∂ν) := by
    rw [← integral_prod_mul]
    congr 1
    ext y
    dsimp [kl]
    ring
  simp_rw [he] at hwp
  have hkm (n) : AEStronglyMeasurable (fun x => ∫ v, k (x,v)*f n (x,v) ∂ν) μ :=
    ((hk.mul (hfm n)).stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hlm (n) : AEStronglyMeasurable (fun x => ∫ v, l (x,v)*f n (x,v) ∂ν) μ :=
    ((hl.mul (hfm n)).stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hp := Compactness.tendsto_L1_product hkm hlm hA hB hui
  have hmi := hui.integrable_of_tendstoInMeasure
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0) hp)
  have hpEq := hwp.eq_of_strong (fun n => memLp_one_iff_integrable.mp (hui.memLp n)) hmi hp
  filter_upwards [hpEq,hkg,hlg] with x hx hkx hlx
  exact hx.symm.trans (by rw [hkx,hlx])

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Extended entropy production is lower semicontinuous under weak L¹ convergence -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem productionDual_integral_tendsto {a b : ℕ → X → ℝ} {A B s : X → ℝ}
    (hA : WeakL1Converges μ a A) (hB : WeakL1Converges μ b B)
    (ha : ∀ n, Integrable (a n) μ) (hb : ∀ n, Integrable (b n) μ)
    (hs : Measurable s) {C : ℝ} (hC : ∀ x, |s x| ≤ C) :
    Tendsto (fun n => ∫ x, productionDual (a n x) (b n x) (s x) ∂μ) atTop
      (𝓝 (∫ x, productionDual (A x) (B x) (s x) ∂μ)) := by
  let u := fun x => s x-Real.exp (-s x)+1
  let v := fun x => -s x-Real.exp (s x)+1
  have hum : Measurable u := (hs.sub hs.neg.exp).add measurable_const
  have hvm : Measurable v := (hs.neg.sub hs.exp).add measurable_const
  have hub x : |u x| ≤ C+Real.exp C+1 := productionDual_coefficient_bound (hC x)
  have hvb x : |v x| ≤ C+Real.exp C+1 := by
    simpa only [neg_neg] using productionDual_coefficient_bound
      (show |-s x| ≤ C by simpa using hC x)
  have he (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
      (∫ x, productionDual (f x) (g x) (s x) ∂μ) =
        (∫ x, u x*f x ∂μ)+(∫ x, v x*g x ∂μ) := by
    simp_rw [productionDual_linear]
    simpa only [u,v,mul_comm] using integral_add
      (hf.bdd_mul hum.aestronglyMeasurable (ae_of_all μ hub))
      (hg.bdd_mul hvm.aestronglyMeasurable (ae_of_all μ hvb))
  simp only [he _ _ (ha _) (hb _),he _ _ hA.2.1 hB.2.1]
  exact (hA.2.2 u hum ⟨_,hub⟩).add (hB.2.2 v hvm ⟨_,hvb⟩)

theorem ofReal_integral_le_lintegral {f : X → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  exact ENNReal.ofReal_le_of_le_toReal (sub_le_self _ ENNReal.toReal_nonneg)

theorem weak_production_liminf {a b : ℕ → X → ℝ} {A B : X → ℝ}
    (hA : WeakL1Converges μ a A) (hB : WeakL1Converges μ b B)
    (ha : ∀ n, Integrable (a n) μ) (hb : ∀ n, Integrable (b n) μ)
    (hAn : 0 ≤ᵐ[μ] A) (hBn : 0 ≤ᵐ[μ] B) :
    (∫⁻ x, extendedEntropyProduction (A x) (B x) ∂μ) ≤
      liminf (fun n => ∫⁻ x, extendedEntropyProduction (a n x) (b n x) ∂μ) atTop := by
  let s : ℕ → X → ℝ := fun n x => boundedProductionTest n (A x) (B x)
  let d : ℕ → X → ℝ := fun n x => productionDual (A x) (B x) (s n x)
  have hsm n : Measurable (s n) := measurable_boundedProductionTest n hA.1 hB.1
  have hsb n x : |s n x| ≤ (n:ℝ) := boundedProductionTest_bound n (A x) (B x)
  have hdi n : Integrable (d n) μ := integrable_productionDual hA.2.1 hB.2.1 (hsm n) (hsb n)
  have hdm n : Measurable (d n) := measurable_productionDual hA.1 hB.1 (hsm n)
  have hdn n : 0 ≤ᵐ[μ] d n := ae_of_all μ (fun x => productionDual_boundedTest_nonneg n _ _)
  have hlim n : ENNReal.ofReal (∫ x, d n x ∂μ) ≤
      liminf (fun k => ∫⁻ x, extendedEntropyProduction (a k x) (b k x) ∂μ) atTop := by
    have ht := ENNReal.tendsto_ofReal (productionDual_integral_tendsto hA hB ha hb (hsm n) (hsb n))
    rw [← ht.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall (fun k =>
      (ofReal_integral_le_lintegral (integrable_productionDual (ha k) (hb k) (hsm n) (hsb n))).trans
        (lintegral_mono (fun x => productionDual_ofReal_le _ _ _))))
  have hfatou : (∫⁻ x, extendedEntropyProduction (A x) (B x) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (d n x) ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (d n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hAn,hBn] with x hax hbx
        exact (ofReal_productionDual_boundedTest_tendsto hax hbx).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le (fun n => (hdm n).ennreal_ofReal)
  apply hfatou.trans
  exact liminf_le_of_frequently_le ((Eventually.of_forall (fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hdi n) (hdn n)]
    exact hlim n)).frequently)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A uniformly bounded weak L1 limit is a weak-star limit -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.weakStar
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [μ.Regular]
    {a : ℕ → X → ℝ} {b : X → ℝ} (h : WeakL1Converges μ a b)
    (ham : ∀ n, Measurable (a n)) {C : ℝ} (hC : 0 ≤ C)
    (hab : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |a n x| ≤ C) (hbb : ∀ᵐ x ∂μ, |b x| ≤ C) :
    Compactness.WeakStarLInfConverges μ a b := by
  apply Compactness.weakStar_of_continuous_compact_tests ham h.1 hC hab hbb
  intro φ hφ hφc
  obtain ⟨B,hB⟩ := hφc.exists_bound_of_continuous hφ
  exact h.2.2 φ hφ.measurable ⟨B,fun x => by simpa only [Real.norm_eq_abs] using hB x⟩

end BoltzmannNonuniqueness.Published

end

end

end OAI
