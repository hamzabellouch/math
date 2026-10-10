import OAI.MathematicalPhysics.Boltzmann.Branching.VaryingBoundedMultiplier
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

section

/-! # Bounded measurable multipliers preserve uniform integrability -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_of_bounded_multiplier
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℝ}
    (hf : UniformIntegrable f 1 μ) {a : X → ℝ} (ha : Measurable a)
    (C : ℝ≥0) (hC : ∀ x, |a x| ≤ C) :
    UniformIntegrable (fun n x => a x*f n x) 1 μ := by
  let D : ℝ≥0 := C+1
  have hD : (0 : ℝ≥0∞) < D := by simp [D]
  have hb (n : ℕ) (ν : Measure X) (hν : ν ≤ μ) :
      eLpNorm (fun x => a x*f n x) 1 ν ≤ (D : ℝ≥0∞)*eLpNorm (f n) 1 ν := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (ha.aestronglyMeasurable.mul ((hf.aestronglyMeasurable n).mono_measure hν))
    filter_upwards [] with x
    apply NNReal.coe_le_coe.mp
    change ‖a x*f n x‖ ≤ (D:ℝ)*‖f n x‖
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right ((hC x).trans (by dsimp [D]; norm_num)) (abs_nonneg _)
  constructor
  · apply unifIntegrable_iff.mpr
    intro ε hε
    obtain ⟨δ,hδ,hδsmall⟩ := unifIntegrable_iff.mp hf.1 (ε/(D:ℝ≥0∞))
      (ENNReal.div_pos hε.ne' ENNReal.coe_ne_top)
    refine ⟨δ,hδ,fun n s hs => ?_⟩
    calc
      _ ≤ (D:ℝ≥0∞)*eLpNorm (f n) 1 (μ.restrict s) := hb n _ Measure.restrict_le_self
      _ ≤ (D:ℝ≥0∞)*(ε/(D:ℝ≥0∞)) := mul_le_mul' le_rfl (hδsmall n s hs)
      _ = ε := ENNReal.mul_div_cancel hD.ne' ENNReal.coe_ne_top
  · obtain ⟨B,hB⟩ := hf.2
    refine ⟨D*B,fun n => ?_⟩
    exact (hb n μ le_rfl).trans (by simpa only [ENNReal.coe_mul] using mul_le_mul' le_rfl (hB n))

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform integrability under bounded varying coefficients -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_of_varying_multiplier
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f a : ℕ → X → ℝ}
    (hf : UniformIntegrable f 1 μ) (ha : ∀ n, Measurable (a n))
    (C : ℝ≥0) (hC : ∀ n x, |a n x| ≤ C) :
    UniformIntegrable (fun n x => a n x*f n x) 1 μ := by
  have hconst := uniformIntegrable_of_bounded_multiplier hf
    (a := fun _ => (C:ℝ)) measurable_const C (fun _ => by simp)
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => a n x*f n x) μ :=
    (ha n).aestronglyMeasurable.mul (hf.aestronglyMeasurable n)
  have hb (n : ℕ) : ∀ᵐ x ∂μ, ‖a n x*f n x‖ₑ ≤ ‖(C:ℝ)*f n x‖ₑ := by
    filter_upwards [] with x
    apply ENNReal.coe_le_coe.mpr
    apply NNReal.coe_le_coe.mp
    change ‖a n x*f n x‖ ≤ ‖(C:ℝ)*f n x‖
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg C.coe_nonneg]
    exact mul_le_mul_of_nonneg_right (hC n x) (abs_nonneg _)
  obtain ⟨hu,B,hB⟩ := hconst
  exact ⟨hu.ae_mono hm hb,B,fun n => (eLpNorm_mono_enorm_ae (hm n) (hb n)).trans (hB n)⟩

theorem uniformIntegrable_sub
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : ℕ → X → ℝ}
    (hf : UniformIntegrable f 1 μ) (hg : UniformIntegrable g 1 μ) :
    UniformIntegrable (fun n x => f n x-g n x) 1 μ := by
  obtain ⟨hu,C,hC⟩ := hf
  obtain ⟨hv,D,hD⟩ := hg
  refine ⟨hu.sub hv (by norm_num),C+D,fun n => ?_⟩
  exact (eLpNorm_sub_le (by norm_num : (1:ℝ≥0∞) ≤ 1)).trans
    (by simpa only [ENNReal.coe_add] using add_le_add (hC n) (hD n))

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform integrability removes bounded multipliers that vanish in L1 -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness

theorem tendsto_L1_mul_uniformIntegrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f a : ℕ → X → ℝ} (hf : UniformIntegrable f 1 μ)
    (hfm : ∀ n, Measurable (f n)) (ham : ∀ n, Measurable (a n))
    (ha0 : Tendsto (fun n => eLpNorm (a n) 1 μ) atTop (𝓝 0))
    (C : ℝ≥0) (ha : ∀ n x, |a n x| ≤ C) :
    Tendsto (fun n => eLpNorm (fun x => a n x*f n x) 1 μ) atTop (𝓝 0) := by
  let D : ℝ≥0 := C+1
  have hD : (0 : ℝ≥0∞) < D := by simp [D]
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hε2 : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hε' : 0 < (ε/2)/(D:ℝ≥0∞) :=
    ENNReal.div_pos hε2.ne' ENNReal.coe_ne_top
  obtain ⟨K,hK⟩ := hf.spec (by norm_num : (1:ℝ≥0∞) ≠ 0) (by norm_num) hε'
  let u (n : ℕ) : X → ℝ := {x | ‖f n x‖₊ < K}.indicator (f n)
  have hum n : Measurable (u n) :=
    (hfm n).indicator (measurableSet_lt (hfm n).nnnorm measurable_const)
  have hub n x : |u n x| ≤ K := by
    by_cases hx : ‖f n x‖₊ < K
    · simpa [u,hx,Real.norm_eq_abs] using
        (show ‖f n x‖ ≤ (K:ℝ) by exact_mod_cast hx.le)
    · simp [u,hx]
  have hue n : eLpNorm (fun x => f n x-u n x) 1 μ ≤ (ε/2)/(D:ℝ≥0∞) := by
    have he : (fun x => f n x-u n x) = {x | K ≤ ‖f n x‖₊}.indicator (f n) := by
      funext x
      by_cases hx : ‖f n x‖₊ < K
      · simp [u,hx,not_le.mpr hx]
      · simp [u,hx,le_of_not_gt hx]
    rw [he]
    exact hK n
  have hs : Tendsto (fun n => eLpNorm (fun x => a n x*u n x) 1 μ) atTop (𝓝 0) := by
    have h := tendsto_L1_bounded_mul_zero
      (fun n => (ham n).aestronglyMeasurable) (fun n => (hum n).aestronglyMeasurable)
      ha0 K.coe_nonneg (Eventually.of_forall (fun n => ae_of_all _ (hub n)))
    simpa only [mul_comm] using h
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hs (ε/2) hε2] with n hn
  have herr : eLpNorm (fun x => a n x*(f n x-u n x)) 1 μ ≤ ε/2 := by
    have hb := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      ((ham n).mul ((hfm n).sub (hum n))).aestronglyMeasurable
      (ae_of_all μ (fun x => show ‖a n x*(f n x-u n x)‖₊ ≤ D*‖f n x-u n x‖₊ from by
        apply NNReal.coe_le_coe.mp
        change |a n x*(f n x-u n x)| ≤ (D:ℝ)*|f n x-u n x|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right ((ha n x).trans (by dsimp [D]; norm_num)) (abs_nonneg _)))
      (p := 1)
    calc
      _ ≤ (D:ℝ≥0∞)*eLpNorm (fun x => f n x-u n x) 1 μ := hb
      _ ≤ (D:ℝ≥0∞)*((ε/2)/(D:ℝ≥0∞)) := mul_le_mul' le_rfl (hue n)
      _ = ε/2 := ENNReal.mul_div_cancel hD.ne' ENNReal.coe_ne_top
  have he : (fun x => a n x*f n x) =
      (fun x => a n x*(f n x-u n x))+(fun x => a n x*u n x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact (eLpNorm_add_le (by norm_num)).trans ((add_le_add herr hn).trans_eq ε.add_halves)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform L¹ approximation preserves uniform integrability

This is the analytic bridge from the fixed outer-annulus majorants and the
vanishing small-annulus collision integrals to full uniform integrability.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_of_approximation {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ℕ → X → ℝ} {g : ℕ → ℕ → X → ℝ}
    (hg : ∀ j, UniformIntegrable (g j) 1 μ)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ j : ℕ, ∀ n,
      eLpNorm (fun x => f n x-g j n x) 1 μ ≤ ε) :
    UniformIntegrable f 1 μ := by
  have htri (j n : ℕ) (ν : Measure X) : eLpNorm (f n) 1 ν ≤
      eLpNorm (fun x => f n x-g j n x) 1 ν+eLpNorm (g j n) 1 ν := by
    have he : f n = (fun x => f n x-g j n x)+(g j n) := by funext x; simp
    calc
      _ = eLpNorm ((fun x => f n x-g j n x)+(g j n)) 1 ν :=
        congrArg (fun h : X → ℝ => eLpNorm h 1 ν) he
      _ ≤ _ := eLpNorm_add_le (by norm_num)
  constructor
  · apply unifIntegrable_iff.mpr
    intro ε hε
    obtain ⟨j,hj⟩ := happrox (ε/2) (ε.half_pos hε.ne')
    obtain ⟨δ,hδ,hgδ⟩ := unifIntegrable_iff.mp (hg j).1 (ε/2) (ε.half_pos hε.ne')
    refine ⟨δ,hδ,?_⟩
    intro n s hs
    calc
      _ ≤ eLpNorm (fun x => f n x-g j n x) 1 (μ.restrict s)+
          eLpNorm (g j n) 1 (μ.restrict s) := htri j n _
      _ ≤ ε/2+ε/2 := add_le_add
        ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hj n)) (hgδ n s hs)
      _ = ε := ε.add_halves
  · obtain ⟨j,hj⟩ := happrox 1 (by norm_num)
    obtain ⟨C,hC⟩ := (hg j).2
    refine ⟨1+C,?_⟩
    intro n
    calc
      _ ≤ eLpNorm (fun x => f n x-g j n x) 1 μ+eLpNorm (g j n) 1 μ := htri j n _
      _ ≤ 1+C := add_le_add (hj n) (hC n)
      _ = _ := by simp

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Extending uniformly integrable families by zero from a measurable region -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_indicator_of_restrict
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℝ}
    {s : Set X} (hs : MeasurableSet s) (hf : UniformIntegrable f 1 (μ.restrict s)) :
    UniformIntegrable (fun n => s.indicator (f n)) 1 μ := by
  constructor
  · apply unifIntegrable_iff'.mpr
    intro ε hε
    obtain ⟨δ,hδ,hsmall⟩ := unifIntegrable_iff'.mp hf.1 ε hε
    refine ⟨δ,hδ,fun n a ha hμa => ?_⟩
    calc
      _ = eLpNorm (f n) 1 ((μ.restrict s).restrict a) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hs,
          Measure.restrict_restrict hs,Measure.restrict_restrict ha,inter_comm]
      _ ≤ ε := hsmall n a ha ((Measure.restrict_le_self a).trans hμa)
  · obtain ⟨C,hC⟩ := hf.2
    refine ⟨C,fun n => ?_⟩
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    exact hC n

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Sums and real absolute-value majorants for uniform L1 integrability -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem uniformIntegrable_add {f g : ℕ → X → ℝ}
    (hf : UniformIntegrable f 1 μ) (hg : UniformIntegrable g 1 μ) :
    UniformIntegrable (fun n x => f n x+g n x) 1 μ := by
  obtain ⟨hU,A,hA⟩ := hf
  obtain ⟨hV,B,hB⟩ := hg
  refine ⟨hU.add hV (by norm_num),A+B,fun n => ?_⟩
  exact (eLpNorm_add_le (by norm_num)).trans (by
    simpa only [ENNReal.coe_add] using add_le_add (hA n) (hB n))

theorem uniformIntegrable_abs_le {f g : ℕ → X → ℝ}
    (hg : UniformIntegrable g 1 μ) (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ g n x) : UniformIntegrable f 1 μ := by
  have hnorm n : ∀ᵐ x ∂μ, ‖f n x‖ₑ ≤ ‖g n x‖ₑ := by
    filter_upwards [hb n] with x hx
    apply enorm_le_iff_norm_le.mpr
    simpa only [Real.norm_eq_abs] using hx.trans (le_abs_self _)
  obtain ⟨hU,A,hA⟩ := hg
  exact ⟨hU.ae_mono hfm hnorm,A,
    fun n => (eLpNorm_mono_enorm_ae (hfm n) (hnorm n)).trans (hA n)⟩

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform integrability transferred through a measure-preserving chart -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_of_comp_measurePreserving
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {φ : X → Y} (hφ : MeasurePreserving φ μ ν)
    {f : ℕ → Y → ℝ} (hf : ∀ n, Measurable (f n))
    (h : UniformIntegrable (fun n => f n ∘ φ) 1 μ) : UniformIntegrable f 1 ν := by
  constructor
  · apply unifIntegrable_iff'.mpr
    intro ε hε
    obtain ⟨δ,hδ,hsmall⟩ := unifIntegrable_iff'.mp h.1 ε hε
    refine ⟨δ,hδ,?_⟩
    intro n s hs hνs
    have hpre : μ (φ ⁻¹' s) ≤ δ := by
      rw [hφ.measure_preimage hs.nullMeasurableSet]
      exact hνs
    have hb := hsmall n (φ ⁻¹' s) (hs.preimage hφ.measurable) hpre
    rw [eLpNorm_comp_measurePreserving (hf n).aestronglyMeasurable.restrict
      (hφ.restrict_preimage hs)] at hb
    exact hb
  · obtain ⟨C,hC⟩ := h.2
    refine ⟨C,fun n => ?_⟩
    have he := eLpNorm_comp_measurePreserving (p := (1 : ℝ≥0∞))
      (hf n).aestronglyMeasurable hφ
    rw [← he]
    exact hC n

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Removing a finite prefix without changing the common sequence index -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

def zeroPrefix {X : Type*} (N : ℕ) (f : ℕ → X → ℝ) (n : ℕ) : X → ℝ :=
  if N ≤ n then f n else 0

theorem zeroPrefix_eventually {X : Type*} (N : ℕ) (f : ℕ → X → ℝ) :
    ∀ᶠ n in atTop, zeroPrefix N f n = f n := by
  filter_upwards [eventually_ge_atTop N] with n hn
  exact ite_eq_left hn

theorem uniformIntegrable_zeroPrefix {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ℕ → X → ℝ} {N : ℕ} {p : ℝ≥0∞}
    (h : UniformIntegrable (fun n => f (n+N)) p μ) :
    UniformIntegrable (zeroPrefix N f) p μ := by
  constructor
  · apply unifIntegrable_iff.mpr
    intro ε hε
    obtain ⟨δ,hδ,hs⟩ := unifIntegrable_iff.mp h.1 ε hε
    refine ⟨δ,hδ,fun n s hμs => ?_⟩
    by_cases hn : N ≤ n
    · simpa only [zeroPrefix,ite_eq_left hn,Nat.sub_add_cancel hn] using hs (n-N) s hμs
    · simp only [zeroPrefix,ite_eq_right hn,eLpNorm_zero]
      exact bot_le
  · obtain ⟨C,hC⟩ := h.2
    refine ⟨C,fun n => ?_⟩
    by_cases hn : N ≤ n
    · simpa only [zeroPrefix,ite_eq_left hn,Nat.sub_add_cancel hn] using hC (n-N)
    · simp only [zeroPrefix,ite_eq_right hn,eLpNorm_zero]
      exact bot_le

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Tensoring a uniformly integrable family with one fixed integrable function -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

 theorem eLpNorm_mul_prod_one {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (fun p : X × Y => f p.1*g p.2) 1 (μ.prod ν) =
      eLpNorm f 1 μ*eLpNorm g 1 ν := by
  have hm : AEStronglyMeasurable (fun p : X × Y => f p.1*g p.2) (μ.prod ν) :=
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hm,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable]
  simp only [enorm_mul]
  have he : AEMeasurable (fun p : X × Y => ‖f p.1‖ₑ*‖g p.2‖ₑ) (μ.prod ν) :=
    ((hf.enorm.comp measurable_fst).mul (hg.enorm.comp measurable_snd)).aemeasurable
  rw [lintegral_prod _ he]
  simp_rw [lintegral_const_mul _ hg.enorm]
  exact lintegral_mul_const _ hf.enorm

theorem uniformIntegrable_tensor {μ : Measure X} {ν : Measure Y}
    [IsFiniteMeasure μ] [SFinite ν] {f : ℕ → X → ℝ} {g : Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hui : UniformIntegrable f 1 μ)
    (hgm : Measurable g) (hgi : Integrable g ν) :
    UniformIntegrable (fun (n : ℕ) (p : X × Y) => f n p.1*g p.2) 1 (μ.prod ν) := by
  have hd (j : ℕ) : 0 < ENNReal.ofReal (1/((j:ℝ)+1)) := by positivity
  choose C hC using (fun j => hui.spec (by norm_num : (1:ℝ≥0∞) ≠ 0)
    (by norm_num : (1:ℝ≥0∞) ≠ ∞) (hd j))
  let u (j n : ℕ) : X → ℝ := {x | ‖f n x‖₊ < C j}.indicator (f n)
  have hum (j n : ℕ) : Measurable (u j n) :=
    (hfm n).indicator (measurableSet_lt (hfm n).nnnorm measurable_const)
  have hub (j n : ℕ) (x : X) : |u j n x| ≤ (C j : ℝ) := by
    by_cases hx : ‖f n x‖₊ < C j
    · simpa [u,hx,Real.norm_eq_abs] using
        (show ‖f n x‖ ≤ (C j:ℝ) by exact_mod_cast hx.le)
    · simp [u,hx]
  have hue (j n : ℕ) : eLpNorm (fun x => f n x-u j n x) 1 μ ≤ ENNReal.ofReal (1/((j:ℝ)+1)) := by
    have he : (fun x => f n x-u j n x) = {x | C j ≤ ‖f n x‖₊}.indicator (f n) := by
      funext x
      by_cases hx : ‖f n x‖₊ < C j
      · simp [u,hx,not_le.mpr hx]
      · simp [u,hx,le_of_not_gt hx]
    rw [he]
    exact hC j n
  apply uniformIntegrable_of_approximation (g := fun j n p => u j n p.1*g p.2)
  · intro j
    let b : X × Y → ℝ := fun p => (C j:ℝ)*|g p.2|
    have hbi : Integrable b (μ.prod ν) := (integrable_const (C j:ℝ)).mul_prod hgi.abs
    have hbui := uniformIntegrable_const (ι := ℕ) (by norm_num : (1:ℝ≥0∞) ≤ 1)
      (by norm_num) (memLp_one_iff_integrable.mpr hbi)
    have hm n : AEStronglyMeasurable (fun p : X × Y => u j n p.1*g p.2) (μ.prod ν) :=
      ((hum j n).comp measurable_fst |>.mul (hgm.comp measurable_snd)).aestronglyMeasurable
    have he n : ∀ᵐ p : X × Y ∂μ.prod ν, ‖u j n p.1*g p.2‖ₑ ≤ ‖b p‖ₑ := by
      filter_upwards [] with p
      apply enorm_le_iff_norm_le.mpr
      rw [Real.norm_eq_abs,abs_mul,Real.norm_of_nonneg (mul_nonneg (C j).coe_nonneg (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hub j n p.1) (abs_nonneg _)
    obtain ⟨hu,K,hK⟩ := hbui
    exact ⟨hu.ae_mono hm he,K,fun n => (eLpNorm_mono_enorm_ae (hm n) (he n)).trans (hK n)⟩
  · intro ε hε
    have hdlim : Tendsto (fun j : ℕ => ENNReal.ofReal (1/((j:ℝ)+1))) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
        (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds) :
          Tendsto (fun j : ℕ => (1:ℝ)/((j:ℝ)+1)) atTop (𝓝 0))
    have hp := ENNReal.Tendsto.mul_const hdlim (Or.inr (memLp_one_iff_integrable.mpr hgi).eLpNorm_ne_top)
    simp only [zero_mul] at hp
    obtain ⟨j,hj⟩ := (hp.eventually (gt_mem_nhds hε)).exists
    refine ⟨j,fun n => ?_⟩
    have he : (fun p : X × Y => f n p.1*g p.2-u j n p.1*g p.2) =
        (fun p : X × Y => (f n p.1-u j n p.1)*g p.2) := by funext p; ring
    rw [he,eLpNorm_mul_prod_one (f := fun x => f n x-u j n x) ((hfm n).sub (hum j n)) hgm]
    exact (mul_le_mul' (hue j n) le_rfl).trans hj.le

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Nonnegative uniformly integrable densities have uniformly small clipping errors -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem uniform_min_truncation {f : ℕ → X → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n x, 0 ≤ f n x)
    (hui : UniformIntegrable f 1 μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ K : ℝ, (C:ℝ) ≤ K → ∀ n,
      eLpNorm (fun x => f n x-min (f n x) K) 1 μ ≤ ε := by
  obtain ⟨C,hC⟩ := hui.spec (by norm_num) (by norm_num) hε
  refine ⟨C,fun K hK n => ?_⟩
  apply le_trans _ (hC n)
  apply eLpNorm_mono ((hfm n).sub ((hfm n).min measurable_const)).aestronglyMeasurable
  intro x
  change ‖f n x-min (f n x) K‖ ≤ ‖{x | C ≤ ‖f n x‖₊}.indicator (f n) x‖
  by_cases hx : f n x ≤ K
  · rw [min_eq_left hx,sub_self,norm_zero]
    exact norm_nonneg _
  · have hlt : K < f n x := lt_of_not_ge hx
    have hcx : C ≤ ‖f n x‖₊ := by
      have hb : (C:ℝ) ≤ ‖f n x‖ := by
        rw [Real.norm_of_nonneg (hf n x)]
        exact hK.trans hlt.le
      exact_mod_cast hb
    rw [min_eq_right hlt.le,indicator_of_mem (show x ∈ {x | C ≤ ‖f n x‖₊} from hcx),
      Real.norm_of_nonneg (sub_nonneg.mpr hlt.le),Real.norm_of_nonneg (hf n x)]
    exact sub_le_self _ (C.coe_nonneg.trans hK)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
