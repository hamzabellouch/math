import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedVelocityIntegral
import OAI.MathematicalPhysics.Boltzmann.Collision.ScalarEntropyConvex
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

section

/-! # Joint value and velocity truncation controlled by absolute entropy -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def entropyGauge (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  f p*(1+‖p.2‖^2+|Real.log (f p)|)

def entropyTruncation (R : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  if ‖p.2‖ ≤ R ∧ f p ≤ Real.exp R then f p else 0

theorem entropyGauge_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (entropyGauge f) :=
  hf.mul ((measurable_const.add (measurable_snd.norm.pow_const 2)).add hf.log.abs)

theorem entropyTruncation_measurable (R : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (entropyTruncation R f) :=
  Measurable.ite ((measurableSet_le measurable_snd.norm measurable_const).inter
    (measurableSet_le hf measurable_const)) hf measurable_const

omit [MeasurableSpace X] in
theorem entropyGauge_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ entropyGauge f p := mul_nonneg (hf p) (by positivity)

omit [MeasurableSpace X] in
theorem entropyGauge_ge_density {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    f p ≤ entropyGauge f p := by
  have hs := mul_nonneg (hf p) (sq_nonneg ‖p.2‖)
  have hl := mul_nonneg (hf p) (abs_nonneg (Real.log (f p)))
  unfold entropyGauge
  nlinarith

omit [MeasurableSpace X] in
theorem entropyTruncation_bounds (R : ℝ) {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ entropyTruncation R f p ∧ entropyTruncation R f p ≤ Real.exp R := by
  unfold entropyTruncation
  split_ifs with hp
  · exact ⟨hf p,hp.2⟩
  · exact ⟨le_rfl,(Real.exp_pos R).le⟩

omit [MeasurableSpace X] in
theorem entropyTruncation_support (R : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity)
    (hp : R < ‖p.2‖) : entropyTruncation R f p = 0 := by
  simp only [entropyTruncation,not_le.mpr hp,false_and,ite_false]

omit [MeasurableSpace X] in
theorem entropyTruncation_error {R : ℝ} (hR : 1 ≤ R) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    |f p-entropyTruncation R f p| ≤ entropyGauge f p/R := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  unfold entropyTruncation
  split_ifs with hp
  · rw [sub_self,abs_zero]
    exact div_nonneg (entropyGauge_nonneg hf p) hR0.le
  · rw [sub_zero,abs_of_nonneg (hf p)]
    apply (le_div_iff₀ hR0).mpr
    have hn := hf p
    have he : 0 ≤ ‖p.2‖^2 := sq_nonneg _
    have hl : 0 ≤ |Real.log (f p)| := abs_nonneg _
    by_cases hv : ‖p.2‖ ≤ R
    · have hbig : Real.exp R < f p := lt_of_not_ge (fun ha => hp ⟨hv,ha⟩)
      have hlog : R ≤ Real.log (f p) := by
        simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos R) hbig.le
      have hh := mul_le_mul_of_nonneg_left (hlog.trans (le_abs_self _)) hn
      unfold entropyGauge
      nlinarith [mul_nonneg hn he]
    · have hvR : R < ‖p.2‖ := lt_of_not_ge hv
      have hs : R ≤ ‖p.2‖^2 := by nlinarith [norm_nonneg p.2]
      have hh := mul_le_mul_of_nonneg_left hs hn
      unfold entropyGauge
      nlinarith [mul_nonneg hn hl]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Entropy convergence of truncations with a vanishing bounded perturbation -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem scalarRelativeEntropy_truncation_perturbation_le {q C p a b f : ℝ}
    (hC : 0 ≤ C) (hp : 1 < p) (v : Velocity)
    (ha : 0 ≤ a) (haf : a ≤ f) (hb : 0 ≤ b) (hbg : b ≤ C*H q v) :
    scalarRelativeEntropy (maxwellian v) (a+b) ≤
      scalarRelativeEntropy (maxwellian v) f+entropyPowerMajorant q C p v+
        (f+C*H q v)*Real.log 2 := by
  have hs := scalarRelativeEntropy_add_le (m := maxwellian v) ha hb
  have hcut := scalarRelativeEntropy_le_of_le (maxwellian_pos v) ha haf
  have hhot := scalarRelativeEntropy_le_majorant hC hp v hb hbg
  have hmass := mul_le_mul_of_nonneg_right (add_le_add haf hbg)
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  linarith

theorem entropy_truncation_perturbation_tendsto {q C p : ℝ}
    (hq : q < 2) (hC : 0 ≤ C) (hp : 1 < p)
    (hpi : Integrable (fun v : Velocity => H q v^p))
    {f : Density} (hf : FiniteEntropyDatum f)
    {a b : ℕ → Density} (ham : ∀ n, Measurable (a n)) (hbm : ∀ n, Measurable (b n))
    (ha : ∀ n z, 0 ≤ a n z ∧ a n z ≤ f z)
    (hb : ∀ n z, 0 ≤ b n z ∧ b n z ≤ C*H q z.2)
    (halim : ∀ z, Tendsto (fun n => a n z) atTop (𝓝 (f z)))
    (hblim : ∀ z, Tendsto (fun n => b n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, scalarRelativeEntropy (maxwellian z.2) (a n z+b n z))
      atTop (𝓝 (relativeEntropy f)) := by
  let B : Phase → ℝ := fun z => scalarRelativeEntropy (maxwellian z.2) (f z)+
    entropyPowerMajorant q C p z.2+(f z+C*H q z.2)*Real.log 2
  have hHi : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z)) := by
    apply (FiniteEntropyDatum.integrable_relativeEntropy hf).congr
    filter_upwards [] with z
    exact (scalarRelativeEntropy_eq (maxwellian_pos z.2) (f z)).symm
  have hBi : Integrable B := by
    exact (hHi.add ((entropyPowerMajorant_integrable (B := C) hq hpi).comp_snd volume)).add
      (((FiniteEntropyDatum.integrable hf).add (((integrable_H hq).const_mul C).comp_snd volume)).mul_const _)
  have hlim := tendsto_integral_of_dominated_convergence B (fun n => by
    have hm : Measurable (fun z : Phase => scalarRelativeEntropy (maxwellian z.2) (a n z+b n z)) := by
      have hsum := (ham n).add (hbm n)
      have hM : Measurable (fun z : Phase => maxwellian z.2) := by unfold maxwellian; fun_prop
      exact ((hsum.mul hsum.log).sub (hsum.mul (measurable_const.add hM.log))).add hM
    exact hm.aestronglyMeasurable) hBi (fun n => by
      filter_upwards [] with z
      rw [Real.norm_of_nonneg (scalarRelativeEntropy_nonneg (maxwellian_pos z.2)
        (add_nonneg (ha n z).1 (hb n z).1))]
      exact scalarRelativeEntropy_truncation_perturbation_le hC hp z.2 (ha n z).1 (ha n z).2
        (hb n z).1 (hb n z).2) (by
      filter_upwards [] with z
      have hs : Tendsto (fun n => a n z+b n z) atTop (𝓝 (f z)) := by
        simpa only [add_zero] using (halim z).add (hblim z)
      exact ((scalarRelativeEntropy_continuous (maxwellian z.2)).tendsto (f z)).comp hs)
  have he : (∫ z, scalarRelativeEntropy (maxwellian z.2) (f z)) = relativeEntropy f := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact scalarRelativeEntropy_eq (maxwellian_pos z.2) (f z)
  rwa [he] at hlim

end BoltzmannNonuniqueness

end

end

section

/-! # Uniform L1 approximation by bounded velocity truncations -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem integrable_of_entropyGauge {μ : Measure (X × Velocity)} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyGauge f) μ) : Integrable f μ := by
  apply hi.mono' hfm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_of_nonneg (hf p)]
    exact entropyGauge_ge_density hf p)

theorem entropyTruncation_integrable {μ : Measure X} [IsFiniteMeasure μ]
    (R : ℝ) {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    Integrable (entropyTruncation R f) (μ.prod volume) :=
  bounded_velocity_integrable (entropyTruncation_measurable R hfm)
    (fun p => (abs_of_nonneg (entropyTruncation_bounds R hf p).1).trans_le
      (entropyTruncation_bounds R hf p).2) (entropyTruncation_support R f)

theorem entropyTruncation_L1_bound {μ : Measure X} [IsFiniteMeasure μ]
    {R C : ℝ} (hR : 1 ≤ R) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyGauge f) (μ.prod volume))
    (hb : (∫ p, entropyGauge f p ∂μ.prod volume) ≤ C) :
    eLpNorm (fun p => f p-entropyTruncation R f p) 1 (μ.prod volume) ≤ ENNReal.ofReal (C/R) := by
  have hei := (integrable_of_entropyGauge hfm hf hi).sub (entropyTruncation_integrable R hfm hf)
  change Integrable (fun p => f p-entropyTruncation R f p) (μ.prod volume) at hei
  rw [eLpNorm_one_eq_lintegral_enorm hei.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hei]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ p, entropyGauge f p/R ∂μ.prod volume :=
      integral_mono hei.norm (hi.div_const R) (fun p => by
        simpa only [Real.norm_eq_abs] using entropyTruncation_error hR hf p)
    _ = (∫ p, entropyGauge f p ∂μ.prod volume)/R := integral_div R _
    _ ≤ C/R := div_le_div_of_nonneg_right hb (zero_le_one.trans hR)

theorem entropyTruncation_uniformIntegrable {μ : Measure X} [IsFiniteMeasure μ]
    (R : ℝ) {f : ℕ → X × Velocity → ℝ} (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p) :
    UniformIntegrable (fun n => entropyTruncation R (f n)) 1 (μ.prod volume) := by
  let g : X × Velocity → ℝ := fun p =>
    (Metric.closedBall (0:Velocity) R).indicator (fun _ => Real.exp R) p.2
  have hi : Integrable g (μ.prod volume) :=
    ((integrableOn_const (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet).comp_snd μ
  have hg := uniformIntegrable_const (ι := ℕ) (by norm_num : (1:ℝ≥0∞) ≤ 1) (by norm_num) (memLp_one_iff_integrable.mpr hi)
  have hdom (n : ℕ) (p : X × Velocity) : ‖entropyTruncation R (f n) p‖ ≤ g p := by
    rw [Real.norm_of_nonneg (entropyTruncation_bounds R (hf n) p).1]
    by_cases hp : p.2 ∈ Metric.closedBall 0 R
    · rw [show g p = Real.exp R from indicator_of_mem hp _]
      exact (entropyTruncation_bounds R (hf n) p).2
    · have hv : R < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
      rw [entropyTruncation_support R (f n) p hv,show g p = 0 from indicator_of_notMem hp _]
  have hmono (n : ℕ) (s : Set (X × Velocity)) :
      eLpNorm (entropyTruncation R (f n)) 1 ((μ.prod volume).restrict s) ≤
        eLpNorm g 1 ((μ.prod volume).restrict s) :=
    eLpNorm_mono_real (entropyTruncation_measurable R (hfm n)).aestronglyMeasurable (hdom n)
  refine ⟨unifIntegrable_iff.mpr ?_,?_⟩
  · intro ε hε
    obtain ⟨δ,hδ,hgδ⟩ := unifIntegrable_iff.mp hg.1 ε hε
    exact ⟨δ,hδ,fun n s hs => (hmono n s).trans (hgδ n s hs)⟩
  · obtain ⟨C,hC⟩ := hg.2
    refine ⟨C,fun n => ?_⟩
    have h := (hmono n univ).trans (by simpa only [Measure.restrict_univ] using hC n)
    simpa only [Measure.restrict_univ] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform entropy and velocity moments imply L1 compactness hypotheses -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

 theorem exists_entropyTruncation_radius (C : ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ j : ℕ, ENNReal.ofReal (C/((j:ℝ)+1)) ≤ ε := by
  have h : Tendsto (fun j : ℕ => C/((j:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have ht : Tendsto (fun j : ℕ => ENNReal.ofReal (C/((j:ℝ)+1))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h
  obtain ⟨j,hj⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨j,hj.le⟩

variable {X : Type*} [MeasurableSpace X]

theorem uniformIntegrable_of_entropyGauge {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable f 1 (μ.prod volume) := by
  apply Compactness.uniformIntegrable_of_approximation
    (g := fun j n => entropyTruncation ((j:ℝ)+1) (f n))
    (fun j => entropyTruncation_uniformIntegrable ((j:ℝ)+1) hfm hf)
  intro ε hε
  obtain ⟨j,hj⟩ := exists_entropyTruncation_radius C hε
  refine ⟨j,fun n => ?_⟩
  exact (entropyTruncation_L1_bound (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
    (hfm n) (hf n) (hi n) (hb n)).trans hj

theorem unifTight_of_entropyGauge {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UnifTight f 1 (μ.prod volume) := by
  intro ε hε
  obtain ⟨j,hj⟩ := exists_entropyTruncation_radius C hε
  let R : ℝ := (j:ℝ)+1
  let s : Set (X × Velocity) := univ ×ˢ Metric.closedBall 0 R
  have hs : MeasurableSet s := MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet
  refine ⟨s,?_,fun n => ?_⟩
  · rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  · have hdom (p : X × Velocity) : ‖sᶜ.indicator (f n) p‖ ≤ ‖f n p-entropyTruncation R (f n) p‖ := by
      by_cases hp : p ∈ s
      · rw [indicator_of_notMem (notMem_compl_iff.mpr hp),norm_zero]
        exact norm_nonneg _
      · have hv : R < ‖p.2‖ := by
          have hnv : p.2 ∉ Metric.closedBall 0 R := fun hv => hp ⟨mem_univ _,hv⟩
          simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hnv
        rw [indicator_of_mem (mem_compl hp),entropyTruncation_support R (f n) p hv,sub_zero]
    exact (eLpNorm_mono ((hfm n).indicator hs.compl).aestronglyMeasurable hdom).trans
      ((entropyTruncation_L1_bound (by dsimp [R]; have := Nat.cast_nonneg (α := ℝ) j; linarith)
        (hfm n) (hf n) (hi n) (hb n)).trans hj)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
