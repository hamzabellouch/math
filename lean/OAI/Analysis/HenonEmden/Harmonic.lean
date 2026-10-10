import OAI.Analysis.HenonEmden.FundamentalSolution

namespace OAI

universe uE uE2

section Harmonic

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden.SphereCalculus
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma harmonic_mean_zero (hn : 2 ≤ Module.finrank ℝ E) {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (heq : ∀ x, Laplacian.laplacian u x = 0) {R : ℝ} (hR : 0 ≤ R) :
    mean u R = mean u 0 := by
  have hflux (r : ℝ) (hr : 0 < r) : HasDerivAt
      (fun s => s^(Module.finrank ℝ E-1)*meanD u s) 0 r := by
    convert hasDerivAt_mean_flux hu.contDiffOn (continuous_const.continuousOn : ContinuousOn (fun _ : E => (0:ℝ)) ({0}ᶜ))
      (fun x _ => by rw [heq x,neg_zero]) hr using 1
    simp [mean]
  have hfluxzero (r : ℝ) (hr : 0 < r) : meanD u r = 0 := by
    have hc : Continuous (fun s => s^(Module.finrank ℝ E-1)*meanD u s) :=
      (continuous_id.pow _).mul (continuous_meanD_global hu)
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.le hc.continuousOn
      (fun s hs => hflux s hs.1) (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 r)
    simp only [intervalIntegral.integral_zero,zero_pow (by omega : Module.finrank ℝ E-1 ≠ 0),zero_mul,sub_zero] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ hr.ne')
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR (continuous_mean hu.continuous).continuousOn
    (fun s hs => by simpa only [hfluxzero s hs.1] using hasDerivAt_mean hu.contDiffOn hs.1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 R)
  simpa only [intervalIntegral.integral_zero,sub_eq_zero] using hh.symm

lemma harmonic_ball_zero (hn : 2 ≤ Module.finrank ℝ E) {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (heq : ∀ x, Laplacian.laplacian u x = 0) (R : ℝ) :
    (∫ x in Metric.ball (0:E) R, u x) = (volume (Metric.ball (0:E) R)).toReal*u 0 := by
  have hi : IntegrableOn u (Metric.ball (0:E) R) :=
    (hu.continuous.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall (0:E) R)).mono_set Metric.ball_subset_closedBall
  have hic : IntegrableOn (fun _ : E => u 0) (Metric.ball (0:E) R) := integrableOn_const
  have hc : (volume (Metric.ball (0:E) R)).toReal*u 0 = ∫ _ : E in Metric.ball (0:E) R, u 0 := by simp [Measure.real]
  rw [hc]
  rw [← integral_indicator measurableSet_ball,← integral_indicator measurableSet_ball,
    Polar.integral_polar volume _ ((integrable_indicator_iff measurableSet_ball).mpr hi),
    Polar.integral_polar volume _ ((integrable_indicator_iff measurableSet_ball).mpr hic)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  have hh : ∀ θ : UnitSphere E, (r • (θ:E)) ∈ Metric.ball (0:E) R ↔ r < R := by
    intro θ; rw [Metric.mem_ball,dist_zero_right,norm_smul_sphere hr.le]
  by_cases hrR : r < R
  · have hiu : (fun θ : UnitSphere E => (Metric.ball (0:E) R).indicator u (r • (θ:E))) =
        fun θ : UnitSphere E => u (r • (θ:E)) := by
      ext θ
      exact indicator_of_mem ((hh θ).mpr hrR) _
    have hic0 : (fun θ : UnitSphere E => (Metric.ball (0:E) R).indicator (fun _ => u 0) (r • (θ:E))) =
        fun _ => u 0 := by
      ext θ
      exact indicator_of_mem ((hh θ).mpr hrR) _
    rw [hiu,hic0]
    change r^(Module.finrank ℝ E-1)*mean u r = _
    rw [harmonic_mean_zero hn hu heq hr.le,mean_zero]
    simp [integral_const,Measure.real,smul_eq_mul]
  · have hzero (f : E → ℝ) : (fun θ : UnitSphere E => (Metric.ball (0:E) R).indicator f (r • (θ:E))) = 0 := by
      ext θ
      exact indicator_of_notMem (mt (hh θ).mp hrR) _
    rw [hzero,hzero]
end HenonLaneEmden.SphereCalculus

namespace HenonLaneEmden.SphereCalculus
variable {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma harmonic_ball (hn : 2 ≤ Module.finrank ℝ E) {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (heq : ∀ x, Laplacian.laplacian u x = 0) (x : E) (R : ℝ) :
    (∫ y in Metric.ball x R, u y) = (volume (Metric.ball x R)).toReal*u x := by
  have hh := harmonic_ball_zero hn (hu.comp (contDiff_const.sub contDiff_id))
    (fun z => by change Laplacian.laplacian (fun y => u (x-y)) z = 0; rw [WeakPDE.laplacian_reflect hu,heq]) R
  simp only [Function.comp_def,id_eq,sub_zero] at hh
  have hind : (fun y => (Metric.ball x R).indicator u (x-y)) =
      (Metric.ball (0:E) R).indicator (fun y => u (x-y)) := by
    ext y
    have hm : x-y ∈ Metric.ball x R ↔ y ∈ Metric.ball (0:E) R := by
      simp [Metric.mem_ball,dist_eq_norm]
    by_cases hy : y ∈ Metric.ball (0:E) R
    · rw [indicator_of_mem ((hm).mpr hy),indicator_of_mem hy]
    · rw [indicator_of_notMem (mt hm.mp hy),indicator_of_notMem hy]
  have ht := integral_sub_left_eq_self (μ := volume) ((Metric.ball x R).indicator u) x
  rw [hind,integral_indicator measurableSet_ball,integral_indicator measurableSet_ball] at ht
  rw [← ht,hh,Measure.addHaar_ball_center volume x]

lemma harmonic_nonnegative_constant (hn : 2 ≤ Module.finrank ℝ E) {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (heq : ∀ x, Laplacian.laplacian u x = 0) (hp : ∀ x, 0 ≤ u x)
    (x z : E) : u x = u z := by
  suffices h : ∀ x z : E, u x ≤ u z from le_antisymm (h x z) (h z x)
  intro x z
  let b := dist x z
  let c := (volume (Metric.ball (0:E) 1)).toReal
  have hc : 0 < c := ENNReal.toReal_pos (Metric.measure_ball_pos volume (0:E) zero_lt_one).ne'
    (measure_ball_lt_top (μ := volume)).ne
  have hv (y : E) (R : ℝ) (hR : 0 < R) : (volume (Metric.ball y R)).toReal = R^(Module.finrank ℝ E)*c := by
    rw [Measure.addHaar_ball_of_pos volume y hR,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hR.le _)]
  have hcomp (R : ℝ) (hR : 0 < R) : u x ≤ (1+b/R)^(Module.finrank ℝ E)*u z := by
    have hb : 0 ≤ b := dist_nonneg
    have hs : Metric.ball x R ⊆ Metric.ball z (R+b) := by
      intro y hy
      have ht := dist_triangle y x z
      change dist y z < R+dist x z
      change dist y x < R at hy
      linarith
    have hI := setIntegral_mono_set (μ := volume) (s := Metric.ball x R) (t := Metric.ball z (R+b))
      ((hu.continuous.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall z (R+b))).mono_set Metric.ball_subset_closedBall)
      (Eventually.of_forall fun y => hp y) (Eventually.of_forall hs)
    rw [harmonic_ball hn hu heq,harmonic_ball hn hu heq,hv x R hR,hv z (R+b) (by positivity)] at hI
    have hfac : (R+b)^(Module.finrank ℝ E) = R^(Module.finrank ℝ E)*(1+b/R)^(Module.finrank ℝ E) := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [hfac] at hI
    apply (mul_le_mul_iff_of_pos_left (mul_pos (pow_pos hR _) hc)).mp
    convert hI using 1; ring
  have ht : Tendsto (fun R : ℝ => (1+b/R)^(Module.finrank ℝ E)*u z) atTop (𝓝 (u z)) := by
    have hh := (((tendsto_const_nhds : Tendsto (fun _ : ℝ => b) atTop (𝓝 b)).div_atTop tendsto_id).const_add 1).pow (Module.finrank ℝ E)
    simpa using hh.mul_const (u z)
  exact ge_of_tendsto ht (eventually_atTop.2 ⟨1,fun R hR => hcomp R (by linarith)⟩)
end HenonLaneEmden.SphereCalculus

end
end Harmonic

end OAI
