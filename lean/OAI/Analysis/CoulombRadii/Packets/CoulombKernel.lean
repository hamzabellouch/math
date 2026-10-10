import Mathlib
import OAI.Analysis.CoulombRadii.Variational.WeakLaplacian

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def coulombKernel (x : Position) : ℝ := ‖x‖⁻¹

def potentialOf (ρ : Position → ℝ) (x : Position) : ℝ :=
  ∫ y, coulombKernel (x-y)*ρ y

def kernelBallMass (r : ℝ) : ℝ := ∫ y in Metric.ball (0 : Position) r, coulombKernel y

theorem coulombKernel_nonneg (x : Position) : 0 ≤ coulombKernel x :=
  inv_nonneg.mpr (norm_nonneg x)

theorem measurable_coulombKernel : Measurable coulombKernel :=
  measurable_norm.inv

theorem coulombKernel_integrableOn_ball (r : ℝ) :
    IntegrableOn coulombKernel (Metric.ball (0 : Position) r) := by
  apply integrableOn_ball_of_norm_le_rpow
    (by simp : 1 ≤ Module.finrank ℝ Position)
    (C := 1) (α := 1) (by norm_num : (1:ℝ) < Module.finrank ℝ Position)
    _ measurable_coulombKernel.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simp [coulombKernel, Real.rpow_neg_one])

theorem radial_integral_exterior (f : ℝ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : Position in {x | a < ‖x‖}, f ‖x‖) =
      (4*Real.pi) * ∫ r : ℝ in Set.Ioi a, r^2*f r := by
  have hS : MeasurableSet {x : Position | a < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [← integral_indicator hS]
  have hid : (fun x : Position => Set.indicator {x : Position | a < ‖x‖} (fun x => f ‖x‖) x) =
      (fun x : Position => (Set.Ioi a).indicator f ‖x‖) := by
    ext x
    by_cases hx : a < ‖x‖ <;> simp [hx]
  rw [hid, integral_fun_norm_addHaar volume]
  have hinner : (∫ r in Set.Ioi (0:ℝ), r^(Module.finrank ℝ Position-1) • (Set.Ioi a).indicator f r) =
      ∫ r in Set.Ioi a, r^2*f r := by
    simp only [finrank_euclideanSpace_fin]
    norm_num
    have heq : (fun r : ℝ => r^2*(Set.Ioi a).indicator f r) =
        (Set.Ioi a).indicator (fun r => r^2*f r) := by
      ext r
      by_cases hr : r ∈ Set.Ioi a <;> simp [hr]
    rw [heq, setIntegral_indicator measurableSet_Ioi]
    rw [Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi ha)]
  rw [hinner]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow,
    one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3), smul_eq_mul,
    nsmul_eq_mul]
  norm_num [Position, finrank_euclideanSpace_fin]
  ring

theorem radial_integrable_exterior (f : ℝ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x : Position => f ‖x‖) {x | a < ‖x‖} ↔
      IntegrableOn (fun r : ℝ => r^2*f r) (Set.Ioi a) := by
  have hS : MeasurableSet {x : Position | a < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [← integrable_indicator_iff hS]
  change Integrable (fun x : Position => Set.indicator {x : Position | a < ‖x‖} (fun x => f ‖x‖) x) ↔ _
  have hid : (fun x : Position => Set.indicator {x : Position | a < ‖x‖} (fun x => f ‖x‖) x) =
      (fun x : Position => (Set.Ioi a).indicator f ‖x‖) := by
    ext x
    by_cases hx : a < ‖x‖ <;> simp [hx]
  rw [hid, integrable_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace_fin]
  norm_num
  have heq : (fun r : ℝ => r^2*(Set.Ioi a).indicator f r) =
      (Set.Ioi a).indicator (fun r => r^2*f r) := by
    ext r
    by_cases hr : r ∈ Set.Ioi a <;> simp [hr]
  rw [heq, integrableOn_indicator_iff measurableSet_Ioi,
    Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi ha)]

def regularizedKernel (ε : ℝ) (x : Position) : ℝ :=
  (‖x‖^2+ε^2)^(-1/2 : ℝ)

def regularizedCharge (ε : ℝ) (x : Position) : ℝ :=
  3*ε^2*(‖x‖^2+ε^2)^(-5/2 : ℝ)

theorem contDiff_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedKernel ε) := by
  apply ContDiff.rpow_const_of_ne
  · exact (contDiff_norm_sq ℝ).add contDiff_const
  · intro x
    exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)).ne'

theorem laplacian_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) (x : Position) :
    coordinateLaplacian (regularizedKernel ε) x = -regularizedCharge ε x := by
  have hq : 0 < ‖x‖^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)
  have he : ∀ a : Fin 3, (fun t : ℝ => regularizedKernel ε (x+t • axis a)) =
      (fun t => ((‖x‖^2+ε^2)+2*t*x a+t^2)^(-1/2 : ℝ)) := by
    intro a
    ext t
    unfold regularizedKernel
    rw [norm_sq_axis_shift]
    congr 1
    ring
  unfold coordinateLaplacian
  simp_rw [he, second_deriv_quadratic_rpow hq]
  norm_num
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hpow : (‖x‖^2+ε^2)^(-5/2 : ℝ)*(‖x‖^2+ε^2) =
      (‖x‖^2+ε^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hq.ne']
    norm_num
  calc
    _ = 3*(‖x‖^2+ε^2)^(-5/2 : ℝ)*(∑ a : Fin 3, (x a)^2) -
        3*(‖x‖^2+ε^2)^(-3/2 : ℝ) := by
      rw [Finset.mul_sum]
      congr 1
      all_goals ring_nf
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      unfold regularizedCharge
      rw [← hpow]
      ring

def chargePrimitive (r : ℝ) : ℝ := r^3*(1+r^2)^(-3/2 : ℝ)

theorem hasDerivAt_chargePrimitive (r : ℝ) :
    HasDerivAt chargePrimitive (3*r^2*(1+r^2)^(-5/2 : ℝ)) r := by
  have hp : 0 < 1+r^2 := by positivity
  have hd := ((hasDerivAt_id r).pow 3).mul
    (((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)).rpow_const
      (p := (-3/2 : ℝ)) (Or.inl hp.ne'))
  unfold chargePrimitive
  apply hd.congr_deriv
  norm_num
  have he : (1+r^2)^(-5/2 : ℝ)*(1+r^2) = (1+r^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hp.ne']; norm_num
  norm_num at he
  rw [← he]
  ring

theorem chargePrimitive_eq_ratio {r : ℝ} (hr : 0 ≤ r) :
    chargePrimitive r = (1-(1+r^2)⁻¹)^(3/2 : ℝ) := by
  have hp : 0 < 1+r^2 := by positivity
  have hh : 1-(1+r^2)⁻¹ = r^2/(1+r^2) := by field_simp; ring
  rw [hh, Real.div_rpow (sq_nonneg _) hp.le]
  have hn : (r^2)^(3/2 : ℝ) = r^3 := by
    rw [← Real.rpow_natCast_mul hr]
    norm_num
  rw [hn]
  unfold chargePrimitive
  rw [show (-3/2:ℝ) = -(3/2:ℝ) by ring, Real.rpow_neg hp.le]
  rfl

theorem tendsto_chargePrimitive : Tendsto chargePrimitive atTop (𝓝 1) := by
  have hp : Tendsto (fun r : ℝ => 1+r^2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))
  have hi := tendsto_inv_atTop_zero.comp hp
  have hh := (tendsto_const_nhds.sub hi).rpow tendsto_const_nhds
    (Or.inl (by norm_num : (1:ℝ)-0 ≠ 0) : (1:ℝ)-0 ≠ 0 ∨ 0 < (3/2:ℝ))
  apply Filter.Tendsto.congr' _ (by simpa using hh)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  exact (chargePrimitive_eq_ratio hr).symm

theorem integrable_radial_regularizedCharge_one :
    IntegrableOn (fun r : ℝ => 3*r^2*(1+r^2)^(-5/2 : ℝ)) (Set.Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg' (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity) tendsto_chargePrimitive

theorem integral_radial_regularizedCharge_one :
    (∫ r : ℝ in Set.Ioi 0, 3*r^2*(1+r^2)^(-5/2 : ℝ)) = 1 := by
  have hder := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0:ℝ)) (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity : ∀ r ∈ Set.Ioi (0:ℝ), 0 ≤ 3*r^2*(1+r^2)^(-5/2 : ℝ))
    tendsto_chargePrimitive
  simpa [chargePrimitive] using hder

theorem regularizedCharge_one_eq : regularizedCharge 1 =
    fun x : Position => 3*(1+‖x‖^2)^(-5/2 : ℝ) := by
  ext x
  simp [regularizedCharge, add_comm]

theorem integrable_regularizedCharge_one : Integrable (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq, integrable_fun_norm_addHaar volume
    (f := fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simpa [finrank_euclideanSpace_fin, smul_eq_mul, mul_comm, mul_assoc,
    mul_left_comm] using integrable_radial_regularizedCharge_one

theorem integral_regularizedCharge_one : (∫ x, regularizedCharge 1 x) = 4*Real.pi := by
  rw [regularizedCharge_one_eq, integral_fun_norm_addHaar volume
    (fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]
  norm_num
  have hi : (∫ r : ℝ in Set.Ioi 0, r^2*(3*(1+r^2)^(-(5/2): ℝ))) = 1 := by
    simpa only [neg_div, mul_assoc, mul_comm, mul_left_comm] using
      integral_radial_regularizedCharge_one
  rw [hi]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,
    one_pow, one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  ring

theorem regularizedCharge_smul {ε : ℝ} (hε : 0 < ε) (x : Position) :
    regularizedCharge ε (ε • x) = (ε^3)⁻¹*regularizedCharge 1 x := by
  unfold regularizedCharge
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have he : (ε*‖x‖)^2+ε^2 = ε^2*(‖x‖^2+1) := by ring
  rw [he, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (ε^2)^(-5/2:ℝ) = (ε^5)⁻¹ := by
    rw [← Real.rpow_natCast_mul hε.le]
    norm_num [Real.rpow_neg hε.le]
  rw [hp]
  norm_num
  field_simp

theorem integral_regularizedCharge_scale {ε : ℝ} (hε : 0 < ε) (φ : Position → ℝ) :
    (∫ x, regularizedCharge ε x*φ x) = ∫ x, regularizedCharge 1 x*φ (ε • x) := by
  have hs := Measure.integral_comp_smul_of_nonneg volume
    (fun x => regularizedCharge ε x*φ x) ε (hR := hε.le)
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at hs
  have ht : (∫ x, regularizedCharge ε (ε • x)*φ (ε • x)) =
      (ε^3)⁻¹*(∫ x, regularizedCharge 1 x*φ (ε • x)) := by
    simp_rw [regularizedCharge_smul hε, mul_assoc]
    exact integral_const_mul _ _
  rw [ht] at hs
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hε.ne')) hs).symm

theorem regularizedCharge_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedCharge ε x := by unfold regularizedCharge; positivity

theorem continuous_regularizedCharge_one : Continuous (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq]
  apply Continuous.const_mul
  apply Continuous.rpow_const
  · fun_prop
  · intro x
    left
    positivity

theorem regularizedCharge_tendsto_dirac {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedCharge (ε n) x*φ x)
      atTop (𝓝 (4*Real.pi*φ 0)) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hD := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure Position)) (fun x => regularizedCharge 1 x*C)
    (F := fun n x => regularizedCharge 1 x*φ (ε n • x))
    (f := fun x => regularizedCharge 1 x*φ 0)
    (fun n => (continuous_regularizedCharge_one.mul
      (hφ.comp (show Continuous (fun x : Position => ε n • x) by fun_prop))).aestronglyMeasurable)
    (integrable_regularizedCharge_one.mul_const C)
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedCharge_nonneg 1 x)]
      exact mul_le_mul_of_nonneg_left (hC _) (regularizedCharge_nonneg 1 x)))
    (Filter.Eventually.of_forall (fun x => by
      have he : Tendsto (fun n => ε n • x) atTop (𝓝 (0 : Position)) := by
        simpa using hlim.smul_const x
      exact tendsto_const_nhds.mul (hφ.continuousAt.tendsto.comp he)))
  simp only [integral_mul_const, integral_regularizedCharge_one] at hD
  simpa only [integral_regularizedCharge_scale (hε _)] using hD

theorem locallyIntegrable_coulombKernel : LocallyIntegrable coulombKernel volume := by
  intro x
  refine ⟨Metric.ball 0 (‖x‖+1), IsOpen.mem_nhds Metric.isOpen_ball ?_,
    coulombKernel_integrableOn_ball _⟩
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖

theorem coulombKernel_eq_rpow (x : Position) :
    coulombKernel x = (‖x‖^2)^(-1/2 : ℝ) := by
  rw [← Real.rpow_natCast_mul (norm_nonneg x)]
  norm_num [coulombKernel, Real.rpow_neg_one]

theorem regularizedKernel_le {ε : ℝ} {x : Position} (hx : x ≠ 0) :
    regularizedKernel ε x ≤ coulombKernel x := by
  rw [coulombKernel_eq_rpow]
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (le_add_of_nonneg_right (sq_nonneg ε)) (by norm_num)

theorem regularizedKernel_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedKernel ε x := by unfold regularizedKernel; positivity

theorem regularizedKernel_tendsto {ε : ℕ → ℝ} (hlim : Tendsto ε atTop (𝓝 0))
    {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => regularizedKernel (ε n) x) atTop (𝓝 (coulombKernel x)) := by
  have hh : Tendsto (fun n => ‖x‖^2+(ε n)^2) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add (hlim.pow 2)
  have hr := hh.rpow tendsto_const_nhds
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)) : ‖x‖^2 ≠ 0 ∨ 0 < (-1/2:ℝ))
  simpa only [regularizedKernel, coulombKernel_eq_rpow] using hr

theorem regularizedKernel_integral_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedKernel (ε n) x*φ x)
      atTop (𝓝 (∫ x, coulombKernel x*φ x)) := by
  have hae : ∀ᵐ x : Position ∂volume, x ≠ 0 := volume.ae_ne 0
  have hb : Integrable (fun x => coulombKernel x*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => coulombKernel x*‖φ x‖)
  · intro n
    exact ((contDiff_regularizedKernel (hε n).ne').continuous.mul hφ).aestronglyMeasurable
  · exact hb
  · intro n
    filter_upwards [hae] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedKernel_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right (regularizedKernel_le hx) (norm_nonneg _)
  · filter_upwards [hae] with x hx
    exact (regularizedKernel_tendsto hlim hx).mul_const (φ x)

theorem integral_coulombKernel_laplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, coulombKernel x*coordinateLaplacian φ x) = -(4*Real.pi*φ 0) := by
  let ε : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hleft := regularizedKernel_integral_tendsto hε hεlim
    (continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)))
    (hasCompactSupport_coordinateLaplacian hφc)
  have hright := (regularizedCharge_tendsto_dirac hε hεlim hφ.continuous hφc).neg
  have he : (fun n => ∫ x, regularizedKernel (ε n) x*coordinateLaplacian φ x) =
      (fun n => -(∫ x, regularizedCharge (ε n) x*φ x)) := by
    funext n
    rw [integral_mul_coordinateLaplacian_eq
      (fun x _ => ((contDiff_regularizedKernel (hε n).ne').of_le
        (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt) hφ hφc]
    simp_rw [laplacian_regularizedKernel (hε n).ne', neg_mul, integral_neg]
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

theorem integrable_coulomb_test_product {ρ φ : Position → ℝ}
    (hρ : Integrable ρ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z : Position × Position => coulombKernel (z.1-z.2)*ρ z.2*φ z.1)
      (volume.prod volume) := by
  let k : Position → ℝ := (Metric.ball 0 1).indicator coulombKernel
  have hk : Integrable k :=
    (coulombKernel_integrableOn_ball 1).integrable_indicator measurableSet_ball
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hn : Integrable (fun z : Position × Position => ‖ρ z.2‖*k (z.1-z.2))
      (volume.prod volume) := by
    simpa using hρ.norm.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hk
  have hf : Integrable (fun z : Position × Position => ‖φ z.1‖*‖ρ z.2‖)
      (volume.prod volume) := hφ.integrable_of_hasCompactSupport hφc |>.norm.mul_prod hρ.norm
  have hm : AEStronglyMeasurable
      (fun z : Position × Position => coulombKernel (z.1-z.2)*ρ z.2*φ z.1)
      (volume.prod volume) := by
    have hh := hρ.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) measurable_coulombKernel.aestronglyMeasurable
    have hh' : AEStronglyMeasurable
        (fun z : Position × Position => ρ z.2*coulombKernel (z.1-z.2)*φ z.1)
        (volume.prod volume) := hh.mul hφ.aestronglyMeasurable.comp_fst
    convert hh' using 1
    ext z
    ring
  refine Integrable.mono' ((hn.const_mul C).add hf) hm (Filter.Eventually.of_forall ?_)
  intro z
  have hK : coulombKernel (z.1-z.2) ≤ k (z.1-z.2)+1 := by
    by_cases hz : z.1-z.2 ∈ Metric.ball (0 : Position) 1
    · simp only [k, Set.indicator_of_mem hz]
      linarith
    · have hl : 1 ≤ ‖z.1-z.2‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz
      have hh : ‖z.1-z.2‖⁻¹ ≤ (1:ℝ) := by simpa using inv_anti₀ (by norm_num : (0:ℝ)<1) hl
      simpa only [k, Set.indicator_of_notMem hz, zero_add, coulombKernel] using hh
  have hkpos : 0 ≤ k (z.1-z.2) := Set.indicator_nonneg (fun x _ => coulombKernel_nonneg x) _
  rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (coulombKernel_nonneg _)]
  calc
    coulombKernel (z.1-z.2)*‖ρ z.2‖*‖φ z.1‖ ≤
        (k (z.1-z.2)+1)*‖ρ z.2‖*‖φ z.1‖ := by gcongr
    _ = ‖ρ z.2‖*k (z.1-z.2)*‖φ z.1‖+‖φ z.1‖*‖ρ z.2‖ := by ring
    _ ≤ C*(‖ρ z.2‖*k (z.1-z.2))+‖φ z.1‖*‖ρ z.2‖ := by
      nlinarith [mul_nonneg (norm_nonneg (ρ z.2)) hkpos,
        mul_le_mul_of_nonneg_left (hC z.1) (mul_nonneg (norm_nonneg (ρ z.2)) hkpos)]

theorem coordinateLaplacian_translate (φ : Position → ℝ) (x y : Position) :
    coordinateLaplacian (fun z => φ (z+y)) x = coordinateLaplacian φ (x+y) := by
  unfold coordinateLaplacian
  simp only [add_right_comm _ _ y]

theorem integral_translated_coulombKernel_laplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (y : Position) :
    (∫ x, coulombKernel (x-y)*coordinateLaplacian φ x) = -(4*Real.pi*φ y) := by
  have ht : ContDiff ℝ ∞ (fun z => φ (z+y)) := hφ.comp (contDiff_id.add contDiff_const)
  have hc : HasCompactSupport (fun z => φ (z+y)) :=
    hφc.comp_homeomorph (Homeomorph.addRight y)
  have he := integral_coulombKernel_laplacian ht hc
  simp only [coordinateLaplacian_translate, zero_add] at he
  rw [← integral_add_right_eq_self (fun x => coulombKernel (x-y)*coordinateLaplacian φ x) y]
  simpa only [add_sub_cancel_right] using he

theorem potentialOf_weakLaplacian {ρ : Position → ℝ} (hρ : Integrable ρ) :
    HasWeakLaplacian (potentialOf ρ) Set.univ (fun x => -(4*Real.pi)*ρ x) := by
  intro φ hφ hφc _
  have hL : Continuous (coordinateLaplacian φ) :=
    continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  calc
    (∫ x, potentialOf ρ x*coordinateLaplacian φ x) =
        ∫ x, ∫ y, coulombKernel (x-y)*ρ y*coordinateLaplacian φ x := by
      simp only [potentialOf, integral_mul_const]
    _ = ∫ y, ∫ x, coulombKernel (x-y)*ρ y*coordinateLaplacian φ x :=
      integral_integral_swap (integrable_coulomb_test_product hρ hL
        (hasCompactSupport_coordinateLaplacian hφc))
    _ = ∫ y, (-(4*Real.pi)*ρ y)*φ y := by
      apply integral_congr_ae
      filter_upwards [] with y
      calc
        (∫ x, coulombKernel (x-y)*ρ y*coordinateLaplacian φ x) =
            (∫ x, coulombKernel (x-y)*coordinateLaplacian φ x)*ρ y := by
          simp only [mul_right_comm _ (ρ y), integral_mul_const]
        _ = _ := by rw [integral_translated_coulombKernel_laplacian hφ hφc]; ring

theorem bounded_density_convolution {k ρ : Position → ℝ} {A : ℝ}
    (hk : Measurable k) (hkpos : ∀ x, 0 ≤ k x)
    (hki : IntegrableOn k (Metric.ball 0 1))
    (hkfar : ∀ x, 1 ≤ ‖x‖ → k x ≤ 1)
    (hρ : Integrable ρ) (hρpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) (x : Position) :
    Integrable (fun y => k (x-y)*ρ y) ∧
      (∫ y, k (x-y)*ρ y) ≤ A*(∫ y in Metric.ball 0 1, k y)+(∫ y, ρ y) := by
  let kn := (Metric.ball (0 : Position) 1).indicator k
  have hi : Integrable (fun y => kn (x-y)) :=
    (integrable_comp_sub_left kn x).mpr (hki.integrable_indicator measurableSet_ball)
  have hb : Integrable (fun y => A*kn (x-y)+ρ y) := (hi.const_mul A).add hρ
  have hd : ∀ y, k (x-y)*ρ y ≤ A*kn (x-y)+ρ y := by
    intro y
    by_cases hy : x-y ∈ Metric.ball (0 : Position) 1
    · simp only [kn, Set.indicator_of_mem hy]
      nlinarith [mul_le_mul_of_nonneg_left (hA y) (hkpos (x-y)), hρpos y]
    · simp only [kn, Set.indicator_of_notMem hy, mul_zero, zero_add]
      have hh : 1 ≤ ‖x-y‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hy
      simpa using mul_le_mul_of_nonneg_right (hkfar _ hh) (hρpos y)
  have hm : AEStronglyMeasurable (fun y => k (x-y)*ρ y) volume :=
    (hk.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hρ.aestronglyMeasurable
  have hp : Integrable (fun y => k (x-y)*ρ y) :=
    hb.mono' hm (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hkpos _) (hρpos _))]
      exact hd y))
  refine ⟨hp, (integral_mono hp hb hd).trans_eq ?_⟩
  rw [integral_add (hi.const_mul A) hρ, integral_const_mul, integral_sub_left_eq_self]
  rw [integral_indicator measurableSet_ball]

end NeutralAtom
end
end
end

end OAI
