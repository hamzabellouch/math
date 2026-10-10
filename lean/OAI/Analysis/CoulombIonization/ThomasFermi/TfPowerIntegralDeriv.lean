import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.Pairing

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma tf_power_integral_hasDerivAt {f h : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hh : MemLp h (5 / 3) μ) :
    HasDerivAt (fun t : ℝ => ∫ x, |f x + t * h x| ^ (5 / 3 : ℝ) ∂μ)
      (∫ x, tfPowerDerivative (f x) * h x ∂μ) 0 := by
  have hsum : MemLp (fun x => |f x| + |h x|) (5 / 3) μ := hf.norm.add hh.norm
  have hbound : Integrable (fun x => (5 / 3 : ℝ) * (|f x| + |h x|) ^ (5 / 3 : ℝ)) μ :=
    (tf_integrable hsum (Eventually.of_forall fun x => add_nonneg (abs_nonneg _) (abs_nonneg _))).const_mul _
  have hi := hf.integrable_norm_rpow (by norm_num : (5 / 3 : ENNReal) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
  norm_num at hi
  have hmeas : AEStronglyMeasurable (fun x => tfPowerDerivative (f x) * h x) μ := by
    unfold tfPowerDerivative
    exact ((((hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable.const_mul
      _).mul hf.aestronglyMeasurable).mul hh.aestronglyMeasurable)
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t : ℝ => fun x => |f x + t * h x| ^ (5 / 3 : ℝ))
    (F' := fun t : ℝ => fun x => tfPowerDerivative (f x + t * h x) * h x)
    (s := ball (0 : ℝ) 1) (ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun t =>
      (((hf.aestronglyMeasurable.add (hh.aestronglyMeasurable.const_mul t)).norm.aemeasurable).pow_const
        _).aestronglyMeasurable)
    (by simpa using hi) (by simpa using hmeas)
    (Eventually.of_forall fun x t ht => tfPowerDerivative_bound (f x) (h x) t
      (le_of_lt (by simpa [Real.dist_eq] using ht))) hbound
    (Eventually.of_forall fun x t _ => hasDerivAt_tfPower (f x) (h x) t)
  simpa using hD.2

lemma tfPowerDerivative_mul_integrable {f h : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hh : MemLp h (5 / 3) μ) : Integrable (fun x => tfPowerDerivative (f x) * h x) μ := by
  have hsum : MemLp (fun x => |f x| + |h x|) (5 / 3) μ := hf.norm.add hh.norm
  have hi := (tf_integrable hsum (Eventually.of_forall fun x =>
    add_nonneg (abs_nonneg _) (abs_nonneg _))).const_mul (5 / 3 : ℝ)
  apply hi.mono'
  · unfold tfPowerDerivative
    exact ((((hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable.const_mul
      _).mul hf.aestronglyMeasurable).mul hh.aestronglyMeasurable)
  · exact Eventually.of_forall fun x => by simpa using tfPowerDerivative_bound (f x) (h x) 0 (by norm_num)

lemma tfLp_kinetic_hasDerivAt (f h : TFLp μ) :
    HasDerivAt (fun t : ℝ => ‖f + t • h‖ ^ (5 / 3 : ℝ))
      (∫ x, tfPowerDerivative (f x) * h x ∂μ) 0 := by
  have he (t : ℝ) : ‖f + t • h‖ ^ (5 / 3 : ℝ) =
      ∫ x, |f x + t * h x| ^ (5 / 3 : ℝ) ∂μ := by
    rw [tfLp_norm_rpow]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f (t • h), Lp.coeFn_smul t h] with x ha hs
    simp only [ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul]
  simp_rw [he]
  exact tf_power_integral_hasDerivAt (Lp.memLp f) (Lp.memLp h)

end

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal


lemma tfBallFunctional_hasDerivAt (R T Z η : ℝ) (f h : TFLp (ballMeasure R)) :
    HasDerivAt (fun t : ℝ => tfBallFunctional R T Z η (f + t • h))
      (T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
        tfBallLinear R Z η h + tfCoulombL R f h) 0 := by
  have he (t : ℝ) : tfBallFunctional R T Z η (f + t • h) =
      T * ‖f + t • h‖ ^ (5 / 3 : ℝ) +
        (tfBallLinear R Z η f + t * tfBallLinear R Z η h) +
        (1 / 2 : ℝ) * (tfCoulombL R f f + 2 * t * tfCoulombL R f h +
          t * t * tfCoulombL R h h) := by
    simp only [tfBallFunctional, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    rw [tfCoulombL_symmetric R h f]
    ring
  simp_rw [he]
  have hk := (tfLp_kinetic_hasDerivAt f h).const_mul T
  have hl := (((hasDerivAt_id (0 : ℝ)).mul_const (tfBallLinear R Z η h)).const_add (tfBallLinear R Z η f))
  have hq := ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (tfCoulombL R f h)).const_add
    (tfCoulombL R f f)).add (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (tfCoulombL R h h))
  convert! (hk.add hl).add (hq.const_mul (1 / 2 : ℝ)) using 1
  simp only [id_eq]
  ring

lemma hasDerivAt_nonneg_of_right_min {F : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt F d 0)
    (hmin : ∀ t : ℝ, 0 ≤ t → F 0 ≤ F t) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hmin t ht.le))

lemma tfBallFunctional_variation_nonneg (R T Z η : ℝ) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g)
    {h : TFLp (ballMeasure R)} (hh : NonnegDensity h) :
    0 ≤ T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
      tfBallLinear R Z η h + tfCoulombL R f h := by
  apply hasDerivAt_nonneg_of_right_min (tfBallFunctional_hasDerivAt R T Z η f h)
  intro t ht
  simpa using hmin (f + t • h) (nonnegDensity_add hf (nonnegDensity_smul hh ht))

lemma tfBallFunctional_variation_self (R T Z η : ℝ) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g) :
    T * (∫ x, tfPowerDerivative (f x) * f x ∂ballMeasure R) +
      tfBallLinear R Z η f + tfCoulombL R f f = 0 := by
  apply IsLocalMin.hasDerivAt_eq_zero (f := fun t : ℝ => tfBallFunctional R T Z η (f + t • f))
    _ (tfBallFunctional_hasDerivAt R T Z η f f)
  have hm : Ioi (-1 : ℝ) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by norm_num)
  filter_upwards [hm] with t ht
  have hn : NonnegDensity (f + t • f) := by
    rw [show f + t • f = (1 + t) • f by rw [add_smul, one_smul]]
    exact nonnegDensity_smul hf (by change -1 < t at ht; linarith)
  simpa using hmin _ hn

def tfBallPotential (R : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) : ℝ :=
  ∫ y, f y / ‖x - y‖ ∂ballMeasure R

lemma tfBallPotential_integrable (R : ℝ) (f : TFLp (ballMeasure R)) :
    Integrable (tfBallPotential R f) (ballMeasure R) := by
  have hm := tf_memLp_prod (μ := ballMeasure R) (memLp_const (1 : ℝ)) (Lp.memLp f)
  have hi := (coulomb_memLp R).integrable_mul hm
  have hi' : Integrable (fun p : TFSpace × TFSpace => f p.2 / ‖p.1 - p.2‖)
      ((ballMeasure R).prod (ballMeasure R)) := by
    apply hi.congr (Eventually.of_forall fun p => ?_)
    dsimp only [Pi.mul_apply]
    ring
  exact hi'.integral_prod_left

lemma tfCoulombL_potential (R : ℝ) (f h : TFLp (ballMeasure R)) :
    tfCoulombL R f h = ∫ x, tfBallPotential R f x * h x ∂ballMeasure R := by
  rw [tfCoulombL_symmetric R f h, tfCoulombL_apply, integral_prod _ (tfCoulomb_integrable R h f)]
  apply integral_congr_ae (Eventually.of_forall fun x => ?_)
  rw [mul_comm (tfBallPotential R f x)]
  unfold tfBallPotential
  rw [← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only [tfBallPotential]
  ring

lemma tfBallPotential_mul_integrable (R : ℝ) (f h : TFLp (ballMeasure R)) :
    Integrable (fun x => tfBallPotential R f x * h x) (ballMeasure R) := by
  have hi := (tfCoulomb_integrable R h f).integral_prod_left
  convert hi using 1
  ext x
  rw [mul_comm (tfBallPotential R f x)]
  unfold tfBallPotential
  rw [← integral_const_mul]
  congr 1
  ext y
  ring

def tfBallGradient (R T Z η : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) : ℝ :=
  T * tfPowerDerivative (f x) + η - Z / ‖x‖ + tfBallPotential R f x

lemma tfBallGradient_integrable (R T Z η : ℝ) (f : TFLp (ballMeasure R)) :
    Integrable (tfBallGradient R T Z η f) (ballMeasure R) := by
  have hi : Integrable (fun x => tfPowerDerivative (f x)) (ballMeasure R) := by
    simpa only [mul_one] using tfPowerDerivative_mul_integrable (Lp.memLp f) (memLp_const (1 : ℝ))
  have hn : Integrable (fun x : TFSpace => Z / ‖x‖) (ballMeasure R) := by
    simpa only [div_eq_mul_inv] using ((nuclear_memLp R).integrable (Fact.out : (1 : ENNReal) ≤ 5 / 2)).const_mul Z
  exact (((hi.const_mul T).add (integrable_const η)).sub hn).add (tfBallPotential_integrable R f)

lemma tfBallGradient_mul_integrable (R T Z η : ℝ) (f h : TFLp (ballMeasure R)) :
    Integrable (fun x => tfBallGradient R T Z η f x * h x) (ballMeasure R) := by
  have hi := (tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp h)).const_mul T
  have hc := ((Lp.memLp h).integrable (Fact.out : (1 : ENNReal) ≤ 5 / 3)).const_mul η
  have hn := (tfPairing_integrable _ (nuclear_memLp R) h).const_mul Z
  apply (((hi.add hc).sub hn).add (tfBallPotential_mul_integrable R f h)).congr
  exact Eventually.of_forall fun x => by dsimp [tfBallGradient]; ring

lemma tfBallGradient_pair (R T Z η : ℝ) (f h : TFLp (ballMeasure R)) :
    (∫ x, tfBallGradient R T Z η f x * h x ∂ballMeasure R) =
      T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
        tfBallLinear R Z η h + tfCoulombL R f h := by
  have hi := (tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp h)).const_mul T
  have hc := ((Lp.memLp h).integrable (Fact.out : (1 : ENNReal) ≤ 5 / 3)).const_mul η
  have hn := (tfPairing_integrable _ (nuclear_memLp R) h).const_mul Z
  have he : (fun x => tfBallGradient R T Z η f x * h x) =
      (fun x => T * (tfPowerDerivative (f x) * h x) + η * h x - Z * (‖x‖⁻¹ * h x) +
        tfBallPotential R f x * h x) := by
    ext x
    dsimp only [tfBallGradient]
    ring
  rw [he, integral_add ((hi.fun_add hc).sub' hn) (tfBallPotential_mul_integrable R f h),
    integral_sub (hi.fun_add hc) hn, integral_add hi hc]
  simp only [integral_const_mul, tfBallLinear, sub_apply, smul_apply, smul_eq_mul,
    tfPairing_apply, one_mul, tfCoulombL_potential]
  ring

lemma tfBallGradient_nonneg (R T Z η : ℝ) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g) :
    ∀ᵐ x ∂ballMeasure R, 0 ≤ tfBallGradient R T Z η f x := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (tfBallGradient_integrable R T Z η f)
  intro s hs _
  let hm : MemLp (s.indicator (fun _ : TFSpace => (1 : ℝ))) (5 / 3) (ballMeasure R) :=
    (memLp_const 1).indicator hs
  let h := hm.toLp (s.indicator (fun _ : TFSpace => (1 : ℝ)))
  have hcoe : (fun x => h x) =ᵐ[ballMeasure R] s.indicator (fun _ => (1 : ℝ)) := hm.coeFn_toLp
  have hh : NonnegDensity h := by
    filter_upwards [hcoe] with x hx
    rw [hx]
    exact indicator_nonneg (fun _ _ => zero_le_one) x
  have hp := tfBallFunctional_variation_nonneg R T Z η hf hmin hh
  rw [← tfBallGradient_pair] at hp
  have he : (fun x => tfBallGradient R T Z η f x * h x) =ᵐ[ballMeasure R]
      s.indicator (tfBallGradient R T Z η f) := by
    filter_upwards [hcoe] with x hx
    rw [hx]
    by_cases hx' : x ∈ s <;> simp [hx']
  rwa [integral_congr_ae he, integral_indicator hs] at hp

lemma tfBallGradient_complementarity (R T Z η : ℝ) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g) :
    ∀ᵐ x ∂ballMeasure R, tfBallGradient R T Z η f x * f x = 0 := by
  have hn : ∀ᵐ x ∂ballMeasure R, 0 ≤ tfBallGradient R T Z η f x * f x := by
    filter_upwards [hf, tfBallGradient_nonneg R T Z η hf hmin] with x hfx hgx
    exact mul_nonneg hgx hfx
  apply (integral_eq_zero_iff_of_nonneg_ae hn (tfBallGradient_mul_integrable R T Z η f f)).mp
  rw [tfBallGradient_pair]
  exact tfBallFunctional_variation_self R T Z η hf hmin

theorem tfBallFunctional_euler (R Z η : ℝ) {T : ℝ} (hT : 0 < T)
    {f : TFLp (ballMeasure R)} (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g) :
    ∀ᵐ x ∂ballMeasure R, f x =
      (max (Z / ‖x‖ - tfBallPotential R f x - η) 0 / ((5 / 3 : ℝ) * T)) ^ (3 / 2 : ℝ) := by
  have hA : 0 < (5 / 3 : ℝ) * T := mul_pos (by norm_num) hT
  filter_upwards [hf, tfBallGradient_nonneg R T Z η hf hmin,
    tfBallGradient_complementarity R T Z η hf hmin] with x hfx hgx hcx
  have he : (5 / 3 : ℝ) * T * (f x) ^ (2 / 3 : ℝ) = max (Z / ‖x‖ - tfBallPotential R f x - η) 0 := by
    dsimp only [tfBallGradient] at hgx hcx
    rw [tfPowerDerivative_nonneg hfx] at hgx hcx
    by_cases hf0 : f x = 0
    · simp only [hf0, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), mul_zero, zero_add] at hgx ⊢
      rw [max_eq_right (by linarith)]
    · have hz := (mul_eq_zero.mp hcx).resolve_right hf0
      have hp := Real.rpow_nonneg hfx (2 / 3 : ℝ)
      have hxmax : 0 ≤ Z / ‖x‖ - tfBallPotential R f x - η := by nlinarith
      rw [max_eq_left hxmax]
      nlinarith
  have hdiv : (f x) ^ (2 / 3 : ℝ) = max (Z / ‖x‖ - tfBallPotential R f x - η) 0 / ((5 / 3 : ℝ) * T) :=
    (eq_div_iff hA.ne').mpr (by nlinarith [he])
  rw [← hdiv, ← Real.rpow_mul hfx]
  norm_num


open MeasureTheory Filter
open scoped Topology BigOperators Pointwise

end CoulombAnalysis

end

end OAI
