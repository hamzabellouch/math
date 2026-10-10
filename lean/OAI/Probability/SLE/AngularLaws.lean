import Mathlib
import OAI.Probability.SLE.RadiusClocks

namespace OAI

/-! Angular Laws for chordal SLE. -/

section
section
section
open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian ENNReal
namespace SLEExactGauge
noncomputable def greenInner (n : ℕ) : ℝ := (1 / 2) * (1 / ((n : ℝ) + 1))
noncomputable def greenOuter (n : ℕ) : ℝ := 1 - greenInner n

lemma greenInner_pos (n : ℕ) : 0 < greenInner n := by unfold greenInner; positivity

lemma greenInner_le_half (n : ℕ) : greenInner n ≤ 1 / 2 := by
  unfold greenInner
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hh : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr hn
  linarith

lemma greenInner_le_outer (n : ℕ) : greenInner n ≤ greenOuter n := by
  unfold greenOuter
  linarith [greenInner_le_half n]

lemma greenOuter_pos (n : ℕ) : 0 < greenOuter n :=
  (greenInner_pos n).trans_le (greenInner_le_outer n)

lemma greenOuter_lt_one (n : ℕ) : greenOuter n < 1 := by
  unfold greenOuter
  linarith [greenInner_pos n]

lemma greenInner_tendsto : Tendsto greenInner atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1 / 2) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0)
  simpa only [greenInner, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)

lemma greenOuter_tendsto : Tendsto greenOuter atTop (𝓝 1) := by
  change Tendsto (fun n => 1 - greenInner n) atTop (𝓝 1)
  simpa only [greenOuter, sub_zero] using tendsto_const_nhds.sub greenInner_tendsto

lemma greenInner_log_tendsto : Tendsto (fun n => -greenInner n * Real.log (greenInner n)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, zero_mul, neg_zero, neg_mul] using
    ((Real.continuous_mul_log.tendsto 0).comp greenInner_tendsto).neg

def polarUnitDisk : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo (-Real.pi) Real.pi

noncomputable def polarGreenTarget (u : ℂ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  polarUnitDisk.indicator (fun p : ℝ × ℝ =>
    ENNReal.ofReal (p.1 * (-Real.log p.1) * (-(Δ u) (polarPoint p.1 p.2)))) p

lemma greenTruncation_tendsto {u : ℂ → ℝ} {p : ℝ × ℝ} (hp : p ∈ polarUnitDisk) :
    Tendsto (fun n => ENNReal.ofReal (greenTruncation u (greenInner n) (greenOuter n) p)) atTop
      (𝓝 (ENNReal.ofReal (p.1 * (-Real.log p.1) * (-(Δ u) (polarPoint p.1 p.2))))) := by
  have he : ∀ᶠ n in atTop, greenTruncation u (greenInner n) (greenOuter n) p =
      p.1 * (Real.log (greenOuter n) - Real.log p.1) * (-(Δ u) (polarPoint p.1 p.2)) := by
    filter_upwards [greenInner_tendsto (Iio_mem_nhds hp.1.1),
      greenOuter_tendsto (Ioi_mem_nhds hp.1.2)] with n ha hR
    have hm : p ∈ greenRectangle (greenInner n) (greenOuter n) :=
      ⟨⟨ha.le, hR.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
    simp only [greenTruncation, indicator_of_mem hm, annulusDensity]
  have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp greenOuter_tendsto
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (((hl.sub_const (Real.log p.1)).const_mul p.1).mul_const
      (-(Δ u) (polarPoint p.1 p.2)))
  simp only [Function.comp_def, Real.log_one, zero_sub] at ht
  exact ht.congr' (he.mono fun n hn => congrArg ENNReal.ofReal hn.symm)

 

lemma polar_green_le {u : ℂ → ℝ} {C : ℝ}
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z)
    (hun : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z)
    (hub : ∀ z ∈ ball (0 : ℂ) 1, u z ≤ C)
    (hΔ : ∀ z ∈ ball (0 : ℂ) 1, (Δ u) z ≤ 0) :
    (∫⁻ p, polarGreenTarget u p) ≤ ENNReal.ofReal (2 * Real.pi * C) := by
  let F : ℕ → ℝ × ℝ → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (greenTruncation u (greenInner n) (greenOuter n) p)
  have hmeas (n : ℕ) : AEMeasurable (F n) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (greenTruncation_integrable (greenInner_pos n) (greenOuter_lt_one n) hu).aemeasurable
  have hp : polarGreenTarget u ≤ fun p => liminf (fun n => F n p) atTop := by
    intro p
    by_cases hp : p ∈ polarUnitDisk
    · rw [polarGreenTarget, indicator_of_mem hp]
      exact le_of_eq (greenTruncation_tendsto (u := u) hp).liminf_eq.symm
    · simp only [polarGreenTarget, indicator_of_notMem hp]
      exact bot_le
  rcases derivative_locally_bounded (hu 0 (by simp)) with ⟨δ, M, hδ, hM, hgrad⟩
  have hbound : ∀ᶠ n in atTop, (∫⁻ p, F n p) ≤
      ENNReal.ofReal (2 * Real.pi * (C + M * (-greenInner n * Real.log (greenInner n)))) := by
    filter_upwards [greenInner_tendsto (Iio_mem_nhds hδ)] with n hn
    change greenInner n < δ at hn
    exact greenTruncation_lintegral_le (greenInner_pos n) (greenInner_le_outer n)
      (greenOuter_lt_one n) hu hun hub hΔ hM (fun θ => hgrad _ (by
        simpa only [polarPoint_norm, abs_of_pos (greenInner_pos n)] using hn))
  have ht : Tendsto (fun n => ENNReal.ofReal
      (2 * Real.pi * (C + M * (-greenInner n * Real.log (greenInner n))))) atTop
      (𝓝 (ENNReal.ofReal (2 * Real.pi * C))) := by
    simpa only [Function.comp_def, mul_zero, add_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds.add (greenInner_log_tendsto.const_mul M)).const_mul (2 * Real.pi))
  exact (lintegral_mono hp).trans ((lintegral_liminf_le' hmeas).trans
    ((liminf_le_liminf hbound).trans_eq ht.liminf_eq))

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

lemma polarPoint_eq_polarCoord (p : ℝ × ℝ) :
    polarPoint p.1 p.2 = Complex.polarCoord.symm p := by
  rw [polarPoint_eq_circleMap]
  apply Complex.ext
  · simp [circleMap_zero_re, Complex.polarCoord_symm_apply, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  · simp [circleMap_zero_im, Complex.polarCoord_symm_apply, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

lemma disk_log_lintegral_polar (h : ℂ → ℝ) :
    (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal ((-Real.log ‖z‖) * h z)) =
      ∫⁻ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (p.1 * (-Real.log p.1) * h (polarPoint p.1 p.2)) := by
  let T : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi
  let S : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo (-Real.pi) Real.pi
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioo
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hST : S ⊆ T := prod_mono Ioo_subset_Ioi_self subset_rfl
  let f : ℂ → ℝ≥0∞ := (ball (0 : ℂ) 1).indicator (fun z => ENNReal.ofReal ((-Real.log ‖z‖) * h z))
  calc
    _ = ∫⁻ z, f z := (lintegral_indicator measurableSet_ball _).symm
    _ = ∫⁻ p in T, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) :=
      (Complex.lintegral_comp_polarCoord_symm f).symm
    _ = ∫⁻ p in T, S.indicator (fun p : ℝ × ℝ =>
        ENNReal.ofReal (p.1 * (-Real.log p.1) * h (polarPoint p.1 p.2))) p := by
      apply setLIntegral_congr_fun hT
      intro p hp
      have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
      by_cases hr : p.1 < 1
      · have hz : Complex.polarCoord.symm p ∈ ball (0 : ℂ) 1 := by
          rw [mem_ball_zero_iff, hn]
          exact hr
        have hs : p ∈ S := ⟨⟨hp.1, hr⟩, hp.2⟩
        simp only [f, indicator_of_mem hz, indicator_of_mem hs, hn, smul_eq_mul,
          polarPoint_eq_polarCoord, ← ENNReal.ofReal_mul hp.1.le, mul_assoc]
      · have hz : Complex.polarCoord.symm p ∉ ball (0 : ℂ) 1 := by
          simpa only [mem_ball_zero_iff, hn] using hr
        have hs : p ∉ S := fun hs => hr hs.1.2
        simp only [f, indicator_of_notMem hz, indicator_of_notMem hs, smul_zero]
    _ = _ := by
      rw [lintegral_indicator hS, Measure.restrict_restrict hS, inter_eq_left.mpr hST]

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian ENNReal
namespace SLEExactGauge

 
lemma disk_green_le {u : ℂ → ℝ} {C : ℝ}
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z)
    (hun : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z)
    (hub : ∀ z ∈ ball (0 : ℂ) 1, u z ≤ C)
    (hΔ : ∀ z ∈ ball (0 : ℂ) 1, (Δ u) z ≤ 0) :
    (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal ((-Real.log ‖z‖) * (-(Δ u) z))) ≤
      ENNReal.ofReal (2 * Real.pi * C) := by
  rw [disk_log_lintegral_polar]
  have hh := polar_green_le hu hun hub hΔ
  simpa only [polarGreenTarget, polarUnitDisk,
    lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)] using hh

end SLEExactGauge

end

 
section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
namespace SLEExactGauge

lemma second_direction_chain {f : ℝ → ℝ} {g : ℂ → ℝ} {z : ℂ}
    (hg : ContDiffAt ℝ 2 g z) (hf : ContDiffAt ℝ 2 f (g z)) (v : ℂ) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) z v v =
      deriv (deriv f) (g z) * (fderiv ℝ g z v) ^ 2 +
        deriv f (g z) * fderiv ℝ (fderiv ℝ g) z v v := by
  have hgd : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hfdd : DifferentiableAt ℝ (deriv f) (g z) :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgdd : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcompdd : DifferentiableAt ℝ (fderiv ℝ (f ∘ g)) z :=
    ((hf.comp z hg).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun w => fderiv ℝ (f ∘ g) w v) =ᶠ[𝓝 z]
      (fun w => deriv f (g w) * fderiv ℝ g w v) := by
    filter_upwards [hg.eventually (by norm_num),
      hgd.continuousAt (hf.eventually (by norm_num))] with w hgw hfw
    change ContDiffAt ℝ 2 f (g w) at hfw
    rw [fderiv_comp w (hfw.differentiableAt (by norm_num)) (hgw.differentiableAt (by norm_num)),
      ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul, mul_comm]
  have hleft : fderiv ℝ (fun w => fderiv ℝ (f ∘ g) w v) z v =
      fderiv ℝ (fderiv ℝ (f ∘ g)) z v v := by
    rw [fderiv_clm_apply hcompdd (differentiableAt_const v)]
    simp
  have hright : fderiv ℝ (fun w => deriv f (g w) * fderiv ℝ g w v) z v =
      deriv (deriv f) (g z) * (fderiv ℝ g z v) ^ 2 +
        deriv f (g z) * fderiv ℝ (fderiv ℝ g) z v v := by
    have hmul := fderiv_fun_mul (hfdd.comp z hgd) (hgdd.clm_apply (differentiableAt_const v))
    simp only [Function.comp_apply] at hmul
    rw [hmul]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [fderiv_comp z hfdd hgd, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv,
      fderiv_clm_apply hgdd (differentiableAt_const v)]
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  rw [← hleft, heq.fderiv_eq, hright]

 

lemma plane_laplacian_chain {f : ℝ → ℝ} {g : ℂ → ℝ} {z : ℂ}
    (hg : ContDiffAt ℝ 2 g z) (hf : ContDiffAt ℝ 2 f (g z)) :
    (Δ (f ∘ g)) z = deriv f (g z) * (Δ g) z +
      deriv (deriv f) (g z) * ((fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z I) ^ 2) := by
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [second_direction_chain hg hf 1, second_direction_chain hg hf I]
  ring

end SLEExactGauge

end

 
section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian RealInnerProductSpace
namespace SLEExactGauge

noncomputable def diskWeight (z : ℂ) : ℝ := 1 - ‖z‖ ^ 2

lemma diskWeight_pos {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : 0 < diskWeight z := by
  have hn := mem_ball_zero_iff.mp hz
  dsimp [diskWeight]
  nlinarith [norm_nonneg z]

lemma diskWeight_contDiff : ContDiff ℝ 2 diskWeight :=
  contDiff_const.sub (contDiff_id.norm_sq ℂ)

lemma diskWeight_fderiv (z : ℂ) :
    fderiv ℝ diskWeight z = (-2 : ℝ) • innerSL ℝ z := by
  change fderiv ℝ (fun w : ℂ => 1 - ‖w‖ ^ 2) z = _
  rw [fderiv_const_sub, fderiv_norm_sq_apply]
  ext v
  simp [smul_apply, nsmul_eq_mul]
  ring

lemma diskWeight_laplacian (z : ℂ) : (Δ diskWeight) z = -4 := by
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have heq : fderiv ℝ diskWeight = fun z => (-2 : ℝ) • innerSL ℝ z := funext diskWeight_fderiv
  rw [heq]
  rw [fderiv_fun_const_smul (𝕜 := ℝ) (x := z)
    (innerSL ℝ (E := ℂ)).differentiableAt (-2 : ℝ)]
  simp only [ContinuousLinearMap.fderiv, smul_apply, smul_eq_mul]
  change -2 * inner ℝ (1 : ℂ) 1 + -2 * inner ℝ (I : ℂ) I = -4
  norm_num [real_inner_self_eq_norm_sq]

lemma log_diskWeight_laplacian {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (Δ (fun w => Real.log (diskWeight w))) z = -4 / diskWeight z ^ 2 := by
  have hg := diskWeight_contDiff.contDiffAt (x := z)
  have hf : ContDiffAt ℝ 2 Real.log (diskWeight z) := Real.contDiffAt_log.mpr (diskWeight_pos hz).ne'
  have hh := plane_laplacian_chain hg hf
  have hlog2 : deriv (deriv Real.log) (diskWeight z) = -(diskWeight z ^ 2)⁻¹ := by
    rw [Real.deriv_log']
    exact (hasDerivAt_inv (diskWeight_pos hz).ne').deriv
  change (Δ (fun w => Real.log (diskWeight w))) z = _ at hh
  rw [Real.deriv_log, hlog2, diskWeight_laplacian, diskWeight_fderiv] at hh
  rw [hh]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  have he : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by simpa [Complex.normSq_apply, sq] using Complex.sq_norm z
  have hwne : 1 - ‖z‖ ^ 2 ≠ 0 := (diskWeight_pos hz).ne'
  simp [diskWeight, Complex.mul_re]
  field_simp [hwne]
  nlinarith [he]

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology
namespace SLEExactGauge

lemma log_norm_direction_bound {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) (v : ℂ) :
    |fderiv ℝ (fun w => Real.log ‖f w‖) z v| ≤ ‖deriv f z / f z‖ * ‖v‖ := by
  have hnorm : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) (f z) :=
    differentiableAt_id.norm ℂ hne
  have hd := ((hnorm.hasFDerivAt.comp z (hf.restrictScalars ℝ).hasFDerivAt).log (norm_ne_zero_iff.mpr hne)).fderiv
  change fderiv ℝ (fun w => Real.log ‖f w‖) z = _ at hd
  rw [hd]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, abs_mul,
    abs_inv, Function.comp_apply, abs_norm]
  have hbound := (fderiv ℝ (fun w : ℂ => ‖w‖) (f z)).le_opNorm (fderiv ℝ f z v)
  rw [norm_fderiv_norm hnorm, one_mul, Real.norm_eq_abs] at hbound
  have hvalue : fderiv ℝ f z v = v * deriv f z := by
    rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
    change fderiv ℂ f z v = _
    rw [fderiv_eq_smul_deriv, smul_eq_mul]
  rw [hvalue, norm_mul] at hbound
  rw [hvalue]
  calc
    ‖f z‖⁻¹ * |(fderiv ℝ (fun w : ℂ => ‖w‖) (f z)) (v * deriv f z)|
        ≤ ‖f z‖⁻¹ * (‖v‖ * ‖deriv f z‖) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (norm_nonneg _))
    _ = ‖deriv f z / f z‖ * ‖v‖ := by rw [norm_div]; ring

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma univalent_omitted_value_bound_ball {f : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball z r))
    (hi : InjOn f (ball z r)) (a : ℂ) (ha : a ∉ f '' ball z r) :
    r * ‖deriv f z‖ ≤ (128 * Real.pi) * ‖f z - a‖ := by
  let g : ℂ → ℂ := fun w => z + (r : ℂ) * w
  have hgmap : MapsTo g (ball 0 1) (ball z r) := by
    intro w hw
    rw [mem_ball_iff_norm]
    dsimp only [g]
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left (by simpa [mem_ball_zero_iff] using hw) hr).trans_eq (mul_one r)
  have hgd : Differentiable ℂ g := (differentiable_const z).add ((differentiable_const (r : ℂ)).mul differentiable_id)
  have hgi : Function.Injective g := by
    intro v w he
    exact mul_left_cancel₀ (by exact_mod_cast hr.ne') (add_left_cancel he)
  have hfd : DifferentiableOn ℂ (f ∘ g) (ball 0 1) := hd.comp hgd.differentiableOn hgmap
  have hfi : InjOn (f ∘ g) (ball 0 1) := by
    intro v hv w hw he
    exact hgi (hi (hgmap hv) (hgmap hw) he)
  have hfa : a ∉ (f ∘ g) '' ball 0 1 := by
    rintro ⟨w, hw, he⟩
    exact ha ⟨g w, hgmap hw, he⟩
  have hg0 : g 0 = z := by simp [g]
  have hgder : HasDerivAt g (r : ℂ) 0 := by
    simpa [g] using ((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)).const_add z
  have hfz := (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
  have hder : deriv (f ∘ g) 0 = deriv f z * (r : ℂ) := by
    have hfg : HasDerivAt f (deriv f z) (g 0) := by rw [hg0]; exact hfz
    exact (hfg.comp 0 hgder).deriv
  have hh := univalent_omitted_value_bound hfd hfi a hfa
  simpa [hder, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Function.comp_apply, hg0, mul_comm] using hh

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma logarithmic_lift_deriv_bound {f h : ℂ → ℂ} {a : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (ha : a ∉ f '' ball 0 1)
    (hh : ∀ z ∈ ball (0 : ℂ) 1, deriv h z = deriv f z / (f z - a))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) (1 / 2 : ℝ)) :
    ‖deriv h z‖ ≤ 256 * Real.pi := by
  have hsub : ball z (1 / 2 : ℝ) ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    apply mem_ball.mpr
    have hw' := mem_ball.mp hw
    have hz' := mem_closedBall.mp hz
    exact (dist_triangle w z 0).trans_lt (by linarith)
  have hz' : z ∈ ball (0 : ℂ) 1 := (closedBall_subset_ball (by norm_num)) hz
  have hn : f z - a ≠ 0 := by
    intro he
    exact ha ⟨z, hz', sub_eq_zero.mp he⟩
  have hb := univalent_omitted_value_bound_ball (by norm_num : (0 : ℝ) < 1 / 2)
    (hd.mono hsub) (hi.mono hsub) a (fun he => ha (image_mono hsub he))
  rw [hh z hz', norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr
  linarith

lemma logarithmic_lift_second_bound {f h : ℂ → ℂ} {a : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (ha : a ∉ f '' ball 0 1) (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hh : ∀ z ∈ ball (0 : ℂ) 1, deriv h z = deriv f z / (f z - a)) :
    ‖deriv (deriv h) 0‖ ≤ 512 * Real.pi := by
  have hs : closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 2)
    ((hhd.deriv isOpen_ball).diffContOnCl_ball hs)
    (fun z hz => logarithmic_lift_deriv_bound hd hi ha hh (sphere_subset_closedBall hz))
  convert hb using 1; ring

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma exists_omitted_near_of_inverse {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hf0 : deriv f 0 ≠ 0)
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ z ∈ ball (0 : ℂ) 1, g (f z) = z) :
    ∃ a : ℂ, a ∉ f '' ball 0 1 ∧ ‖f 0 - a‖ < 2 * ‖deriv f 0‖ := by
  have hz : (0 : ℂ) ∈ ball 0 1 := mem_ball_self (by norm_num)
  have hn : 0 < ‖deriv f 0‖ := norm_pos_iff.mpr hf0
  have hr : 0 < 2 * ‖deriv f 0‖ := by positivity
  by_contra! hcontra
  have hsub : ball (f 0) (2 * ‖deriv f 0‖) ⊆ f '' ball 0 1 := by
    intro a ha
    by_contra hnot
    have hh := hcontra a hnot
    have hn' : ‖f 0 - a‖ < 2 * ‖deriv f 0‖ := by
      simpa only [mem_ball_iff_norm, norm_sub_rev] using ha
    linarith
  have hgd := hg.mono hsub
  have hgm : MapsTo g (ball (f 0) (2 * ‖deriv f 0‖)) (closedBall (g (f 0)) 1) := by
    intro w hw
    obtain ⟨z, hz', rfl⟩ := hsub hw
    rw [hgf z hz', hgf 0 hz]
    exact ball_subset_closedBall hz'
  have hbound := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hgm hr
  have hdf := (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hdg := (hgd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
  have heq : (g ∘ f) =ᶠ[𝓝 (0 : ℂ)] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with z hz'
    exact hgf z hz'
  have hprod : deriv g (f 0) * deriv f 0 = 1 :=
    ((hdg.comp 0 hdf).congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id 0)
  have hnormprod : ‖deriv g (f 0)‖ * ‖deriv f 0‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hh := (le_div_iff₀ hr).mp hbound
  nlinarith

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma preSchwarzian_bound_of_inverse {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hf0 : deriv f 0 ≠ 0)
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ z ∈ ball (0 : ℂ) 1, g (f z) = z) :
    ‖deriv (deriv f) 0 / deriv f 0‖ ≤ 1280 * Real.pi := by
  obtain ⟨a, ha, hnear⟩ := exists_omitted_near_of_inverse hd hf0 hg hgf
  have hz : (0 : ℂ) ∈ ball 0 1 := mem_ball_self (by norm_num)
  have hnon (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : f z - a ≠ 0 := by
    intro he
    exact ha ⟨z, hz, sub_eq_zero.mp he⟩
  obtain ⟨h, hhd, hexp, hh⟩ := exists_holomorphic_log_on_ball (by norm_num : (0 : ℝ) < 1)
    (hd.sub_const a) hnon
  have hh' (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      deriv h z = deriv f z / (f z - a) := by
    rw [hh z hz]
    congr 1
    exact ((hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const a).deriv
  have hdf := (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hddf := ((hd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have heq : deriv h =ᶠ[𝓝 (0 : ℂ)] (fun z => deriv f z / (f z - a)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with z hz'
    exact hh' z hz'
  have hsecond : deriv (deriv h) 0 =
      (deriv (deriv f) 0 * (f 0 - a) - deriv f 0 * deriv f 0) / (f 0 - a) ^ 2 :=
    ((hddf.div (hdf.sub_const a) (hnon 0 hz)).congr_of_eventuallyEq heq).deriv
  have halg : deriv (deriv f) 0 / deriv f 0 =
      deriv (deriv h) 0 / deriv h 0 + deriv h 0 := by
    rw [hsecond, hh' 0 hz]
    field_simp [hf0, hnon 0 hz]
    ring
  have hfirst := logarithmic_lift_deriv_bound hd hi ha hh'
    (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have htwo := logarithmic_lift_second_bound hd hi ha hhd hh'
  have hlower : (1 / 2 : ℝ) ≤ ‖deriv h 0‖ := by
    rw [hh' 0 hz, norm_div]
    apply (le_div_iff₀ (norm_pos_iff.mpr (hnon 0 hz))).mpr
    linarith
  have hpos : 0 < ‖deriv h 0‖ := by linarith
  have hratio : ‖deriv (deriv h) 0‖ / ‖deriv h 0‖ ≤ 1024 * Real.pi := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [Real.pi_pos]
  rw [halg]
  calc
    ‖deriv (deriv h) 0 / deriv h 0 + deriv h 0‖ ≤
        ‖deriv (deriv h) 0‖ / ‖deriv h 0‖ + ‖deriv h 0‖ := by
      simpa only [norm_div] using norm_add_le (deriv (deriv h) 0 / deriv h 0) (deriv h 0)
    _ ≤ 1280 * Real.pi := by linarith

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma preSchwarzian_bound_ball {f g : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball z r))
    (hi : InjOn f (ball z r)) (hf0 : deriv f z ≠ 0)
    (hg : DifferentiableOn ℂ g (f '' ball z r))
    (hgf : ∀ w ∈ ball z r, g (f w) = w) :
    r * ‖deriv (deriv f) z / deriv f z‖ ≤ 1280 * Real.pi := by
  let A : ℂ → ℂ := fun w => z + (r : ℂ) * w
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hAmap : MapsTo A (ball 0 1) (ball z r) := by
    intro w hw
    rw [mem_ball_iff_norm]
    dsimp only [A]
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hw) hr).trans_eq (mul_one r)
  have hAd : Differentiable ℂ A :=
    (differentiable_const z).add ((differentiable_const (r : ℂ)).mul differentiable_id)
  have hAder (w : ℂ) : HasDerivAt A (r : ℂ) w := by
    simpa [A] using ((hasDerivAt_id w).const_mul (r : ℂ)).const_add z
  have hAi : Function.Injective A := by
    intro v w he
    exact mul_left_cancel₀ hrC (add_left_cancel he)
  have hA0 : A 0 = z := by simp [A]
  let F := f ∘ A
  let G := fun w => (g w - z) / (r : ℂ)
  have hFd : DifferentiableOn ℂ F (ball 0 1) := hd.comp hAd.differentiableOn hAmap
  have hFi : InjOn F (ball 0 1) := by
    intro v hv w hw he
    exact hAi (hi (hAmap hv) (hAmap hw) he)
  have hsub : F '' ball 0 1 ⊆ f '' ball z r := by
    rintro w ⟨v, hv, rfl⟩
    exact ⟨A v, hAmap hv, rfl⟩
  have hGd : DifferentiableOn ℂ G (F '' ball 0 1) :=
    ((hg.mono hsub).sub_const z).div_const (r : ℂ)
  have hGF : ∀ w ∈ ball (0 : ℂ) 1, G (F w) = w := by
    intro w hw
    dsimp [G, F]
    rw [hgf _ (hAmap hw)]
    dsimp [A]
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hrC]
  have hdf := (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
  have hFder : deriv F 0 = deriv f z * (r : ℂ) := by
    have hh : HasDerivAt f (deriv f z) (A 0) := by rw [hA0]; exact hdf
    exact (hh.comp 0 (hAder 0)).deriv
  have hbound := preSchwarzian_bound_of_inverse hFd hFi
    (by rw [hFder]; exact mul_ne_zero hf0 hrC) hGd hGF
  have hFsecond : deriv (deriv F) 0 = deriv (deriv f) z * (r : ℂ) ^ 2 := by
    have heq : deriv F =ᶠ[𝓝 (0 : ℂ)] (fun w => deriv f (A w) * (r : ℂ)) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1))] with w hw
      exact (((hd.differentiableAt (isOpen_ball.mem_nhds (hAmap hw))).hasDerivAt).comp w (hAder w)).deriv
    have hdd := ((hd.deriv isOpen_ball).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
    have hh : HasDerivAt (deriv f) (deriv (deriv f) z) (A 0) := by rw [hA0]; exact hdd
    have hh' := (((hh.comp 0 (hAder 0)).mul_const (r : ℂ)).congr_of_eventuallyEq heq).deriv
    simpa only [pow_two, mul_assoc] using hh'
  have halg : deriv (deriv F) 0 / deriv F 0 = (r : ℂ) * (deriv (deriv f) z / deriv f z) := by
    rw [hFsecond, hFder]
    field_simp
  rw [halg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hbound
  exact hbound

 

lemma disk_preSchwarzian_bound {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hfz : deriv f z ≠ 0) :
    ‖((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv f) z / deriv f z) - 2 * star z‖ ≤
      2560 * Real.pi + 2 := by
  have hn := mem_ball_zero_iff.mp hz
  have hr : 0 < 1 - ‖z‖ := by linarith
  have hsub : ball z (1 - ‖z‖) ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    apply mem_ball.mpr
    have hh := mem_ball.mp hw
    have hd0 : dist z 0 = ‖z‖ := dist_zero_right z
    exact (dist_triangle w z 0).trans_lt (by linarith)
  have hb := preSchwarzian_bound_ball hr (hd.mono hsub) (hi.mono hsub) hfz
    (hg.mono (image_mono hsub)) (fun w hw => hgf w (hsub hw))
  have hrad : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  calc
    _ ≤ ‖((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv f) z / deriv f z)‖ + ‖2 * star z‖ := norm_sub_le _ _
    _ = (1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖ + 2 * ‖z‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrad,
        norm_ofNat, norm_star]
    _ ≤ 2560 * Real.pi + 2 := by
      have hprod := mul_le_mul_of_nonneg_right (show (1 + ‖z‖) ≤ 2 by linarith)
        (mul_nonneg hr.le (norm_nonneg (deriv (deriv f) z / deriv f z)))
      nlinarith

end SLEExactGauge

end

 
section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian RealInnerProductSpace
namespace SLEExactGauge

noncomputable def diskLogRadius (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  Real.log (diskWeight z) + Real.log ‖deriv f z‖

lemma diskLogRadius_contDiffAt {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) :
    ContDiffAt ℝ 2 (diskLogRadius f) z := by
  have hh := (((hd.deriv isOpen_ball).analyticAt (isOpen_ball.mem_nhds hz))).harmonicAt_log_norm hne
  exact (diskWeight_contDiff.contDiffAt.log (diskWeight_pos hz).ne').add hh.1

end SLEExactGauge
end
end
end

end OAI
