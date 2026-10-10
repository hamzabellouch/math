import OAI.Analysis.HenonEmden.SphereFlux

namespace OAI

universe uE uE2

section RadialODE

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
noncomputable section


open Set Filter Topology
namespace HenonLaneEmden.RadialODE
lemma pow_le_self {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) : r^k ≤ r := by
  calc r^k ≤ r^1 := pow_le_pow_of_le_one hr hr1 hk
       _ = r := pow_one r

lemma sample_flux {U V : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hU : ContinuousOn U (Ici 0)) (hV : ∀ r > 0, HasDerivAt U (V r) r)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ c ∈ Ioo 0 r, |c^k * V c| ≤ |U r-U 0| := by
  obtain ⟨c,hc,hd⟩ := exists_hasDerivAt_eq_slope U V hr (hU.mono (Icc_subset_Ici_self))
    (fun x hx => hV x hx.1)
  refine ⟨c,hc,?_⟩
  rw [hd,sub_zero,← mul_div_assoc,abs_div,abs_mul,abs_of_pos (pow_pos hc.1 k),abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  have hp : c^k ≤ r := (pow_le_self hk hc.1.le (hc.2.le.trans hr1)).trans hc.2.le
  nlinarith [abs_nonneg (U r-U 0)]

lemma flux_nonpos {U V : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hU : ContinuousOn U (Ici 0)) (hV : ∀ r > 0, HasDerivAt U (V r) r)
    (hF : AntitoneOn (fun r => r^k*V r) (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    r^k*V r ≤ 0 := by
  have hl : Tendsto (fun s => |U s-U 0|) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto U (𝓝[>] 0) (𝓝 (U 0)) := (hU 0 (by simp)).mono Ioi_subset_Ici_self
    simpa using (hc.sub_const (U 0)).abs
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one : (0:ℝ)<1))] with s hs hsr hs1
  obtain ⟨c,hc,hsamp⟩ := sample_flux hk hU hV hs hs1.le
  exact (hF hc.1 hr (hc.2.le.trans hsr.le)).trans ((le_abs_self _).trans hsamp)

lemma flux_tendsto_zero {U V : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hU : ContinuousOn U (Ici 0)) (hV : ∀ r > 0, HasDerivAt U (V r) r)
    (hF : AntitoneOn (fun r => r^k*V r) (Ioi 0)) :
    Tendsto (fun r => r^k*V r) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hl : Tendsto (fun s => |U s-U 0|) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto U (𝓝[>] 0) (𝓝 (U 0)) := (hU 0 (by simp)).mono Ioi_subset_Ici_self
    simpa using (hc.sub_const (U 0)).abs
  have he : ∀ᶠ s in 𝓝[>] (0:ℝ), |U s-U 0| < ε := hl (Iio_mem_nhds hε)
  obtain ⟨s,⟨hs,hs1⟩,he⟩ := (((show ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s from self_mem_nhdsWithin).and
    (show ∀ᶠ s : ℝ in 𝓝[>] 0, s < 1 from mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one))).and he).exists
  obtain ⟨c,hc,hsamp⟩ := sample_flux hk hU hV hs hs1.le
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hc.1)] with r hr hrc
  have hneg := flux_nonpos hk hU hV hF hr
  have hlo := hF hr hc.1 hrc.le
  rw [Real.dist_eq,sub_zero,abs_of_nonpos hneg]
  have hcneg : -(c^k*V c) ≤ |c^k*V c| := neg_le_abs _
  linarith
end HenonLaneEmden.RadialODE

namespace HenonLaneEmden.RadialODE
lemma positive_radial_flux_lower {k : ℕ} (hk : 2 ≤ k) {U V : ℝ → ℝ}
    (hV : ∀ r > 0, HasDerivAt U (V r) r)
    (hF : AntitoneOn (fun r => r^k*V r) (Ioi 0)) (hU : ∀ r > 0, 0 ≤ U r)
    {r : ℝ} (hr : 0 < r) : 0 ≤ r*V r+((k:ℝ)-1)*U r := by
  let c : ℝ := r^k*V r/((k:ℝ)-1)
  have hk1 : 0 < (k:ℝ)-1 := by exact_mod_cast (show 0 < (k:ℤ)-1 by omega)
  have hkpos : 1 ≤ k := by omega
  have hcomp : AntitoneOn (fun s : ℝ => U s+c*s^(-((k:ℝ)-1))) (Ici r) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici r)
    · intro s hs
      have hs0 : 0 < s := hr.trans_le hs
      exact ((hV s hs0).continuousAt.add
        ((Real.continuousAt_rpow_const _ _ (Or.inl hs0.ne')).const_mul c)).continuousWithinAt
    · intro s hs
      have hs0 : 0 < s := hr.trans (by simpa using hs)
      exact ((hV s hs0).add ((Real.hasDerivAt_rpow_const (Or.inl hs0.ne')).const_mul c)).hasDerivWithinAt
    · intro s hs
      have hsr : r < s := by simpa using hs
      have hs0 : 0 < s := hr.trans hsr
      have hh := hF hr hs0 hsr.le
      have he : -((k:ℝ)-1)-1 = -(k:ℝ) := by ring
      change V s+c*(-((k:ℝ)-1)*s^(-((k:ℝ)-1)-1)) ≤ 0
      rw [he,Real.rpow_neg hs0.le,Real.rpow_natCast]
      dsimp [c]
      have hden : (k:ℝ)-1 ≠ 0 := ne_of_gt hk1
      have hsPow : 0 < s^k := pow_pos hs0 _
      have hh' : V s ≤ r^k*V r/(s^k) := (le_div_iff₀ hsPow).mpr (by simpa [mul_comm] using hh)
      field_simp
      field_simp at hh'
      nlinarith
  have hbound : ∀ᶠ s : ℝ in atTop, c*s^(-((k:ℝ)-1)) ≤ U r+c*r^(-((k:ℝ)-1)) := by
    filter_upwards [eventually_ge_atTop r] with s hs
    have hh := hcomp (by simp) hs hs
    linarith [hU s (hr.trans_le hs)]
  have hh : 0 ≤ U r+c*r^(-((k:ℝ)-1)) :=
    le_of_tendsto (by simpa using (tendsto_rpow_neg_atTop hk1).const_mul c) hbound
  have he : (k:ℝ)-1 = ((k-1:ℕ):ℝ) := by rw [Nat.cast_sub hkpos]; norm_num
  rw [Real.rpow_neg hr.le,he,Real.rpow_natCast] at hh
  have hpow : r^k = r*r^(k-1) := by
    conv_lhs => rw [show k = (k-1)+1 by omega,pow_succ]
    ring
  dsimp [c] at hh
  rw [hpow] at hh
  have hrp : r^(k-1) ≠ 0 := pow_ne_zero _ hr.ne'
  have hsimp : r*r^(k-1)*V r/((k:ℝ)-1)*(r^(k-1))⁻¹ = r*V r/((k:ℝ)-1) := by field_simp
  rw [hsimp] at hh
  nlinarith [(le_div_iff₀ hk1).mp (show -(U r) ≤ r*V r/((k:ℝ)-1) by linarith)]
end HenonLaneEmden.RadialODE

open MeasureTheory
namespace HenonLaneEmden.RadialODE
lemma radial_source_integral_bound {k : ℕ} (hk : 2 ≤ k) {U V V' W : ℝ → ℝ}
    (hUc : ContinuousOn U (Ici 0)) (hVc : ContinuousOn V (Ici 0))
    (hWc : ContinuousOn W (Ici 0))
    (hU : ∀ r > 0, HasDerivAt U (V r) r) (hV : ∀ r > 0, HasDerivAt V (V' r) r)
    (hF : AntitoneOn (fun r => r^k*V r) (Ioi 0))
    (hODE : ∀ r > 0, r*V' r+(k:ℝ)*V r = -r*W r)
    (hp : ∀ r > 0, 0 ≤ U r) {R : ℝ} (hR : 0 < R) :
    (∫ r in 0..R, r*W r) ≤ ((k:ℝ)-1)*U 0 := by
  have hH : ContinuousOn (fun r => r*V r+((k:ℝ)-1)*U r) (Icc 0 R) :=
    ((continuousOn_id.mul hVc).add (hUc.const_mul _)).mono Icc_subset_Ici_self
  have hHd (r : ℝ) (hr : r ∈ Ioo 0 R) :
      HasDerivAt (fun s => s*V s+((k:ℝ)-1)*U s) (-r*W r) r := by
    convert! (((hasDerivAt_id r).mul (hV r hr.1)).add ((hU r hr.1).const_mul ((k:ℝ)-1))) using 1
    simp only [id_eq,one_mul]
    nlinarith [hODE r hr.1]
  have hi : IntervalIntegrable (fun r => r*W r) volume 0 R :=
    (continuousOn_id.mul hWc).mono Icc_subset_Ici_self |>.intervalIntegrable_of_Icc hR.le
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hH hHd (by simpa only [Pi.neg_def,neg_mul] using hi.neg)
  simp only [zero_mul,zero_add] at hh
  have hi' : (∫ r in 0..R, -r*W r) = -(∫ r in 0..R, r*W r) := by
    simp_rw [neg_mul]; exact intervalIntegral.integral_neg
  rw [hi'] at hh
  linarith [positive_radial_flux_lower hk hU hF hp hR]
end HenonLaneEmden.RadialODE

namespace HenonLaneEmden.SphereCalculus
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
lemma continuous_meanD_global {u : E → ℝ} (hu : ContDiff ℝ 2 u) : Continuous (meanD u) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support isCompact_univ
    (s := (univ : Set ℝ))
  · exact (((hu.continuous_fderiv (by norm_num)).comp
      (continuous_fst.smul continuous_snd.subtype_val)).clm_apply
      continuous_snd.subtype_val).continuousOn
  · exact fun _ _ _ h => (h (mem_univ _)).elim

lemma spherical_source_integral_bound (hn : 3 ≤ Module.finrank ℝ E) {u w : E → ℝ}
    (hu : ContDiff ℝ 2 u) (hw : Continuous w) (hp : ∀ x, 0 ≤ u x) (hwp : ∀ x, 0 ≤ w x)
    (hEq : ∀ x, -Laplacian.laplacian u x = w x) {R : ℝ} (hR : 0 < R) :
    (∫ r in 0..R, r*mean w r) ≤ ((Module.finrank ℝ E:ℝ)-2)*mean u 0 := by
  have hd (r : ℝ) (hr : 0 < r) := hasDerivAt_mean_flux hu.contDiffOn hw.continuousOn
    (fun x _ => hEq x) hr
  have hF : AntitoneOn (fun r => r^(Module.finrank ℝ E-1)*meanD u r) (Ioi 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
      (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hd r (by simpa using hr)).hasDerivWithinAt)
    intro r hr
    have hr0 : 0 < r := by simpa using hr
    exact neg_nonpos.mpr (mul_nonneg (pow_nonneg hr0.le _)
      (integral_nonneg fun θ => hwp (r • θ.1)))
  have hODE (r : ℝ) (hr : 0 < r) : r*meanDD u r+
      ((Module.finrank ℝ E-1:ℕ):ℝ)*meanD u r = -r*mean w r := by
    have h := mean_laplacian_ode hu.contDiffOn hw.neg.continuousOn
      (fun x _ => neg_eq_iff_eq_neg.mp (hEq x)) hr
    simp only [Pi.neg_def,mean_neg] at h
    have hpower : r^(Module.finrank ℝ E-1) = r^(Module.finrank ℝ E-2)*r := by
      rw [show Module.finrank ℝ E-1 = Module.finrank ℝ E-2+1 by omega,pow_succ]
    rw [hpower] at h
    have hnz : r^(Module.finrank ℝ E-2) ≠ 0 := pow_ne_zero _ hr.ne'
    apply (mul_left_cancel₀ hnz)
    nlinarith [h]
  have hh := RadialODE.radial_source_integral_bound (k := Module.finrank ℝ E-1) (by omega)
    (continuous_mean hu.continuous).continuousOn (continuous_meanD_global hu).continuousOn
    (continuous_mean hw).continuousOn
    (fun r hr => hasDerivAt_mean hu.contDiffOn hr)
    (fun r hr => hasDerivAt_meanD hu.contDiffOn hr) hF hODE
    (fun r _ => integral_nonneg fun θ => hp (r • θ.1)) hR
  have hcast : ((Module.finrank ℝ E-1:ℕ):ℝ)-1 = (Module.finrank ℝ E:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Module.finrank ℝ E),Nat.cast_one]
    ring
  simpa only [hcast] using hh
end HenonLaneEmden.SphereCalculus

namespace HenonLaneEmden.SphereCalculus
variable {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma spherical_source_lintegral_bound (hn : 3 ≤ Module.finrank ℝ E) {u w : E → ℝ}
    (hu : ContDiff ℝ 2 u) (hw : Continuous w) (hp : ∀ x, 0 ≤ u x) (hwp : ∀ x, 0 ≤ w x)
    (hEq : ∀ x, -Laplacian.laplacian u x = w x) :
    (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r*mean w r)) ≤
      ENNReal.ofReal (((Module.finrank ℝ E:ℝ)-2)*mean u 0) := by
  have hUnion : (⋃ j : ℕ, Ioc (0:ℝ) (j+1:ℝ)) = Ioi 0 := by
    apply iUnion_Ioc_eq_Ioi_self_iff.mpr
    intro r _
    obtain ⟨j,hj⟩ := exists_nat_gt r
    exact ⟨j,by linarith⟩
  have hm : Monotone (fun j : ℕ => Ioc (0:ℝ) (j+1:ℝ)) := by
    intro i j hij
    exact Ioc_subset_Ioc_right (by exact_mod_cast (Nat.add_le_add_right hij 1))
  rw [← hUnion,setLIntegral_iUnion_of_directed _ hm.directed_le]
  apply iSup_le
  intro j
  have hR : (0:ℝ) < j+1 := by positivity
  have hi : IntervalIntegrable (fun r => r*mean w r) volume 0 (j+1:ℝ) :=
    (continuous_id.mul (continuous_mean hw)).intervalIntegrable _ _
  have hrw : (∫⁻ r in Ioc (0:ℝ) (j+1:ℝ), ENNReal.ofReal (r*mean w r)) =
      ENNReal.ofReal (∫ r in 0..(j+1:ℝ), r*mean w r) := by
    rw [intervalIntegral.integral_of_le hR.le]
    apply (ofReal_integral_eq_lintegral_ofReal hi.1 _).symm
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg hr.1.le (integral_nonneg fun θ => hwp (r • θ.1))
  rw [hrw]
  exact ENNReal.ofReal_le_ofReal (spherical_source_integral_bound hn hu hw hp hwp hEq hR)

lemma kernel_source_polar (hn : 3 ≤ Module.finrank ℝ E) {w : E → ℝ}
    (hw : Continuous w) (hp : ∀ x, 0 ≤ w x) :
    (∫⁻ x : E, ENNReal.ofReal (‖x‖^(2-(Module.finrank ℝ E:ℝ))*w x)) =
      ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r*mean w r) := by
  rw [Polar.lintegral_polar volume _ (by fun_prop)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr0 : 0 < r := hr
  simp_rw [norm_smul_sphere hr0.le]
  have hsint : Integrable (fun θ : UnitSphere E => w (r • θ.1)) (volume : Measure E).toSphere :=
    (hw.comp (continuous_const.smul continuous_subtype_val)).integrable_of_hasCompactSupport
      (.of_compactSpace _)
  have hs : (∫⁻ θ : UnitSphere E, ENNReal.ofReal (r^(2-(Module.finrank ℝ E:ℝ))*w (r • θ.1))
      ∂(volume : Measure E).toSphere) =
      ENNReal.ofReal (r^(2-(Module.finrank ℝ E:ℝ))*mean w r) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hsint.const_mul _) (Eventually.of_forall fun θ =>
      mul_nonneg (Real.rpow_nonneg hr0.le _) (hp _)),integral_const_mul]
    rfl
  rw [hs,← ENNReal.ofReal_mul (pow_nonneg hr0.le _)]
  congr 1
  rw [← mul_assoc]
  congr 1
  rw [← Real.rpow_natCast,← Real.rpow_add hr0]
  have hc : ((Module.finrank ℝ E-1:ℕ):ℝ)+(2-(Module.finrank ℝ E:ℝ)) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Module.finrank ℝ E),Nat.cast_one]
    ring
  rw [hc,Real.rpow_one]

lemma smooth_newton_lower_at_zero (hn : 3 ≤ Module.finrank ℝ E) {u w : E → ℝ}
    (hu : ContDiff ℝ 2 u) (hw : Continuous w) (hp : ∀ x, 0 ≤ u x) (hwp : ∀ x, 0 ≤ w x)
    (hEq : ∀ x, -Laplacian.laplacian u x = w x) :
    (∫⁻ x : E, ENNReal.ofReal (‖x‖^(2-(Module.finrank ℝ E:ℝ))*w x)) ≤
      ENNReal.ofReal (((Module.finrank ℝ E:ℝ)-2)*
        ((volume : Measure E).toSphere univ).toReal*u 0) := by
  rw [kernel_source_polar hn hw hwp]
  simpa only [mean_zero, mul_assoc] using spherical_source_lintegral_bound hn hu hw hp hwp hEq
end HenonLaneEmden.SphereCalculus

end
end RadialODE

end OAI
