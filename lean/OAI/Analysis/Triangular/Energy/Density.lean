import OAI.Analysis.Triangular.Energy.Cutoff

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal RealInnerProductSpace FourierTransform
open Classical Filter MeasureTheory Complex ComplexConjugate FourierTransform
namespace TriangularUniversal
/-- Regularity actually used by the density LP proof. Gaussian-bounded Fourier
pairs are put into this class below; no separation of a competitor is assumed. -/
structure LPFunction where
  toFun : Plane → ℂ
  continuous : Continuous toFun
  integrable : Integrable toFun
  fourierIntegrable : Integrable (𝓕 toFun)
  momentIntegrable : Integrable (fun z => ‖z‖ * ‖toFun z‖)
  bound : ℝ
  norm_bound : ∀ x, ‖toFun x‖ ≤ bound

instance : CoeFun LPFunction (fun _ => Plane → ℂ) := ⟨LPFunction.toFun⟩

lemma regular_kernel_integrable (f : LPFunction)
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun xy : Plane × Plane => f (xy.1-xy.2)) (μ.prod ν) := by
  exact (integrable_const f.bound).mono'
    (f.continuous.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    (Eventually.of_forall fun xy => f.norm_bound (xy.1-xy.2))

lemma regular_firstMoment_integrable (f : LPFunction) :
    Integrable (fun z => ‖z‖ * ‖f z‖) := f.momentIntegrable

lemma firstMoment_nonneg (f : Plane → ℂ) : 0 ≤ firstMoment f :=
  integral_nonneg fun z => mul_nonneg (norm_nonneg z) (norm_nonneg (f z))

lemma kernelForm_cutoff (f : LPFunction) {R T : ℝ} (hT : 0 < T)
    (μ : Measure Plane) [IsFiniteMeasure μ] :
    kernelForm f μ (cutoffMeasure R T) = ∫ x, cutoffConvolution f R T x ∂μ := by
  let := cutoffMeasure_finite (R := R) hT
  rw [kernelForm, integral_prod _ (regular_kernel_integrable f μ (cutoffMeasure R T))]
  simp_rw [cutoffConvolution_eq_integral]

lemma kernelForm_cutoff_self_upper (f : LPFunction)
    (ha : 0 ≤ (∫ z, f z).re) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T) :
    (kernelForm f (cutoffMeasure R T) (cutoffMeasure R T)).re ≤
      ((∫ z, f z).re + firstMoment f / T) * Real.pi * (R+T)^2 := by
  let := cutoffMeasure_finite (R := R) hT
  have hi : Integrable (fun x => cutoffConvolution f R T x) (cutoffMeasure R T) := by
    simpa only [cutoffConvolution_eq_integral] using
      (regular_kernel_integrable f (cutoffMeasure R T) (cutoffMeasure R T)).integral_prod_left
  rw [kernelForm_cutoff f hT, integral_reC hi]
  calc
    _ ≤ ∫ _ : Plane, ((∫ z, f z).re + firstMoment f / T) ∂cutoffMeasure R T := by
      apply integral_mono hi.re (integrable_const _)
      intro x
      change (cutoffConvolution f R T x).re ≤
        (∫ z, f z).re + firstMoment f / T
      have hb := (cutoffConvolution_re_bounds f.integrable
        (regular_firstMoment_integrable f) (R := R) hT x).2
      have hm := mul_le_mul_of_nonneg_right (radialCutoff_le_one R T x) ha
      linarith
    _ = ((∫ z, f z).re + firstMoment f / T) * (∫ x, radialCutoff R T x) := by
      rw [integral_const, smul_eq_mul, cutoffMeasure_mass hT]; ring
    _ ≤ ((∫ z, f z).re + firstMoment f / T) * (Real.pi*(R+T)^2) := by
      gcongr
      · exact add_nonneg ha (div_nonneg (firstMoment_nonneg f) hT.le)
      · exact radialCutoff_integral_bound hR hT
    _ = _ := by ring


def pointsMeasure (S : Finset Plane) : Measure Plane := ∑ x ∈ S, Measure.dirac x

instance pointsMeasure_finite (S : Finset Plane) : IsFiniteMeasure (pointsMeasure S) := by
  unfold pointsMeasure
  infer_instance

lemma integral_pointsMeasure (S : Finset Plane) (f : Plane → ℂ) :
    (∫ x, f x ∂pointsMeasure S) = ∑ x ∈ S, f x := by
  rw [pointsMeasure, integral_finsetSum_measure]
  · simp only [integral_dirac]
  · intro i hi
    exact integrable_dirac (by finiteness)

lemma kernelForm_points_points (f : LPFunction) (S : Finset Plane) :
    kernelForm f (pointsMeasure S) (pointsMeasure S) =
      ∑ x ∈ S, ∑ y ∈ S, f (x-y) := by
  rw [kernelForm, integral_prod _ (regular_kernel_integrable f _ _), integral_pointsMeasure]
  simp only [integral_pointsMeasure]

lemma kernelForm_points_cutoff_lower (f : LPFunction)
    (S : Finset Plane) {R T : ℝ} (hT : 0 < T) (hS : ∀ x ∈ S, ‖x‖ ≤ R) :
    (S.card : ℝ) * ((∫ z, f z).re - firstMoment f / T) ≤
      (kernelForm f (pointsMeasure S) (cutoffMeasure R T)).re := by
  rw [kernelForm_cutoff f hT, integral_pointsMeasure, Complex.re_sum]
  calc
    _ = ∑ _x ∈ S, ((∫ z, f z).re - firstMoment f / T) := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      have h := (cutoffConvolution_re_bounds f.integrable
        (regular_firstMoment_integrable f) (R := R) hT x).1
      rwa [radialCutoff_eq_one hT (hS x hx), one_mul] at h

lemma fourier_zero_eq_integral (f : Plane → ℂ) : 𝓕 f 0 = ∫ x, f x := by
  rw [Real.fourier_eq]
  simp

/-- The exact finite-disk estimate underlying the density-only bound.
The correction uses a cutoff of thickness T and its first moment, never a
uniform spacing or local-count bound on S. -/
lemma finite_disk_lp (f : LPFunction)
    (hreal : ∀ w, (𝓕 (f : Plane → ℂ) w).im = 0)
    (hpos : ∀ w, 0 ≤ (𝓕 (f : Plane → ℂ) w).re)
    (S : Finset Plane) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T)
    (hS : ∀ x ∈ S, ‖x‖ ≤ R) :
    2*(S.card : ℝ)*((∫ z, f z).re - firstMoment f/T) -
      ((∫ z, f z).re + firstMoment f/T)*Real.pi*(R+T)^2 ≤
      ∑ x ∈ S, ∑ y ∈ S, (f (x-y)).re := by
  let := cutoffMeasure_finite (R := R) hT
  have ha : 0 ≤ (∫ z, f z).re := by simpa only [fourier_zero_eq_integral] using hpos 0
  have hc := kernelForm_comparison f f.continuous f.integrable
    f.fourierIntegrable hreal hpos (pointsMeasure S) (cutoffMeasure R T)
  have hl := kernelForm_points_cutoff_lower f S hT hS
  have hu := kernelForm_cutoff_self_upper f ha hR hT
  rw [kernelForm_points_points] at hc
  simp only [Complex.re_sum] at hc
  nlinarith

lemma ofReal_finset_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ x ∈ S, f x) ≤ ∑ x ∈ S, ENNReal.ofReal (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    simp only [Finset.sum_insert hx]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

lemma offdiag_sum_eq (f : Plane → ℝ) (S : Finset Plane) :
    (∑ x ∈ S, ∑ y ∈ S.erase x, f (x-y)) =
      (∑ x ∈ S, ∑ y ∈ S, f (x-y)) - (S.card : ℝ)*f 0 := by
  have he : (∑ x ∈ S, ∑ y ∈ S.erase x, f (x-y)) + (S.card : ℝ)*f 0 =
      ∑ x ∈ S, ∑ y ∈ S, f (x-y) := by
    calc
      _ = ∑ x ∈ S, ((∑ y ∈ S.erase x, f (x-y)) + f 0) := by
        rw [Finset.sum_add_distrib]; simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        simpa only [sub_self] using Finset.sum_erase_add S (fun y => f (x-y)) hx
  linarith

lemma normalized_offdiag_minorization (f : Plane → ℂ) (g : ℝ → ℝ)
    (hminor : ∀ x : Plane, x ≠ 0 → (f x).re ≤ g (‖x‖^2))
    (S : Finset Plane) (hN : 0 < S.card) :
    ENNReal.ofReal ((∑ x ∈ S, ∑ y ∈ S.erase x, (f (x-y)).re)/(S.card : ℝ)) ≤
      (S.card : ℝ≥0∞)⁻¹ * ∑ x ∈ S, ∑ y ∈ S.erase x, ENNReal.ofReal (g (‖x-y‖^2)) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast,
    div_eq_mul_inv, mul_comm]
  gcongr
  calc
    _ ≤ ∑ x ∈ S, ENNReal.ofReal (∑ y ∈ S.erase x, (f (x-y)).re) := ofReal_finset_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      calc
        _ ≤ ∑ y ∈ S.erase x, ENNReal.ofReal ((f (x-y)).re) := ofReal_finset_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro y hy
          apply ENNReal.ofReal_le_ofReal
          apply hminor
          exact sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hy).1)

lemma finite_disk_energy_lp (f : LPFunction)
    (hreal : ∀ w, (𝓕 (f : Plane → ℂ) w).im = 0)
    (hpos : ∀ w, 0 ≤ (𝓕 (f : Plane → ℂ) w).re)
    (g : ℝ → ℝ) (hminor : ∀ x : Plane, x ≠ 0 → (f x).re ≤ g (‖x‖^2))
    (C : Set Plane) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T)
    (hN : 0 < diskCount C R) :
    ENNReal.ofReal (2*((∫ z, f z).re - firstMoment f/T) -
      ((∫ z, f z).re + firstMoment f/T) * (Real.pi*(R+T)^2/(diskCount C R : ℝ)) -
        (f 0).re) ≤ diskEnergy g C R := by
  have hS : ∀ x ∈ diskPoints C R, ‖x‖ ≤ R := by
    intro x hx
    unfold diskPoints at hx
    split_ifs at hx with h
    · simpa only [Metric.mem_closedBall, dist_zero_right] using (h.mem_toFinset.mp hx).2
    · simp at hx
  have hl := finite_disk_lp f hreal hpos (diskPoints C R) hR hT hS
  have hN' : (0 : ℝ) < diskCount C R := by exact_mod_cast hN
  have he : 2*((∫ z, f z).re - firstMoment f/T) -
      ((∫ z, f z).re + firstMoment f/T)*(Real.pi*(R+T)^2/(diskCount C R : ℝ)) -
        (f 0).re ≤
      (∑ x ∈ diskPoints C R, ∑ y ∈ (diskPoints C R).erase x, (f (x-y)).re) /
        (diskCount C R : ℝ) := by
    rw [le_div_iff₀ hN', offdiag_sum_eq (fun z => (f z).re)]
    change _ ≤ _ - (diskCount C R : ℝ)*(f 0).re
    have hN0 : (diskCount C R : ℝ) ≠ 0 := ne_of_gt hN'
    have hid : (2*((∫ z, f z).re - firstMoment f/T) -
        ((∫ z, f z).re + firstMoment f/T)*(Real.pi*(R+T)^2/(diskCount C R : ℝ)) -
        (f 0).re) * (diskCount C R : ℝ) =
        2*(diskCount C R : ℝ)*((∫ z, f z).re - firstMoment f/T) -
        ((∫ z, f z).re + firstMoment f/T)*Real.pi*(R+T)^2 -
        (diskCount C R : ℝ)*(f 0).re := by
      field_simp [hN0]
    rw [hid]
    exact sub_le_sub_right hl _
  exact (ENNReal.ofReal_le_ofReal he).trans
    (normalized_offdiag_minorization f g hminor (diskPoints C R) hN)

lemma density_count_eventually_pos {C : Set Plane} (hD : DensityOne C) :
    ∀ᶠ R : ℝ in atTop, 0 < diskCount C R := by
  have hp := hD.eventually (lt_mem_nhds (show (1/2 : ℝ) < 1 by norm_num))
  filter_upwards [hp, eventually_gt_atTop (0 : ℝ)] with R h hR
  have hden : 0 < Real.pi * R^2 := mul_pos Real.pi_pos (sq_pos_of_pos hR)
  have hn := (lt_div_iff₀ hden).mp h
  have hpR : (0 : ℝ) < diskCount C R := by nlinarith
  exact_mod_cast hpR

lemma density_volume_ratio {C : Set Plane} (hD : DensityOne C) (ε : ℝ) :
    Tendsto (fun R : ℝ => Real.pi*(R+ε*R)^2/(diskCount C R : ℝ))
      atTop (𝓝 ((1+ε)^2)) := by
  have h := (hD.inv₀ (show (1 : ℝ) ≠ 0 by norm_num)).const_mul ((1+ε)^2)
  convert h using 1
  · ext R
    simp only [inv_div]
    ring
  · simp

lemma density_lp_epsilon (f : LPFunction)
    (hreal : ∀ w, (𝓕 (f : Plane → ℂ) w).im = 0)
    (hpos : ∀ w, 0 ≤ (𝓕 (f : Plane → ℂ) w).re)
    (g : ℝ → ℝ) (hminor : ∀ x : Plane, x ≠ 0 → (f x).re ≤ g (‖x‖^2))
    {C : Set Plane} (hD : DensityOne C) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (2*(∫ z, f z).re - (∫ z, f z).re*(1+ε)^2 - (f 0).re) ≤ energy g C := by
  have hm : Tendsto (fun R : ℝ => firstMoment f/(ε*R)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hε)
  have ha : Tendsto (fun _ : ℝ => (∫ z, f z).re) atTop (𝓝 (∫ z, f z).re) := tendsto_const_nhds
  have hL : Tendsto (fun R : ℝ =>
      2*((∫ z, f z).re-firstMoment f/(ε*R)) -
      ((∫ z, f z).re+firstMoment f/(ε*R))*(Real.pi*(R+ε*R)^2/(diskCount C R : ℝ)) -
      (f 0).re) atTop
      (𝓝 (2*(∫ z, f z).re - (∫ z, f z).re*(1+ε)^2 - (f 0).re)) := by
    simpa only [sub_zero, add_zero] using
      (((ha.sub hm).const_mul 2).sub ((ha.add hm).mul (density_volume_ratio hD ε))).sub_const (f 0).re
  have hLe := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL
  change _ ≤ Filter.liminf (diskEnergy g C) atTop
  rw [← hLe.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [density_count_eventually_pos hD, eventually_gt_atTop (0 : ℝ)] with R hN hR
  exact finite_disk_energy_lp f hreal hpos g hminor C hR.le (mul_pos hε hR) hN

/-- Source §2, density-only linear programming bound, for the exact ordered-pair
centered-disk ENNReal liminf. This requires no uniform separation, special
local-count bound, finite energy, or decay of the potential. -/
lemma density_lp (f : LPFunction)
    (hreal : ∀ w, (𝓕 (f : Plane → ℂ) w).im = 0)
    (hpos : ∀ w, 0 ≤ (𝓕 (f : Plane → ℂ) w).re)
    (g : ℝ → ℝ) (hminor : ∀ x : Plane, x ≠ 0 → (f x).re ≤ g (‖x‖^2))
    {C : Set Plane} (hD : DensityOne C) :
    ENNReal.ofReal ((∫ z, f z).re - (f 0).re) ≤ energy g C := by
  let a := (∫ z, f z).re
  let b := (f 0).re
  have hc : Continuous (fun ε : ℝ => 2*a-a*(1+ε)^2-b) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => 2*a-a*(1+ε)^2-b) (𝓝[>] (0 : ℝ)) (𝓝 (a-b)) := by
    convert (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds using 1
    congr 1
    ring
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  apply le_of_tendsto he
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact density_lp_epsilon f hreal hpos g hminor hD hε

end TriangularUniversal
end

end OAI
