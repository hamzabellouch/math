import OAI.NumberTheory.DukePrimeDegree.Dynamics.IntegrableCoboundary

namespace OAI

/-! # One-sided integrable bounds for measurable coboundaries

The normalization transfer in the leaf-information identity need not be
integrable. A one-sided integrable bound on its difference is sufficient.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

lemma realClamp_monotone (M : ℝ) : Monotone (realClamp M) := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

theorem integrable_coboundary_of_lower_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) {f b : Y → ℝ}
    (hf : StronglyMeasurable f) (hb : Integrable b μ)
    (hlower : ∀ᵐ y ∂μ, -|b y| ≤ f y-f (T y)) :
    Integrable (fun y => f y-f (T y)) μ := by
  let F : ℕ → Y → ℝ := fun n y => realClamp n (f y)
  let D : ℕ → Y → ℝ := fun n y => F n y-F n (T y)
  have hFm (n : ℕ) : StronglyMeasurable (F n) :=
    (realClamp_lipschitz n).continuous.comp_stronglyMeasurable hf
  have hFi (n : ℕ) : Integrable (F n) μ := by
    apply (integrable_const (n:ℝ)).mono' (hFm n).aestronglyMeasurable
    exact ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs] using realClamp_abs_le (Nat.cast_nonneg n) (f y)
  have hDi (n : ℕ) : Integrable (D n) μ :=
    (hFi n).sub (hT.integrable_comp_of_integrable (hFi n))
  have hzero (n : ℕ) : (∫ y, D n y ∂μ)=0 :=
    integral_coboundary_eq_zero μ hT (hFm n) (hDi n)
  have hnegative (n : ℕ) : ∀ᵐ y ∂μ, (D n y)⁻ ≤ |b y| := by
    filter_upwards [hlower] with y hy
    change max (-(D n y)) 0 ≤ |b y|
    apply max_le _ (abs_nonneg _)
    by_cases h : f (T y) ≤ f y
    · have hm := realClamp_monotone (n:ℝ) h
      change -(realClamp n (f y)-realClamp n (f (T y))) ≤ _
      exact (neg_nonpos.mpr (sub_nonneg.mpr hm)).trans (abs_nonneg _)
    · have hd := realClamp_difference_le n (f y) (f (T y))
      rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))] at hd
      change -(realClamp n (f y)-realClamp n (f (T y))) ≤ _
      exact (neg_le_abs _).trans (hd.trans (by linarith))
  have hL1 (n : ℕ) : (∫ y, ‖D n y‖ ∂μ) ≤ 2 * ∫ y, |b y| ∂μ := by
    simp only [Real.norm_eq_abs]
    rw [integral_abs_eq_two_mul_integral_negPart_add_integral (hDi n), hzero, add_zero]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact integral_mono_ae ((hDi n).neg.sup (integrable_const 0)) hb.abs (hnegative n)
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n => D n y) atTop (𝓝 (f y-f (T y))) := by
    apply ae_of_all
    intro y
    obtain ⟨N,hN⟩ := exists_nat_gt (max |f y| |f (T y)|)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N:ℝ) ≤ n := Nat.cast_le.mpr hn
    have hy : |f y| ≤ (n:ℝ) := (le_max_left _ _).trans hN.le |>.trans hn'
    have hTy : |f (T y)| ≤ (n:ℝ) := (le_max_right _ _).trans hN.le |>.trans hn'
    simp only [D,F,realClamp_eq hy,realClamp_eq hTy]
  have hFatou : (∫⁻ y, ‖f y-f (T y)‖ₑ ∂μ) ≤
      liminf (fun n => ∫⁻ y, ‖D n y‖ₑ ∂μ) atTop := by
    calc
      _ = ∫⁻ y, liminf (fun n => ‖D n y‖ₑ) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono fun _ hy => hy.enorm.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' fun n => (hDi n).aestronglyMeasurable.aemeasurable.enorm
  have hbound : liminf (fun n => ∫⁻ y, ‖D n y‖ₑ ∂μ) atTop ≤
      ENNReal.ofReal (2 * ∫ y, |b y| ∂μ) := by
    apply le_trans (liminf_le_liminf (Eventually.of_forall (fun n => ?_)))
      (le_of_eq (liminf_const _))
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hDi n)]
    exact ENNReal.ofReal_le_ofReal (hL1 n)
  refine ⟨(hf.sub (hf.comp_measurable hT.measurable)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (hFatou.trans hbound).trans_lt ENNReal.ofReal_lt_top

/-- A nonnegative information function differing from an integrable
reference by a measurable coboundary has the same integral. -/
theorem information_integrable_integral_of_coboundary {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) {f J I : Y → ℝ}
    (hf : StronglyMeasurable f) (hJ : Integrable J μ)
    (hI : ∀ᵐ y ∂μ, 0 ≤ I y)
    (heq : I =ᵐ[μ] fun y => J y + (f y-f (T y))) :
    Integrable I μ ∧ (∫ y, I y ∂μ) = ∫ y, J y ∂μ := by
  have hd := integrable_coboundary_of_lower_bound μ hT hf hJ (by
    filter_upwards [hI, heq] with y hy he
    have hj := le_abs_self (J y)
    linarith)
  refine ⟨(hJ.add hd).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_add hJ hd,
    integral_coboundary_eq_zero μ hT hf hd, add_zero]

/-- Null-set changes in the transfer do not affect the information identity. -/
theorem information_integrable_integral_of_ae_coboundary {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) {f J I : Y → ℝ}
    (hf : AEStronglyMeasurable f μ) (hJ : Integrable J μ)
    (hI : ∀ᵐ y ∂μ, 0 ≤ I y)
    (heq : I =ᵐ[μ] fun y => J y + (f y-f (T y))) :
    Integrable I μ ∧ (∫ y, I y ∂μ) = ∫ y, J y ∂μ := by
  apply information_integrable_integral_of_coboundary μ hT
    hf.stronglyMeasurable_mk hJ hI
  filter_upwards [heq, hf.ae_eq_mk, hT.quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk]
    with y hy hf₀ hf₁
  change f (T y) = hf.mk f (T y) at hf₁
  rwa [hf₀, hf₁] at hy

end DukePrimeDegree

end

end OAI
