import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! The interval energy estimate needed for the low-frequency part of
the smooth-convolution versus cell-average comparison. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem integral_square_le_mass_mul_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (g : Ω → ℝ)
    (hg : MemLp g 2 μ) (hgn : 0 ≤ᵐ[μ] g) :
    (∫ x, g x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, g x ^ 2 ∂μ := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ)) (g := g) (by filter_upwards; norm_num) hgn
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ))
    (by simpa using hg)
  simp only [one_mul, integral_const, smul_eq_mul, mul_one, Real.rpow_two,
    one_pow] at h
  have hsq := pow_le_pow_left₀ (integral_nonneg_of_ae hgn) h 2
  have heq (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  rwa [mul_pow, heq _ measureReal_nonneg, heq _ (integral_nonneg fun _ => sq_nonneg _)] at hsq

theorem interval_pair_energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ ^ 2 ≤ (b - a) * ∫ t in Icc a b, ‖deriv f t‖ ^ 2 := by
  have hd1 : IntegrableOn (fun t => ‖deriv f t‖) (Icc a b) := hd.norm.integrable (by norm_num)
  have htotal : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      ‖f v - f u‖ ≤ ∫ t in Icc a b, ‖deriv f t‖ := by
    intro u hu v hv huv
    have hsub : Icc u v ⊆ Icc a b := fun t ht => ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩
    have hraw := norm_sub_le_integral_of_norm_deriv_le_of_le huv
      (fun t ht => (hf t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hf t (hsub ⟨ht.1.le,ht.2.le⟩)).differentiableWithinAt)
      (B := fun t => ‖deriv f t‖) (by filter_upwards; intros; rfl)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr (hd1.mono_set hsub))
    refine hraw.trans ?_
    rw [intervalIntegral.integral_of_le huv]
    exact setIntegral_mono_set hd1 (by filter_upwards with t; exact norm_nonneg _)
      (Filter.Eventually.of_forall fun t ht => hsub ⟨ht.1.le,ht.2⟩)
  have hnorm : ‖f x - f y‖ ≤ ∫ t in Icc a b, ‖deriv f t‖ := by
    rcases le_total x y with hxy | hyx
    · rw [norm_sub_rev]
      exact htotal x hx y hy hxy
    · exact htotal y hy x hx hyx
  have hcauchy := integral_square_le_mass_mul_square (volume.restrict (Icc a b))
    (fun t => ‖deriv f t‖) hd.norm (by filter_upwards with t; exact norm_nonneg _)
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hmass] at hcauchy
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcauchy

theorem norm_sub_mean_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (hf : Integrable f μ)
    (hm : 0 < μ.real univ) (v : E) (B : ℝ)
    (hbound : ∀ᵐ y ∂μ, ‖v - f y‖ ≤ B) :
    ‖v - (μ.real univ)⁻¹ • ∫ y, f y ∂μ‖ ≤ B := by
  have heq : v - (μ.real univ)⁻¹ • ∫ y, f y ∂μ =
      (μ.real univ)⁻¹ • ∫ y, (v - f y) ∂μ := by
    rw [integral_sub (integrable_const v) hf, integral_const,
      smul_sub, smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  calc
    _ ≤ (μ.real univ)⁻¹ * (B * μ.real univ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const hbound) (inv_nonneg.mpr hm.le)
    _ = B := by rw [mul_comm B, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]

/-- Pointwise Poincaré on one interval, with the actual integral mean. -/
theorem interval_mean_energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x - (b - a)⁻¹ • ∫ y in Icc a b, f y‖ ^ 2 ≤
      (b - a) * ∫ y in Icc a b, ‖deriv f y‖ ^ 2 := by
  let energy := (b - a) * ∫ y in Icc a b, ‖deriv f y‖ ^ 2
  have he : 0 ≤ energy := mul_nonneg (sub_nonneg.mpr hab.le)
    (integral_nonneg fun _ => sq_nonneg _)
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have hcont : ContinuousOn f (Icc a b) := fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hbound : ∀ᵐ y ∂volume.restrict (Icc a b), ‖f x - f y‖ ≤ Real.sqrt energy := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt he]
    exact interval_pair_energy f hab.le hf hd hx hy
  have h := norm_sub_mean_le (volume.restrict (Icc a b)) f hcont.integrableOn_Icc
    (by rw [hmass]; exact sub_pos.mpr hab) (f x) (Real.sqrt energy) hbound
  rw [hmass] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [Real.sq_sqrt he] at hsq

/-- Integrated Poincaré with the interval length squared, independent
of the dimension of the Hilbert packet space. -/
theorem interval_poincare {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) :
    (∫ x in Icc a b, ‖f x - (b - a)⁻¹ • ∫ y in Icc a b, f y‖ ^ 2) ≤
      (b - a) ^ 2 * ∫ x in Icc a b, ‖deriv f x‖ ^ 2 := by
  have hcont : ContinuousOn f (Icc a b) := fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have herr : IntegrableOn
      (fun x => ‖f x - (b - a)⁻¹ • ∫ y in Icc a b, f y‖ ^ 2) (Icc a b) volume :=
    ((hcont.sub continuousOn_const).norm.pow 2).integrableOn_Icc
  have h := integral_mono_ae herr (integrable_const
    ((b - a) * ∫ x in Icc a b, ‖deriv f x‖ ^ 2))
    ((ae_restrict_mem measurableSet_Icc).mono fun x hx => interval_mean_energy f hab hf hd hx)
  rw [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] at h
  simpa only [pow_two, mul_assoc] using h

theorem interval_poincare_Ico {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) :
    (∫ x in Ico a b, ‖f x - (b - a)⁻¹ • ∫ y in Ico a b, f y‖ ^ 2) ≤
      (b - a) ^ 2 * ∫ x in Ico a b, ‖deriv f x‖ ^ 2 := by
  simpa only [integral_Icc_eq_integral_Ico] using interval_poincare f hab hf hd

end LipschitzHilbert

end

end OAI
