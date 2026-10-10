import Mathlib
import OAI.Probability.SphericalField.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem weighted_kernel_homogeneous_eq_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NeZero μ] {D : X → ℝ} {K : X → X → ℝ} {B : ℝ}
    (hB : B < 1) (hD : ∀ᵐ r ∂μ, 0 < D r)
    (hK : ∀ r, Integrable (K r) μ) (hKpos : ∀ᵐ r ∂μ, ∀ᵐ s ∂μ, 0 ≤ K r s)
    (hrow : ∀ᵐ r ∂μ, (∫ s, K r s ∂μ) ≤ B * D r)
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hbounded : ∃ M : ℝ, ∀ᵐ r ∂μ, |f r| ≤ M)
    (heq : ∀ᵐ r ∂μ, f r * D r = ∫ s, K r s * f s ∂μ) :
    f =ᵐ[μ] 0 := by
  let C : ℝ := essSup (fun r => |f r|) μ
  obtain ⟨M, hM⟩ := hbounded
  have hb : IsBoundedUnder (· ≤ ·) (ae μ) (fun r => |f r|) :=
    isBoundedUnder_of_eventually_le hM
  have hcob : IsCoboundedUnder (· ≤ ·) (ae μ) (fun r => |f r|) :=
    isCoboundedUnder_le_of_le (ae μ) (fun r => abs_nonneg (f r))
  have hfC : ∀ᵐ r ∂μ, |f r| ≤ C := ae_le_essSup hb
  have hC : 0 ≤ C := by
    obtain ⟨r, hr⟩ := hfC.exists
    exact (abs_nonneg (f r)).trans hr
  have hsmall : ∀ᵐ r ∂μ, |f r| ≤ B * C := by
    filter_upwards [hD, hKpos, hrow, heq] with r hrD hrK hrrow hreq
    have hbound : ∀ᵐ s ∂μ, ‖K r s * f s‖ ≤ K r s * C := by
      filter_upwards [hrK, hfC] with s hsK hsC
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsK]
      exact mul_le_mul_of_nonneg_left hsC hsK
    have hi : Integrable (fun s => K r s * f s) μ :=
      ((hK r).mul_const C).mono' ((hK r).aestronglyMeasurable.mul hf) hbound
    have hh : |f r| * D r ≤ B * D r * C := by
      calc
        |f r| * D r = |f r * D r| := by rw [abs_mul, abs_of_pos hrD]
        _ = |∫ s, K r s * f s ∂μ| := by rw [hreq]
        _ ≤ ∫ s, ‖K r s * f s‖ ∂μ := by
          simpa only [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (fun s => K r s * f s) (μ := μ))
        _ ≤ ∫ s, K r s * C ∂μ :=
          integral_mono_ae hi.norm ((hK r).mul_const C) hbound
        _ = (∫ s, K r s ∂μ) * C := integral_mul_const C (K r)
        _ ≤ B * D r * C := mul_le_mul_of_nonneg_right hrrow hC
    nlinarith
  have hCC : C ≤ B * C := essSup_le_of_ae_le (B * C) hsmall hcob
  have hC0 : C = 0 := by nlinarith
  filter_upwards [hfC] with r hr
  exact abs_eq_zero.mp (le_antisymm (by simpa only [hC0] using hr) (abs_nonneg _))

def sphereKernel (r s : Time) : ℝ := min (r : ℝ) (s : ℝ) - (r : ℝ) * (s : ℝ)

def sphereTail (μ : Measure Time) (r : Time) : ℝ :=
  ∫ s, 1 - max (r : ℝ) (s : ℝ) ∂μ

lemma sphereKernel_nonneg (r s : Time) : 0 ≤ sphereKernel r s := by
  unfold sphereKernel
  rcases le_total (r : ℝ) (s : ℝ) with h | h
  · rw [min_eq_left h]
    nlinarith [r.property.1, s.property.2]
  · rw [min_eq_right h]
    nlinarith [s.property.1, r.property.2]

lemma sphereKernel_le_weight (r s : Time) :
    sphereKernel r s ≤ (r : ℝ) * (1 - max (r : ℝ) (s : ℝ)) := by
  unfold sphereKernel
  rcases le_total (r : ℝ) (s : ℝ) with h | h
  · rw [min_eq_left h, max_eq_right h]
    ring_nf
    exact le_rfl
  · rw [min_eq_right h, max_eq_left h]
    nlinarith [r.property.2]

lemma sphereTail_integrable (μ : Measure Time) [IsFiniteMeasure μ] (r : Time) :
    Integrable (fun s : Time => 1 - max (r : ℝ) (s : ℝ)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    have := r.property.2
    have := s.property.2
    simp only [sub_nonneg, max_le_iff]
    exact ⟨‹_›, ‹_›⟩)]
  have h := r.property.1
  have hh : (r : ℝ) ≤ max (r : ℝ) (s : ℝ) := le_max_left _ _
  linarith

lemma sphereKernel_integrable (μ : Measure Time) [IsFiniteMeasure μ] (r : Time) :
    Integrable (sphereKernel r) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereKernel; fun_prop)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereKernel_nonneg r s)]
  have h := sphereKernel_le_weight r s
  have hmax : 0 ≤ max (r : ℝ) (s : ℝ) := r.property.1.trans (le_max_left _ _)
  nlinarith [r.property.1, r.property.2]

lemma sphereTail_lower (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) {r : Time} (hr : (r : ℝ) ≤ B) :
    1 - B ≤ sphereTail μ r := by
  calc
    _ = ∫ _ : Time, 1 - B ∂μ := by simp
    _ ≤ _ := integral_mono_ae (integrable_const _) (sphereTail_integrable μ r) (by
      filter_upwards [hμ] with s hs
      exact sub_le_sub_left (max_le hr hs) 1)

lemma sphereKernel_row_bound (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} {r : Time} (hr : (r : ℝ) ≤ B) :
    (∫ s, sphereKernel r s ∂μ) ≤ B * sphereTail μ r := by
  have htail : 0 ≤ sphereTail μ r := integral_nonneg (fun s =>
    sub_nonneg.mpr (max_le r.property.2 s.property.2))
  calc
    _ ≤ ∫ s, (r : ℝ) * (1 - max (r : ℝ) (s : ℝ)) ∂μ :=
      integral_mono (sphereKernel_integrable μ r) ((sphereTail_integrable μ r).const_mul _)
        (sphereKernel_le_weight r)
    _ = (r : ℝ) * sphereTail μ r := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hr htail

theorem sphere_equation_unique (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B)
    {a b : Time → ℝ} (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (haBound : ∃ C : ℝ, ∀ᵐ r ∂μ, |a r| ≤ C)
    (hbBound : ∃ C : ℝ, ∀ᵐ r ∂μ, |b r| ≤ C)
    (haEq : ∀ᵐ r ∂μ, a r * sphereTail μ r = (r : ℝ) + ∫ s, sphereKernel r s * a s ∂μ)
    (hbEq : ∀ᵐ r ∂μ, b r * sphereTail μ r = (r : ℝ) + ∫ s, sphereKernel r s * b s ∂μ) :
    a =ᵐ[μ] b := by
  obtain ⟨A, hA⟩ := haBound
  obtain ⟨B', hB'⟩ := hbBound
  have hzero : (fun r => a r - b r) =ᵐ[μ] 0 :=
    weighted_kernel_homogeneous_eq_zero μ (D := sphereTail μ) (K := sphereKernel) hB
      (by filter_upwards [hμ] with r hr; have := sphereTail_lower μ hμ hr; linarith)
      (sphereKernel_integrable μ)
      (Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall (sphereKernel_nonneg r))
      (by filter_upwards [hμ] with r hr; exact sphereKernel_row_bound μ hr)
      (ha.sub hb)
      ⟨A + B', by
        filter_upwards [hA, hB'] with r hAr hBr
        exact (abs_sub (a r) (b r)).trans (add_le_add hAr hBr)⟩
      (by
        filter_upwards [haEq, hbEq] with r har hbr
        have hai : Integrable (fun s => sphereKernel r s * a s) μ := by
          apply ((sphereKernel_integrable μ r).mul_const A).mono'
            ((sphereKernel_integrable μ r).aestronglyMeasurable.mul ha)
          filter_upwards [hA] with s hs
          change |sphereKernel r s * _| ≤ _
          rw [abs_mul, abs_of_nonneg (sphereKernel_nonneg r s)]
          exact mul_le_mul_of_nonneg_left hs (sphereKernel_nonneg r s)
        have hbi : Integrable (fun s => sphereKernel r s * b s) μ := by
          apply ((sphereKernel_integrable μ r).mul_const B').mono'
            ((sphereKernel_integrable μ r).aestronglyMeasurable.mul hb)
          filter_upwards [hB'] with s hs
          change |sphereKernel r s * _| ≤ _
          rw [abs_mul, abs_of_nonneg (sphereKernel_nonneg r s)]
          exact mul_le_mul_of_nonneg_left hs (sphereKernel_nonneg r s)
        simp_rw [mul_sub]
        rw [integral_sub hai hbi, sub_mul, har, hbr]
        ring)
  filter_upwards [hzero] with r hr
  exact sub_eq_zero.mp hr

lemma sphereTail_nonneg (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    0 ≤ sphereTail μ r := integral_nonneg (fun s =>
      sub_nonneg.mpr (max_le r.property.2 s.property.2))

lemma sphereTail_upper (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    sphereTail μ r ≤ 1 - (r : ℝ) := by
  calc
    _ ≤ ∫ _ : Time, 1 - (r : ℝ) ∂μ :=
      integral_mono (sphereTail_integrable μ r) (integrable_const _)
        (fun s => sub_le_sub_left (le_max_left _ _) 1)
    _ = _ := by simp

theorem sphere_equation_support_bound (μ : Measure Time) [IsProbabilityMeasure μ]
    {a : Time → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (haNonneg : ∀ᵐ r ∂μ, 0 ≤ a r) (haBound : ∀ᵐ r ∂μ, a r ≤ A)
    (haEq : ∀ᵐ r ∂μ, a r * sphereTail μ r = (r : ℝ) + ∫ s, sphereKernel r s * a s ∂μ) :
    ∀ᵐ r : Time ∂μ, (r : ℝ) ≤ A / (1 + A) := by
  filter_upwards [haBound, haEq] with r har heq
  have hint : 0 ≤ ∫ s, sphereKernel r s * a s ∂μ :=
    integral_nonneg_of_ae (by
      filter_upwards [haNonneg] with s hs
      exact mul_nonneg (sphereKernel_nonneg r s) hs)
  have hineq : (r : ℝ) ≤ A * (1 - (r : ℝ)) := by
    calc
      _ ≤ a r * sphereTail μ r := by linarith
      _ ≤ A * sphereTail μ r := mul_le_mul_of_nonneg_right har (sphereTail_nonneg μ r)
      _ ≤ _ := mul_le_mul_of_nonneg_left (sphereTail_upper μ r) hA
  apply (le_div_iff₀ (by linarith : 0 < 1 + A)).mpr
  nlinarith

end SphericalPerceptron
end
end

end OAI
