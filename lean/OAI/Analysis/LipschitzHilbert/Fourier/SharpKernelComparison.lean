import OAI.Analysis.LipschitzHilbert.Fourier.DyadicKernelTelescoping
import OAI.Analysis.LipschitzHilbert.Estimates.TimeErrorEnvelope

namespace OAI

/-! The two endpoint envelopes control sharp truncation versus a telescoped
kernel. The profile conditions are local construction obligations. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def sharpTimeKernel (r R t : ℝ) : ℂ :=
  if r < |t| ∧ |t| < R then (t : ℂ)⁻¹ else 0

theorem profile_far_bound (a : ℝ → ℂ) (D : ℝ)
    (hfar : ∀ s, |s| *‖a s‖≤D) (r t : ℝ) (hr : 0<r) (ht : t≠0) :
    ‖a (t/r)‖≤D*r/|t| := by
  have hf : ‖a (t/r)‖*|t|/r≤D := by
    simpa only [abs_div,abs_of_pos hr,div_mul_eq_mul_div,mul_comm] using hfar (t/r)
  apply (le_div_iff₀ (abs_pos.mpr ht)).2
  exact (div_le_iff₀ hr).1 hf

theorem sharpKernelComparison_pointwise (a : ℝ → ℂ) (D : ℝ) (hD : 0≤D)
    (hnear : ∀ s, ‖a s+1‖≤D*|s|) (hfar : ∀ s, |s| *‖a s‖≤D)
    (r R : ℝ) (hr : 0<r) (hrR : r≤R) (t : ℝ) :
    ‖sharpTimeKernel r R t-profileKernelDifference a r R t‖≤
      4*D*(timeErrorEnvelope r t+timeErrorEnvelope R t) := by
  have hR : 0<R := hr.trans_le hrR
  have hqr := timeErrorEnvelope_nonneg r t hr
  have hqR := timeErrorEnvelope_nonneg R t hR
  by_cases ht0 : t=0
  · subst t
    have hs : ¬(r < |(0:ℝ)| ∧ |(0:ℝ)| < R) := by simp [not_lt_of_ge hr.le]
    simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,
      Complex.ofReal_zero,div_zero,sub_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) hD) (add_nonneg hqr hqR)
  have ht : 0 < |t| := abs_pos.mpr ht0
  have hnear_r : ‖a (t/r)+1‖≤D*(|t|/r) := by
    simpa only [abs_div,abs_of_pos hr] using hnear (t/r)
  have hnear_R : ‖a (t/R)+1‖≤D*(|t|/R) := by
    simpa only [abs_div,abs_of_pos hR] using hnear (t/R)
  have hfar_r := profile_far_bound a D hfar r t hr ht0
  have hfar_R := profile_far_bound a D hfar R t hR ht0
  by_cases hlo : |t|≤r
  · have hs : ¬(r < |t| ∧ |t| < R) := by intro h; linarith [h.1]
    have hnum : ‖a (t/r)-a (t/R)‖≤2*D*|t|/r := by
      have hn := norm_sub_le (a (t/r)+1) (a (t/R)+1)
      have hdiff : (a (t/r)+1)-(a (t/R)+1)=a (t/r)-a (t/R) := by ring
      rw [hdiff] at hn
      have hdiv := div_le_div_of_nonneg_left ht.le hr hrR
      calc
        _ ≤ D*(|t|/r)+D*(|t|/r) := hn.trans
          (add_le_add hnear_r (hnear_R.trans (mul_le_mul_of_nonneg_left hdiv hD)))
        _ = _ := by ring
    calc
      _ = ‖a (t/r)-a (t/R)‖/|t| := by
        simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,zero_sub,norm_neg,
          norm_div,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ (2*D*|t|/r)/|t| := div_le_div_of_nonneg_right hnum ht.le
      _ = 2*D*r⁻¹ := by field_simp
      _ ≤ 4*D*timeErrorEnvelope r t := by
        have h := mul_le_mul_of_nonneg_left (timeErrorEnvelope_small r t hr hlo) (mul_nonneg (by norm_num : (0:ℝ)≤2) hD)
        nlinarith only [h]
      _ ≤ _ := by nlinarith only [mul_nonneg hD hqR]
  · have htr : r < |t| := lt_of_not_ge hlo
    by_cases hhi : |t| < R
    · have hnum : ‖1-a (t/r)+a (t/R)‖≤D*r/|t|+D*(|t|/R) := by
        have heq : (1:ℂ)-a (t/r)+a (t/R)=(-a (t/r))+(a (t/R)+1) := by ring
        rw [heq]
        exact (norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using hfar_r) hnear_R)
      have hform : sharpTimeKernel r R t-profileKernelDifference a r R t=
          ((1:ℂ)-a (t/r)+a (t/R))/(t : ℂ) := by
        have hs : r < |t| ∧ |t| < R := ⟨htr,hhi⟩
        simp only [sharpTimeKernel,ite_eq_left hs,profileKernelDifference]
        field_simp
        ring
      calc
        _ = ‖1-a (t/r)+a (t/R)‖/|t| := by rw [hform,norm_div,Complex.norm_real,Real.norm_eq_abs]
        _ ≤ (D*r/|t|+D*(|t|/R))/|t| := div_le_div_of_nonneg_right hnum ht.le
        _ = D*(r/t^2)+D*R⁻¹ := by rw [←sq_abs t]; field_simp
        _ ≤ 2*D*timeErrorEnvelope r t+2*D*timeErrorEnvelope R t := by
          have hrb := mul_le_mul_of_nonneg_left (timeErrorEnvelope_large r t hr htr.le) hD
          have hRb := mul_le_mul_of_nonneg_left (timeErrorEnvelope_small R t hR hhi.le) hD
          nlinarith only [hrb,hRb]
        _ ≤ _ := by nlinarith only [mul_nonneg hD hqr,mul_nonneg hD hqR]
    · have hs : ¬(r < |t| ∧ |t| < R) := by intro h; exact hhi h.2
      have hnum : ‖a (t/r)-a (t/R)‖≤2*D*R/|t| := by
        have h := (norm_sub_le _ _).trans (add_le_add hfar_r hfar_R)
        have hmon := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrR hD) ht.le
        calc
          _ ≤ D*R/|t|+D*R/|t| := h.trans (add_le_add hmon (le_refl _))
          _ = _ := by ring
      calc
        _ = ‖a (t/r)-a (t/R)‖/|t| := by
          simp only [sharpTimeKernel,ite_eq_right hs,profileKernelDifference,zero_sub,norm_neg,
            norm_div,Complex.norm_real,Real.norm_eq_abs]
        _ ≤ (2*D*R/|t|)/|t| := div_le_div_of_nonneg_right hnum ht.le
        _ = 2*D*(R/t^2) := by rw [←sq_abs t]; field_simp
        _ ≤ 4*D*timeErrorEnvelope R t := by
          have h := mul_le_mul_of_nonneg_left
            (timeErrorEnvelope_large R t hR (le_of_not_gt hhi)) (mul_nonneg (by norm_num : (0:ℝ)≤2) hD)
          nlinarith only [h]
        _ ≤ _ := by nlinarith only [mul_nonneg hD hqr]

end LipschitzHilbert.PacketRepresentation

namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_measurable (r R : ℝ) : Measurable (sharpTimeKernel r R) := by
  unfold sharpTimeKernel
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

theorem sharpKernelComparison_integral (a : ℝ → ℂ) (ha : Measurable a)
    (D : ℝ) (hD : 0≤D) (hnear : ∀ s, ‖a s+1‖≤D*|s|)
    (hfar : ∀ s, |s| *‖a s‖≤D) (r R : ℝ) (hr : 0<r) (hrR : r≤R) :
    Integrable (fun t => sharpTimeKernel r R t-profileKernelDifference a r R t) ∧
      (∫ t, ‖sharpTimeKernel r R t-profileKernelDifference a r R t‖)≤8*Real.pi*D := by
  have hR := hr.trans_le hrR
  have hi := ((timeErrorEnvelope_integrable r hr).add
    (timeErrorEnvelope_integrable R hR)).const_mul (4*D)
  have hm : Measurable (fun t => sharpTimeKernel r R t-profileKernelDifference a r R t) := by
    apply (sharpTimeKernel_measurable r R).sub
    unfold profileKernelDifference
    exact ((ha.comp (by fun_prop)).sub (ha.comp (by fun_prop))).div (by fun_prop)
  have hb (t : ℝ) := sharpKernelComparison_pointwise a D hD hnear hfar r R hr hrR t
  have he := hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨he,?_⟩
  calc
    _ ≤ ∫ t, 4*D*(timeErrorEnvelope r t+timeErrorEnvelope R t) :=
      integral_mono he.norm hi hb
    _ = 8*Real.pi*D := by
      rw [integral_const_mul,integral_add (timeErrorEnvelope_integrable r hr)
        (timeErrorEnvelope_integrable R hR),timeErrorEnvelope_integral r hr,
        timeErrorEnvelope_integral R hR]
      ring

theorem finiteTimeKernel_sharp_integral (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (ha : Measurable a) (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (D : ℝ) (hD : 0≤D) (hnear : ∀ s, ‖a s+1‖≤D*|s|)
    (hfar : ∀ s, |s| *‖a s‖≤D) (N : ℕ) (topLength : ℝ) (htop : 0<topLength) :
    Integrable (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t) ∧
    (∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t‖)≤8*Real.pi*D := by
  have hr : 0<2*topLength/(2:ℝ)^N := by positivity
  have hrR : 2*topLength/(2:ℝ)^N≤2*topLength := by
    apply div_le_self (by positivity)
    exact one_le_pow₀ (by norm_num)
  have heq : (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
      finiteTimeKernel k N topLength t) =ᵐ[volume]
      (fun t => sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t) := by
    filter_upwards [volume.ae_ne (0:ℝ)] with t ht
    rw [finiteTimeKernel_eq_profileDifference k a hprofile N topLength htop t ht]
  obtain ⟨hi,hbound⟩ := sharpKernelComparison_integral a ha D hD hnear hfar _ _ hr hrR
  refine ⟨hi.congr heq.symm,?_⟩
  calc
    _ = ∫ t, ‖sharpTimeKernel (2*topLength/(2:ℝ)^N) (2*topLength) t-
        profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t‖ :=
      integral_congr_ae (heq.mono fun _ h => congrArg norm h)
    _ ≤ _ := hbound

end LipschitzHilbert.PacketRepresentation

end

end OAI
