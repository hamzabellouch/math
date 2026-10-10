import OAI.Geometry.NodalSets.Elliptic.RealIntegralSquare
import OAI.Geometry.NodalSets.Elliptic.RealIntervalL2Embedding

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
open scoped ContDiff
noncomputable section

lemma real_interval_integral_square_le (f : ℝ → ℝ) (hf : Continuous f)
    {a b : ℝ} (hab : a < b) :
    (∫ x in Icc a b, f x)^2 ≤ (b-a)*(∫ x in Icc a b, f x^2) := by
  have hm : (volume.restrict (Icc a b)).real univ=b-a := by simp [hab.le]
  have hpos : 0 < (volume.restrict (Icc a b)).real univ := by rw [hm]; linarith
  have h := real_integral_square_le (volume.restrict (Icc a b)) hpos f
    hf.continuousOn.integrableOn_Icc (hf.pow 2).continuousOn.integrableOn_Icc
  rwa [hm] at h

lemma real_interval_derivative_control (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (f x-f y)^2 ≤ (b-a)*(∫ t in Icc a b, (deriv f t)^2) := by
  have hd : Continuous (fun t ↦ |deriv f t|) := (hf.continuous_deriv (by simp)).abs
  have hordered (c d : ℝ) (hc : c ∈ Icc a b) (hd' : d ∈ Icc a b) (hcd : c ≤ d) :
      |f d-f c| ≤ ∫ t in Icc a b, |deriv f t| := by
    have hh := norm_sub_le_integral_of_norm_deriv_le_of_le hcd hf.continuous.continuousOn
      (hf.differentiable (by simp)).differentiableOn
      (Filter.Eventually.of_forall (fun t _ ↦ by rw [Real.norm_eq_abs])) (hd.intervalIntegrable c d)
    rw [intervalIntegral.integral_of_le hcd] at hh
    have hmono : (∫ t in Ioc c d, |deriv f t|) ≤ ∫ t in Icc a b, |deriv f t| := by
      apply setIntegral_mono_set hd.continuousOn.integrableOn_Icc
        (Filter.Eventually.of_forall (fun t ↦ abs_nonneg (deriv f t)))
      exact Filter.Eventually.of_forall (fun t ht ↦ ⟨hc.1.trans ht.1.le,ht.2.trans hd'.2⟩)
    exact (show |f d-f c| ≤ ∫ t in Ioc c d, |deriv f t| by simpa only [Real.norm_eq_abs] using hh).trans hmono
  have hvar : |f x-f y| ≤ ∫ t in Icc a b, |deriv f t| := by
    rcases le_total y x with h | h
    · exact hordered y x hy hx h
    · simpa only [abs_sub_comm] using hordered x y hx hy h
  have hsq := real_interval_integral_square_le (fun t ↦ |deriv f t|) hd hab
  simp only [sq_abs] at hsq
  have hn : 0 ≤ ∫ t in Icc a b, |deriv f t| := integral_nonneg (fun t ↦ abs_nonneg _)
  have hh := sq_le_sq₀ (abs_nonneg (f x-f y)) hn |>.mpr hvar
  rw [sq_abs] at hh
  exact hh.trans hsq

end
end Yau.Geometry

end OAI
