import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.Compact
import OAI.Geometry.NodalSets.Elliptic.AnchoredIntervalBound

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
open scoped ContDiff
noncomputable section

lemma real_interval_square_variation (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (ha : a ∈ Icc (-1:ℝ) 1) (hb : b ∈ Icc (-1:ℝ) 1) :
    |f b^2-f a^2| ≤ ∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2) := by
  have hcont : Continuous (fun t ↦ f t^2+(deriv f t)^2) :=
    (hf.continuous.pow 2).add ((hf.continuous_deriv (by simp)).pow 2)
  have hpos (t : ℝ) : 0 ≤ f t^2+(deriv f t)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hder (t : ℝ) : ‖deriv (fun s ↦ f s^2) t‖ ≤ f t^2+(deriv f t)^2 := by
    have he : deriv (fun s ↦ f s^2) t = 2*f t*deriv f t := by
      simpa only [Pi.pow_apply,Nat.cast_ofNat,show 2-1=1 from rfl,pow_one] using
        ((hf.differentiable (by simp) t).hasDerivAt.fun_pow 2).deriv
    rw [he,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (f t+deriv f t)],
      by nlinarith [sq_nonneg (f t-deriv f t)]⟩
  have hordered (c d : ℝ) (hc : c ∈ Icc (-1:ℝ) 1) (hd : d ∈ Icc (-1:ℝ) 1)
      (hcd : c ≤ d) : |f d^2-f c^2| ≤ ∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2) := by
    have h := norm_sub_le_integral_of_norm_deriv_le_of_le hcd
      (hf.pow 2).continuous.continuousOn ((hf.pow 2).differentiable (by simp)).differentiableOn
      (Filter.Eventually.of_forall (fun t _ ↦ hder t)) (hcont.intervalIntegrable c d)
    rw [intervalIntegral.integral_of_le hcd] at h
    have hm : (∫ t in Ioc c d, (f t^2+(deriv f t)^2)) ≤
        ∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2) := by
      apply setIntegral_mono_set (hcont.continuousOn.integrableOn_compact isCompact_Icc)
        (Filter.Eventually.of_forall hpos)
      exact Filter.Eventually.of_forall (fun t ht ↦ ⟨hc.1.trans ht.1.le,ht.2.trans hd.2⟩)
    have hh : |f d^2-f c^2| ≤ ∫ t in Ioc c d, (f t^2+(deriv f t)^2) := by
      simpa only [Real.norm_eq_abs] using h
    exact hh.trans hm
  rcases le_total a b with hab | hba
  · exact hordered a b ha hb hab
  · simpa only [abs_sub_comm] using hordered b a hb ha hba

theorem real_interval_l2_embedding (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    f x^2 ≤ 2*(∫ t in Icc (-1:ℝ) 1, (f t^2+(deriv f t)^2)) := by
  have hfi : IntegrableOn (fun t ↦ f t^2) (Icc (-1:ℝ) 1) :=
    (hf.continuous.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hdi : IntegrableOn (fun t ↦ (deriv f t)^2) (Icc (-1:ℝ) 1) :=
    ((hf.continuous_deriv (by simp)).pow 2).continuousOn.integrableOn_compact isCompact_Icc
  obtain ⟨y,hy,hmin⟩ := isCompact_Icc.exists_isMinOn (show (Icc (-1:ℝ) 1).Nonempty from ⟨0,by norm_num⟩)
    (hf.continuous.pow 2).continuousOn
  have hm := setIntegral_mono_on
    (integrableOn_const (isCompact_Icc.measure_ne_top (μ := volume))) hfi measurableSet_Icc
    (fun t ht ↦ hmin ht)
  have hm' : 2*f y^2 ≤ ∫ t in Icc (-1:ℝ) 1, f t^2 := by
    norm_num at hm
    exact hm
  have hd : 0 ≤ ∫ t in Icc (-1:ℝ) 1, (deriv f t)^2 := integral_nonneg (fun t ↦ sq_nonneg _)
  have hv := (le_abs_self (f x^2-f y^2)).trans (real_interval_square_variation f hf y x hy hx)
  rw [integral_add hfi hdi] at hv ⊢
  nlinarith [sq_nonneg (f y)]

end
end Yau.Geometry

end OAI
