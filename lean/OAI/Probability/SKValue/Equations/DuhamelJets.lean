import Mathlib
import OAI.Probability.SKValue.Evolution.SmoothFamily

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

noncomputable def duhamel (a b : ℝ) (γ : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in a..b, γ s*heat (s-a) (F s) x

lemma BoundedSmoothFamily.duhamel_hasDerivAt {T a b : ℝ} {γ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (hi : IntervalIntegrable γ volume a b)
    (ha : 0≤a) (hab : a≤b) (hb : b≤T) (x : ℝ) :
    HasDerivAt (duhamel a b γ F) (duhamel a b γ (fun t ↦ _root_.deriv (F t)) x) x := by
  have hfi (u : ℝ) : IntervalIntegrable (fun s ↦ γ s*heat (s-a) (F s) u) volume a b := by
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hab] using (h.heat_continuousOn a u).mono (Icc_subset_Icc ha hb)
  have hf'i (u : ℝ) : IntervalIntegrable (fun s ↦ γ s*heat (s-a) (_root_.deriv (F s)) u) volume a b := by
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hab] using (h.deriv.heat_continuousOn a u).mono (Icc_subset_Icc ha hb)
  obtain ⟨C,hC,hbd⟩ := h.bound 1
  simp only [iteratedDeriv_one] at hbd
  have hi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u s ↦ γ s*heat (s-a) (F s) u)
    (F' := fun u s ↦ γ s*heat (s-a) (_root_.deriv (F s)) u)
    (s := univ) (bound := fun s ↦ |γ s| * C) (μ := volume.restrict (Ioc a b))
    univ_mem (Eventually.of_forall (fun u ↦ ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfi u)).aestronglyMeasurable))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfi x))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hf'i x)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      intro u _
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (heat_bound hC (hbd s ⟨ha.trans hs.1.le,hs.2.trans hb⟩) _ u) (abs_nonneg _))
    (hi'.abs.mul_const C)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      intro u _
      have hfs := h.slices s ⟨ha.trans hs.1.le,hs.2.trans hb⟩
      exact (heat_spatial_hasDerivAt
        (fun y ↦ (hfs.smooth.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) y).hasDerivAt)
        hfs.deriv.smooth.continuous hfs.expGrowth hfs.deriv.expGrowth u (s-a)).const_mul (γ s))
  change HasDerivAt (fun u ↦ ∫ s in a..b, γ s*heat (s-a) (F s) u)
    (∫ s in a..b, γ s*heat (s-a) (_root_.deriv (F s)) x) x
  simpa only [intervalIntegral.integral_of_le hab] using hd.2

lemma BoundedSmoothFamily.duhamel_deriv {T a b : ℝ} {γ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (hi : IntervalIntegrable γ volume a b)
    (ha : 0≤a) (hab : a≤b) (hb : b≤T) :
    _root_.deriv (duhamel a b γ F)=duhamel a b γ (fun t ↦ _root_.deriv (F t)) := by
  funext x
  exact (h.duhamel_hasDerivAt hi ha hab hb x).deriv

lemma BoundedSmoothFamily.iteratedDeriv {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (n : ℕ) :
    BoundedSmoothFamily T (fun t ↦ iteratedDeriv n (F t)) := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

lemma BoundedSmoothFamily.duhamel_iteratedDeriv {T a b : ℝ} {γ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (hi : IntervalIntegrable γ volume a b)
    (ha : 0≤a) (hab : a≤b) (hb : b≤T) (n : ℕ) :
    _root_.iteratedDeriv n (duhamel a b γ F)=duhamel a b γ (fun t ↦ _root_.iteratedDeriv n (F t)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih,(h.iteratedDeriv n).duhamel_deriv hi ha hab hb]
    simp only [iteratedDeriv_succ]

end SKValue

end

end OAI
