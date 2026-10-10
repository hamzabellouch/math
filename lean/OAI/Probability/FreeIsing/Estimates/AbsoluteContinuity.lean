import Mathlib

namespace OAI

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Problem367

theorem absolutelyContinuousOnInterval_comp_lipschitzOn
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {a b : ℝ} {s : Set X} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : LipschitzOnWith K g s)
    (hfs : MapsTo f (uIcc a b) s) :
    AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  have hsmall := hfδ E hE hlen
  calc
    ∑ i ∈ Finset.range E.1, dist ((g ∘ f) (E.2 i).1) ((g ∘ f) (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (f (E.2 i).1) (f (E.2 i).2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hg.dist_le_mul _ (hfs (hE.1 i hi).1) _ (hfs (hE.1 i hi).2)
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hsmall.le K.2
    _ < ((K : ℝ) + 1) * (ε / (K + 1)) := by
      apply mul_lt_mul_of_pos_right (by linarith)
      positivity
    _ = ε := by field_simp

theorem absolutelyContinuousOnInterval_comp_contDiffOn_Icc
    {f g : ℝ → ℝ} {a b c d : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : ContDiffOn ℝ 1 g (Icc c d))
    (hfs : MapsTo f (uIcc a b) (Icc c d)) :
    AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  obtain ⟨K, hK⟩ := hg.exists_lipschitzOnWith (by decide) (convex_Icc c d) isCompact_Icc
  exact absolutelyContinuousOnInterval_comp_lipschitzOn hf hK hfs

theorem ac_le_add_integral_of_neg_le_deriv
    {f k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hk : IntervalIntegrable k volume a b)
    (hbound : ∀ᵐ x ∂volume.restrict (Icc a b), -k x ≤ deriv f x) :
    f a ≤ f b + ∫ x in a..b, k x := by
  have h := intervalIntegral.integral_mono_ae_restrict hab hk.neg
    hf.intervalIntegrable_deriv hbound
  simp only [Pi.neg_apply] at h
  rw [intervalIntegral.integral_neg, hf.integral_deriv_eq_sub] at h
  linarith

theorem ac_sub_le_integral_of_deriv_le
    {f k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hk : IntervalIntegrable k volume a b)
    (hbound : ∀ᵐ x ∂volume.restrict (Icc a b), deriv f x ≤ k x) :
    f b - f a ≤ ∫ x in a..b, k x := by
  rw [← hf.integral_deriv_eq_sub]
  exact intervalIntegral.integral_mono_ae_restrict hab hf.intervalIntegrable_deriv hk hbound

end Problem367

end

end OAI
