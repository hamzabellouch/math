import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMeasurableDuhamel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Strong continuity of the Duhamel integral with merely integrable forcing -/

open Set MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

theorem integrableOn_homogeneous_backward_forcing (a b k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (r : ℝ → HomogeneousY a k) (hr : StronglyMeasurable r)
    (hir : IntegrableOn r (Icc 0 T)) :
    IntegrableOn (fun s => homogeneousFreeOperator a b k (-s) ha ha1 hk (r s)) (Icc 0 T) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    (((continuous_homogeneousFreeBound a k).comp continuous_neg).continuousOn)
  have hm : StronglyMeasurable (fun s => homogeneousFreeOperator a b k (-s) ha ha1 hk (r s)) :=
    (continuous_homogeneousFreeOperator_uncurry a b k ha ha1 hk).comp_stronglyMeasurable
      (continuous_neg.stronglyMeasurable.prodMk hr)
  apply (hir.norm.mul_const C).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hc : homogeneousFreeBound a k (-s) ≤ C :=
    (le_abs_self _).trans (by simpa only [Function.comp_def, Real.norm_eq_abs] using hC s hs)
  exact (homogeneousFreeOperator_norm_le a b k (-s) ha ha1 hk (r s)).trans
    ((mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem homogeneousDuhamel_factor_free (a b k T t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ht : t ∈ Icc 0 T)
    (r : ℝ → HomogeneousY a k) (hr : StronglyMeasurable r)
    (hir : IntegrableOn r (Icc 0 T)) :
    homogeneousDuhamel a b k ha ha1 hk t r =
      homogeneousFreeOperator a b k t ha ha1 hk
        (∫ s in Icc 0 t, homogeneousFreeOperator a b k (-s) ha ha1 hk (r s)) := by
  have hi := (integrableOn_homogeneous_backward_forcing a b k T ha ha1 hk r hr hir).mono_set
    (show Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T from fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
  rw [homogeneousDuhamel, intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc,
    ← (homogeneousFreeOperator a b k t ha ha1 hk).integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [← homogeneousFreeOperator_add, sub_eq_add_neg]

theorem continuousOn_homogeneousDuhamel_measurable (a b k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (r : ℝ → HomogeneousY a k) (hr : StronglyMeasurable r)
    (hir : IntegrableOn r (Icc 0 T)) :
    ContinuousOn (fun t => homogeneousDuhamel a b k ha ha1 hk t r) (Icc 0 T) := by
  have hi := integrableOn_homogeneous_backward_forcing a b k T ha ha1 hk r hr hir
  have hp := intervalIntegral.continuousOn_primitive_Icc hi
  have hc := (continuous_homogeneousFreeOperator_uncurry a b k ha ha1 hk).comp_continuousOn
    (continuousOn_id.prodMk hp)
  apply hc.congr
  intro t ht
  exact homogeneousDuhamel_factor_free a b k T t ha ha1 hk ht r hr hir

end DefocusingNLS

end OAI
