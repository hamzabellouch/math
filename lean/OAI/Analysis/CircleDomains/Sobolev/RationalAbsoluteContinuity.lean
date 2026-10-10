import OAI.Analysis.CircleDomains.Topology.RationalIntervalControl
import OAI.Analysis.CircleDomains.Sobolev.LineLIntegralAbsoluteContinuity
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! Countably many rational interval estimates suffice for local absolute
continuity. This is the passage needed after the common full-measure set
of physical slice bounds has been selected. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

 theorem lintegral_bound_of_rational_enclosures {g : ℝ → ℝ≥0∞}
    {a b x y : ℝ} (hax : a < x) (hyb : y < b)
    (hfin : (∫⁻ t in Icc a b, g t) < ∞) (c : ℝ≥0∞)
    (h : ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < x →
      y < (q : ℝ) → (q : ℝ) < b → c ≤ ∫⁻ t in Icc (p : ℝ) q, g t) :
    c ≤ ∫⁻ t in Icc x y, g t := by
  have hμfin : (volume.withDensity g) (Icc a b) < ∞ := by
    rwa [withDensity_apply _ measurableSet_Icc]
  have hh := le_measure_Icc_of_rational_enclosures (volume.withDensity g) hax hyb hμfin c
    (fun p q hp hpx hyq hq => by
      rw [withDensity_apply _ measurableSet_Icc]
      exact h p q hp hpx hyq hq)
  rwa [withDensity_apply _ measurableSet_Icc] at hh

 theorem locally_absolutelyContinuous_of_rational_bounds
    {X : Type*} [PseudoMetricSpace X] (f : ℝ → X) (g : ℝ → ℝ≥0∞)
    {a b c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hfin : (∫⁻ t in Icc a b, g t) < ∞)
    (hbound : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x < y →
      ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < x →
        y < (q : ℝ) → (q : ℝ) < b →
          ENNReal.ofReal (dist (f x) (f y)) ≤ ∫⁻ t in Icc (p : ℝ) q, g t) :
    AbsolutelyContinuousOnInterval f c d := by
  have hsub : Icc c d ⊆ Ioo a b := fun _ hx => ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩
  have hcdab : Icc c d ⊆ Icc a b := Icc_subset_Icc hac.le hdb.le
  have hfin' : (∫⁻ t in uIoc c d, g t) < ∞ := by
    apply (lintegral_mono_set ?_).trans_lt hfin
    rw [uIoc_of_le hcd]
    exact Ioc_subset_Icc_self.trans hcdab
  apply absolutelyContinuousOnInterval_of_lintegral_bound hfin'
  intro x hx y hy
  rw [uIcc_of_le hcd] at hx hy
  have hseg (u v : ℝ) (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (huv : u < v) :
      ENNReal.ofReal (dist (f u) (f v)) ≤ ∫⁻ t in uIoc u v, g t := by
    rw [uIoc_of_le huv.le]
    have he : (∫⁻ t in Ioc u v, g t) = ∫⁻ t in Icc u v, g t :=
      setLIntegral_congr Ioc_ae_eq_Icc
    rw [he]
    exact lintegral_bound_of_rational_enclosures (hsub hu).1 (hsub hv).2 hfin _
      (hbound u (hsub hu) v (hsub hv) huv)
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact hseg x y hx hy hxy
  · subst y
    simp only [dist_self, ENNReal.ofReal_zero, zero_le]
  · simpa only [dist_comm, uIoc_comm y x] using hseg y x hy hx hyx

end CircleDomainRigidity

end OAI
