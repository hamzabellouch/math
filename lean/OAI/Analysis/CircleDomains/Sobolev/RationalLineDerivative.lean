import OAI.Analysis.CircleDomains.Sobolev.RationalAbsoluteContinuity
import OAI.Analysis.CircleDomains.Sobolev.LineLIntegralDerivativeBound

namespace OAI

/-! The same rational interval estimates control the almost-everywhere
ordinary derivative by the actual measurable line density. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

 theorem locally_ae_abs_deriv_le_of_rational_bounds
    (f : ℝ → ℝ) (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    {a b c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hfin : (∫⁻ t in Icc a b, g t) < ∞)
    (hbound : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x < y →
      ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < x →
        y < (q : ℝ) → (q : ℝ) < b →
          ENNReal.ofReal (dist (f x) (f y)) ≤ ∫⁻ t in Icc (p : ℝ) q, g t) :
    ∀ᵐ x ∂volume.restrict (Icc c d), |deriv f x| ≤ (g x).toReal := by
  have hsub : Icc c d ⊆ Ioo a b := fun _ hx => ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩
  have hcdab : Icc c d ⊆ Icc a b := Icc_subset_Icc hac.le hdb.le
  apply ae_abs_deriv_le_of_lintegral_bound hcd hg ((lintegral_mono_set hcdab).trans_lt hfin)
  intro x hx y hy
  have hseg (u v : ℝ) (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (huv : u < v) :
      ENNReal.ofReal (dist (f u) (f v)) ≤ ∫⁻ t in uIoc u v, g t := by
    rw [uIoc_of_le huv.le]
    have he : (∫⁻ t in Ioc u v, g t) = ∫⁻ t in Icc u v, g t :=
      setLIntegral_congr Ioc_ae_eq_Icc
    rw [he]
    exact lintegral_bound_of_rational_enclosures (hsub hu).1 (hsub hv).2 hfin _
      (hbound u (hsub hu) v (hsub hv) huv)
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · simpa only [Real.dist_eq] using hseg x y hx hy hxy
  · subst y
    simp only [sub_self, abs_zero, ENNReal.ofReal_zero, zero_le]
  · simpa only [Real.dist_eq, abs_sub_comm, uIoc_comm y x] using hseg y x hy hx hyx

end CircleDomainRigidity

end OAI
