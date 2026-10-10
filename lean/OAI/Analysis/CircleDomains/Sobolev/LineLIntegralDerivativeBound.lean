import OAI.Analysis.CircleDomains.Sobolev.IncrementDerivativeBound
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! The path inequality is naturally extended-valued. On each finite
slice it bounds the ordinary derivative by the real density. -/

open Set Filter MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity

theorem ae_abs_deriv_le_of_lintegral_bound
    {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞} {a b : ℝ} (hab : a ≤ b)
    (hg : Measurable g) (hfinite : (∫⁻t in Icc a b, g t) < ∞)
    (hbound : ∀x ∈ Icc a b, ∀y ∈ Icc a b,
      ENNReal.ofReal |f x - f y| ≤ ∫⁻t in uIoc x y, g t) :
    ∀ᵐ x ∂volume.restrict (Icc a b), |deriv f x| ≤ (g x).toReal := by
  have hgint : Integrable (fun t => (g t).toReal) (volume.restrict (Icc a b)) :=
    integrable_toReal_of_lintegral_ne_top hg.aemeasurable hfinite.ne
  apply ae_abs_deriv_le_of_integral_bound hab
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hgint)
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  intro x hx y hy
  have hsub : uIoc x y ⊆ Icc a b :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc hx hy)
  have hfin : (∫⁻t in uIoc x y, g t) < ∞ :=
    (lintegral_mono_set hsub).trans_lt hfinite
  have hreal : |f x - f y| ≤ (∫⁻t in uIoc x y, g t).toReal := by
    exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 (hbound x hx y hy)
  rw [integral_toReal hg.aemeasurable (ae_lt_top hg hfin.ne)]
  exact hreal

end CircleDomainRigidity

end OAI
