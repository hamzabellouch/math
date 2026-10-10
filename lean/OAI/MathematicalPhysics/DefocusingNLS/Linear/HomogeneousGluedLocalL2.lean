import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedOriginRegularity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! Origin regularity and a strict power bound give the required radial top energy. -/

open Set Filter MeasureTheory Topology
open scoped ContDiff
namespace DefocusingNLS

theorem homogeneousGlued_local_top_integrable (f : ℝ → ℂ) (N : ℕ)
    (R : ℝ) (hR : 0 < R) (hf : ContDiffOn ℝ ∞ f (Icc 0 R))
    (hs : ContDiffOn ℝ ∞ f (Ioi 0)) :
    IntegrableOn (fun r : ℝ => r ^ 11 * ‖iteratedDeriv N f r‖ ^ 2) (Ioc 0 R) := by
  have hu := uniqueDiffOn_Icc hR
  have hc := hf.continuousOn_iteratedDerivWithin (m := N) (by simp) hu
  have hi : IntegrableOn
      (fun r : ℝ => r ^ 11 * ‖iteratedDerivWithin N f (Icc 0 R) r‖ ^ 2) (Icc 0 R) :=
    ((continuousOn_id.pow 11).mul (hc.norm.pow 2)).integrableOn_Icc
  apply (hi.mono_set Ioc_subset_Icc_self).congr_fun
  · intro r hr
    dsimp only
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (((hs r hr.1).contDiffAt (Ioi_mem_nhds hr.1)).of_le (by simp)) ⟨hr.1.le, hr.2⟩]
  · exact measurableSet_Ioc

theorem homogeneousGlued_top_integrable (f : ℝ → ℂ) (N : ℕ) (s : ℝ)
    (hf : ∀ R : ℝ, 0 < R → ContDiffOn ℝ ∞ f (Icc 0 R))
    (hs : ContDiffOn ℝ ∞ f (Ioi 0)) (hexp : 11 + 2 * s < -1)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in atTop, ‖iteratedDeriv N f r‖ ≤ C * r ^ s) :
    IntegrableOn (fun r : ℝ => r ^ 11 * ‖iteratedDeriv N f r‖ ^ 2) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := hb
  obtain ⟨T, hT⟩ := eventually_atTop.mp hb
  let R := max T 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsD : ∀ j : ℕ, ContDiffOn ℝ ∞ (iteratedDeriv j f) (Ioi 0) := by
    intro j
    induction j with
    | zero => simpa using hs
    | succ j ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (by simp)
  have hsN : ContinuousOn (iteratedDeriv N f) (Ioi 0) := (hsD N).continuousOn
  have hc : ContinuousOn (fun r : ℝ => r ^ 11 * ‖iteratedDeriv N f r‖ ^ 2) (Ioi R) :=
    (continuousOn_id.pow 11).mul
      (((hsN.mono (Ioi_subset_Ioi hR.le)).norm).pow 2)
  have hi := (integrableOn_Ioi_rpow_of_lt hexp hR).const_mul (C ^ 2)
  have ht : IntegrableOn (fun r : ℝ => r ^ 11 * ‖iteratedDeriv N f r‖ ^ 2) (Ioi R) := by
    apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hR.trans hr
    have hpow : r ^ (11 + 2 * s) = r ^ 11 * (r ^ s) ^ 2 := by
      rw [Real.rpow_add hr0, show (2 : ℝ) * s = s * 2 by ring, Real.rpow_mul hr0.le]
      norm_num
    have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedDeriv N f r))
      (hT r ((le_max_left T 1).trans hr.le)) 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hpow]
    calc
      _ ≤ r ^ 11 * (C * r ^ s) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring
  have hn := homogeneousGlued_local_top_integrable f N R hR (hf R hR) hs
  apply (hn.union ht).mono_set
  intro r hr
  by_cases h : r ≤ R
  · exact Or.inl ⟨hr, h⟩
  · exact Or.inr (lt_of_not_ge h)

end DefocusingNLS

end OAI
