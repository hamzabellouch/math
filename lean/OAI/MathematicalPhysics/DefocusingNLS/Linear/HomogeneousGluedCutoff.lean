import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedRegularity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-! A harmless extension on negative radii makes the glued radial pair bounded globally. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

noncomputable def homogeneousGluedCutoff (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  (Real.smoothTransition (r + 1) : ℂ) * f r

theorem homogeneousGluedCutoff_eq (f : ℝ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    homogeneousGluedCutoff f r = f r := by
  simp only [homogeneousGluedCutoff,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ r + 1),
    Complex.ofReal_one, one_mul]

theorem homogeneousGluedCutoff_contDiff {n : ℕ∞} (f : ℝ → ℂ)
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (homogeneousGluedCutoff f) := by
  exact (Complex.ofRealCLM.contDiff.comp
    (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))).mul hf

theorem homogeneousGluedCutoff_eventuallyEq (f : ℝ → ℂ) (r : ℝ) (hr : 0 < r) :
    homogeneousGluedCutoff f =ᶠ[𝓝 r] f := by
  filter_upwards [Ioi_mem_nhds hr] with t ht
  exact homogeneousGluedCutoff_eq f t ht.le

theorem homogeneousGluedCutoff_iteratedDeriv (f : ℝ → ℂ) (N : ℕ)
    (r : ℝ) (hr : 0 < r) :
    iteratedDeriv N (homogeneousGluedCutoff f) r = iteratedDeriv N f r :=
  (homogeneousGluedCutoff_eventuallyEq f r hr).iteratedDeriv_eq N

theorem homogeneousGluedCutoff_bounded (f : ℝ → ℂ) (hf : Continuous f)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ r in atTop, ‖f r‖ ≤ M) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖homogeneousGluedCutoff f r‖ ≤ M := by
  obtain ⟨M, hM, hbound⟩ := hbound
  obtain ⟨T, hT⟩ := eventually_atTop.mp hbound
  let S := max T 0
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) S) hf.continuousOn
  have hnorm (r : ℝ) : ‖homogeneousGluedCutoff f r‖ ≤ ‖f r‖ := by
    rw [homogeneousGluedCutoff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)
  refine ⟨max (max C 0) M, (le_max_right C 0).trans (le_max_left _ _), ?_⟩
  intro r
  by_cases hr : r ≤ -1
  · have hz : homogeneousGluedCutoff f r = 0 := by
      simp only [homogeneousGluedCutoff,
        Real.smoothTransition.zero_of_nonpos (by linarith : r + 1 ≤ 0),
        Complex.ofReal_zero, zero_mul]
    rw [hz, norm_zero]
    exact (le_max_right C 0).trans (le_max_left _ _)
  · by_cases hS : r ≤ S
    · exact (hnorm r).trans ((hC r ⟨(lt_of_not_ge hr).le, hS⟩).trans
        ((le_max_left C 0).trans (le_max_left _ _)))
    · exact (hnorm r).trans ((hT r ((le_max_left T 0).trans (lt_of_not_ge hS).le)).trans
        (le_max_right _ _))

end DefocusingNLS

end OAI
