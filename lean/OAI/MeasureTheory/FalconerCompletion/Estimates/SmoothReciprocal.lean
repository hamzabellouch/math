import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasure

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
namespace Attempt4FullFar
open Set Filter
open scoped ContDiff Topology

noncomputable def smoothReciprocal (x : ℝ) : ℝ :=
  Real.smoothTransition (2*x-1) / x

lemma smoothReciprocal_zero {x : ℝ} (hx : x ≤ 1/2) : smoothReciprocal x = 0 := by
  rw [smoothReciprocal, Real.smoothTransition.zero_of_nonpos (by linarith), zero_div]

lemma smoothReciprocal_eq_inv {x : ℝ} (hx : 1 ≤ x) : smoothReciprocal x = x⁻¹ := by
  rw [smoothReciprocal, Real.smoothTransition.one_of_one_le (by linarith), one_div]

lemma smoothReciprocal_contDiff : ContDiff ℝ ∞ smoothReciprocal := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1/2 by norm_num)] with y hy
    exact smoothReciprocal_zero hy.le
  · exact (Real.smoothTransition.contDiffAt.comp x
      ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const)).div contDiffAt_id hx

lemma smoothReciprocal_deriv_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ j smoothReciprocal x‖ ≤ C := by
  have hc : Continuous (iteratedDeriv j smoothReciprocal) :=
    smoothReciprocal_contDiff.continuous_iteratedDeriv j
      (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 0 (max C (j.factorial:ℝ)), le_max_left _ _, ?_⟩
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hx0 : x < 0
  · have he : smoothReciprocal =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds (show x < 1/2 by linarith)] with y hy
      exact smoothReciprocal_zero hy.le
    rw [(he.iteratedDeriv j).eq_of_nhds]
    simp
  · by_cases hx2 : x ≤ 2
    · exact (hC x ⟨le_of_not_gt hx0,hx2⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
    · have he : smoothReciprocal =ᶠ[𝓝 x] Inv.inv := by
        filter_upwards [Ioi_mem_nhds (show (1:ℝ) < x by linarith)] with y hy
        exact smoothReciprocal_eq_inv hy.le
      rw [(he.iteratedDeriv j).eq_of_nhds, iteratedDeriv_eq_iterate, iter_deriv_inv]
      have hp : ‖x ^ (-1-(j:ℤ))‖ ≤ (1:ℝ) := by
        rw [Real.norm_eq_abs, abs_of_pos (zpow_pos (by linarith : 0 < x) _)]
        exact zpow_le_one_of_nonpos₀ (by linarith) (by omega)
      calc
        ‖(-1:ℝ)^j * (j.factorial:ℝ) * x^(-1-(j:ℤ))‖ ≤ (j.factorial:ℝ) := by
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Real.norm_natCast]
          exact mul_le_of_le_one_right (by positivity) hp
        _ ≤ max 0 (max C (j.factorial:ℝ)) := (le_max_right _ _).trans (le_max_right _ _)

end Attempt4FullFar
end
end

end OAI
