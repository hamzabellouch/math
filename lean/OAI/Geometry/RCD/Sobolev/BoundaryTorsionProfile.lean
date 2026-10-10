import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-! # A fixed scalar profile for compact interior torsion tests

Only its first two derivatives are used: the profile is zero below one
and agrees with the identity above two. No higher-order rate is needed.
-/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace RegularPointCoordinates

def boundaryTorsionProfile (t : ℝ) : ℝ := t*Real.smoothTransition (t-1)

theorem boundaryTorsionProfile_smooth : ContDiff ℝ ∞ boundaryTorsionProfile :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem boundaryTorsionProfile_zero {t : ℝ} (ht : t≤1) : boundaryTorsionProfile t=0 := by
  rw [boundaryTorsionProfile,Real.smoothTransition.zero_of_nonpos (by linarith),mul_zero]

theorem boundaryTorsionProfile_identity {t : ℝ} (ht : 2≤t) : boundaryTorsionProfile t=t := by
  rw [boundaryTorsionProfile,Real.smoothTransition.one_of_one_le (by linarith),mul_one]

theorem boundaryTorsionProfile_nonneg (t : ℝ) : 0≤boundaryTorsionProfile t := by
  by_cases ht : t≤1
  · rw [boundaryTorsionProfile_zero ht]
  · exact mul_nonneg (by linarith) (Real.smoothTransition.nonneg _)

theorem boundaryTorsionProfile_deriv_zero {t : ℝ} (ht : t<1) :
    deriv boundaryTorsionProfile t=0 := by
  have he : boundaryTorsionProfile=ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact boundaryTorsionProfile_zero hx.le
  rw [he.deriv_eq]
  simp

theorem boundaryTorsionProfile_deriv_one {t : ℝ} (ht : 2<t) :
    deriv boundaryTorsionProfile t=1 := by
  have he : boundaryTorsionProfile=ᶠ[𝓝 t] id := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact boundaryTorsionProfile_identity hx.le
  rw [he.deriv_eq]
  exact deriv_id t

theorem boundaryTorsionProfile_second_zero {t : ℝ} (ht : t<1 ∨ 2<t) :
    deriv (deriv boundaryTorsionProfile) t=0 := by
  rcases ht with ht|ht
  · have he : deriv boundaryTorsionProfile=ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with x hx
      exact boundaryTorsionProfile_deriv_zero hx
    rw [he.deriv_eq]
    simp
  · have he : deriv boundaryTorsionProfile=ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact boundaryTorsionProfile_deriv_one hx
    rw [he.deriv_eq]
    simp

theorem boundaryTorsionProfile_two_derivative_bounds :
    ∃ C : ℝ, 1≤C ∧ ∀ t, |deriv boundaryTorsionProfile t|≤C ∧
      |deriv (deriv boundaryTorsionProfile) t|≤C := by
  have hd : ContDiff ℝ ∞ (deriv boundaryTorsionProfile) := by
    apply ContDiff.deriv'
    simpa using (boundaryTorsionProfile_smooth.of_le (show (⊤:ℕ∞)≤∞ from le_rfl))
  have hdd' : ContDiff ℝ ∞ (deriv (deriv boundaryTorsionProfile)) := by
    apply ContDiff.deriv'
    simpa using hd
  obtain ⟨C₁,hC₁⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 3)).exists_bound_of_continuousOn hd.continuous.continuousOn
  obtain ⟨C₂,hC₂⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 3)).exists_bound_of_continuousOn hdd'.continuous.continuousOn
  refine ⟨max 1 (max C₁ C₂),le_max_left _ _,fun t => ?_⟩
  by_cases ht : t∈Icc (0:ℝ) 3
  · have h₁ : |deriv boundaryTorsionProfile t|≤C₁ := by simpa only [Real.norm_eq_abs] using hC₁ t ht
    have h₂ : |deriv (deriv boundaryTorsionProfile) t|≤C₂ := by simpa only [Real.norm_eq_abs] using hC₂ t ht
    exact ⟨h₁.trans ((le_max_left C₁ C₂).trans (le_max_right 1 _)),
      h₂.trans ((le_max_right C₁ C₂).trans (le_max_right 1 _))⟩
  · have hout : t<1 ∨ 2<t := by
      simp only [mem_Icc,not_and_or,not_le] at ht
      rcases ht with h|h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hdsmall : |deriv boundaryTorsionProfile t|≤1 := by
      rcases hout with h|h
      · rw [boundaryTorsionProfile_deriv_zero h,abs_zero]; norm_num
      · rw [boundaryTorsionProfile_deriv_one h,abs_one]
    exact ⟨hdsmall.trans (le_max_left _ _),by rw [boundaryTorsionProfile_second_zero hout,abs_zero]; positivity⟩

end RegularPointCoordinates

end

end OAI
