import OAI.Analysis.Mahler.ConformalSeries
import OAI.Analysis.Mahler.UniformError
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

namespace SymmetricMahler
open Real Complex MeasureTheory Set

/-- The actual M(r)=F(r) on the real diameter, taking its real part for a
real-valued function on all of ℝ. The estimates use only 0≤r<1. -/
noncomputable def radialMap (r : ℝ) : ℝ := (MahlerConformal.F (r : ℂ)).re

lemma measurable_conformal_F : Measurable MahlerConformal.F := by
  change Measurable (fun w : ℂ => (8/(Real.pi : ℂ)^2) *
    ∑' k : ℕ, MahlerConformal.term 2 k w)
  apply measurable_const.mul
  apply Measurable.tsum
  intro k
  change Measurable (fun w : ℂ => w^(2*k+1) / ((2*k+1 : ℕ) : ℂ)^2)
  fun_prop

lemma measurable_radialMap : Measurable radialMap := by
  change Measurable (fun r : ℝ => (MahlerConformal.F (r : ℂ)).re)
  exact Complex.measurable_re.comp (measurable_conformal_F.comp Complex.measurable_ofReal)

lemma continuousOn_radialMap : ContinuousOn radialMap (Ico 0 1) := by
  intro r hr
  have hw : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_nonneg hr.1] using hr.2
  have h := (MahlerConformal.hasDerivAt_F_series hw).real_of_complex
  exact h.continuousAt.continuousWithinAt

theorem hasDerivAt_radialMap {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt radialMap (radialDerivative r) r := by
  have hw : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_pos hr] using hr1
  have hw0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := (MahlerConformal.hasDerivAt_F_log hw hw0).real_of_complex
  have hq : 0 ≤ (1+r)/(1-r) := by positivity
  have hcast : (1+(r : ℂ))/(1-(r : ℂ)) = (((1+r)/(1-r) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hd : 4/((Real.pi : ℂ)^2*(r : ℂ))*Complex.log ((1+(r : ℂ))/(1-(r : ℂ))) =
      (radialDerivative r : ℂ) := by
    rw [hcast, ← Complex.ofReal_log hq]
    dsimp [radialDerivative]
    push_cast
    rfl
  rw [hd, Complex.ofReal_re] at h
  exact h

theorem radialMap_zero : radialMap 0 = 0 := by
  simp [radialMap, MahlerConformal.F_zero]

/-- Conjugation symmetry makes the real diameter's image real. -/
theorem ofReal_radialMap (r : ℝ) : (radialMap r : ℂ) = MahlerConformal.F (r : ℂ) := by
  apply Complex.conj_eq_iff_re.mp
  simpa using (MahlerConformal.F_conj (r : ℂ)).symm

/-- The derivative formula has the claimed positive removable value at zero. -/
theorem hasDerivAt_radialMap_zero : HasDerivAt radialMap (8/Real.pi^2) 0 := by
  have h := MahlerConformal.hasDerivAt_F_zero.real_of_complex
  have hd : (8/(Real.pi : ℂ)^2) = ((8/Real.pi^2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hd, Complex.ofReal_re] at h
  exact h

/-- The actual series obeys the quantitative radial increment estimate. -/
theorem conformal_radial_increment {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    (4/Real.pi^2)*(b-a) ≤ radialMap b-radialMap a := by
  apply radial_increment_lower ha hab hb
  · exact continuousOn_radialMap.mono (fun x hx => ⟨ha.trans hx.1, hx.2.trans_lt hb⟩)
  · intro x hx
    exact hasDerivAt_radialMap (by linarith [hx.1]) (hx.2.trans hb)

/-- Strict radial monotonicity is proved on the entire positive real radius. -/
theorem strictMonoOn_radialMap : StrictMonoOn radialMap (Ico 0 1) := by
  intro a ha b hb hab
  have h := conformal_radial_increment ha.1 hab.le hb.2
  have hpos : 0 < (4/Real.pi^2)*(b-a) := by positivity
  linarith

theorem radialMap_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < radialMap r := by
  have h := strictMonoOn_radialMap (show 0 ∈ Ico (0 : ℝ) 1 by simp) ⟨hr.le, hr1⟩ hr
  simpa [radialMap_zero] using h

/-- The actual series M has the required uniform small-error property.
This instantiates the full real error analysis; its derivative is not an assumption. -/
theorem conformal_radial_error_small {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → ∀ r₀ ∈ Ico (0 : ℝ) 1,
      IntervalIntegrable (errorIntegrand radialMap r₀ m) volume r₀ 1 ∧
      (∫ r in r₀..(1 : ℝ), errorIntegrand radialMap r₀ m r) < ε := by
  exact uniform_error_small measurable_radialMap continuousOn_radialMap
    (fun _ hr => hasDerivAt_radialMap hr.1 hr.2) hε

end SymmetricMahler

end OAI
