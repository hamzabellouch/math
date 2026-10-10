import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def stationarySineChart (θ : ℝ) : ℝ := 2 * Real.sin (θ / 2)
noncomputable def stationarySineInverse (u : ℝ) : ℝ := 2 * Real.arcsin (u / 2)
noncomputable def stationarySineJacobian (u : ℝ) : ℝ := (Real.sqrt (1 - u^2/4))⁻¹

 theorem stationarySineChart_inverse {u : ℝ} (hu : u ∈ Icc (-2:ℝ) 2) :
    stationarySineChart (stationarySineInverse u) = u := by
  unfold stationarySineChart stationarySineInverse
  rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),
    Real.sin_arcsin (by linarith [hu.1]) (by linarith [hu.2])]
  ring

 theorem stationarySineInverse_chart {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) Real.pi) :
    stationarySineInverse (stationarySineChart θ) = θ := by
  unfold stationarySineChart stationarySineInverse
  rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),
    Real.arcsin_sin (by linarith [hθ.1]) (by linarith [hθ.2])]
  ring

 theorem stationarySineChart_cos (θ : ℝ) :
    Real.cos θ = 1 - (stationarySineChart θ)^2/2 := by
  have h := Real.cos_two_mul (θ/2)
  have hs := Real.sin_sq_add_cos_sq (θ/2)
  have he : 2*(θ/2) = θ := by ring
  rw [he] at h
  unfold stationarySineChart
  nlinarith

 theorem stationarySineInverse_cos {u : ℝ} (hu : u ∈ Icc (-2:ℝ) 2) :
    Real.cos (stationarySineInverse u) = 1 - u^2/2 := by
  rw [stationarySineChart_cos,stationarySineChart_inverse hu]

 theorem stationarySineInverse_hasDerivAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    HasDerivAt stationarySineInverse (stationarySineJacobian u) u := by
  have h := ((Real.hasDerivAt_arcsin (by linarith [hu.1] : u/2 ≠ -1)
    (by linarith [hu.2] : u/2 ≠ 1)).comp u ((hasDerivAt_id u).div_const 2)).const_mul 2
  have he : 1 - (u/2)^2 = 1 - u^2/4 := by ring
  have hc : 2 * (1 / Real.sqrt (1-(u/2)^2) * (1/2)) = stationarySineJacobian u := by
    rw [he]
    unfold stationarySineJacobian
    ring
  rw [hc] at h
  exact h

 theorem stationarySineInverse_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineInverse u := by
  have hi : ContDiffAt ℝ ∞ (fun x : ℝ => x/2) u := contDiffAt_id.div_const 2
  have hh : ContDiffAt ℝ ∞ Real.arcsin (u/2) :=
    Real.contDiffAt_arcsin (by linarith [hu.1]) (by linarith [hu.2])
  have ht : ContDiffAt ℝ ∞ (fun x : ℝ => Real.arcsin (x/2)) u :=
    ContDiffAt.comp (f := fun x : ℝ => x/2) (g := Real.arcsin) u hh hi
  exact contDiffAt_const.mul ht

 theorem stationarySineJacobian_continuousOn :
    ContinuousOn stationarySineJacobian (Ioo (-2:ℝ) 2) := by
  apply ContinuousOn.inv₀
  · exact (Real.continuous_sqrt.comp (continuous_const.sub ((continuous_id.pow 2).div_const 4))).continuousOn
  · intro u hu
    apply ne_of_gt
    apply Real.sqrt_pos.2
    nlinarith [hu.1,hu.2,sq_nonneg (u-2),sq_nonneg (u+2)]

 theorem stationarySine_substitution {a b : ℝ} (ha : -2 < a) (hab : a ≤ b) (hb : b < 2)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ u in a..b, (stationarySineJacobian u : ℂ) * f (stationarySineInverse u)) =
      ∫ θ in stationarySineInverse a..stationarySineInverse b, f θ := by
  have hs : uIcc a b ⊆ Ioo (-2:ℝ) 2 := by
    rw [uIcc_of_le hab]
    intro u hu
    exact ⟨ha.trans_le hu.1,hu.2.trans_lt hb⟩
  simpa only [Complex.real_smul,Function.comp_apply] using
    intervalIntegral.integral_deriv_smul_comp
      (fun u hu => stationarySineInverse_hasDerivAt (hs hu))
      (stationarySineJacobian_continuousOn.mono hs) hf

end PlanarFalconer

end OAI
