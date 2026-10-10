import OAI.NumberTheory.TwoPoint.Fourier.MajorArcBandAvoidance
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingParameters
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcWorkingBound

namespace OAI

/-! The literal first band satisfies all minor-arc support conditions
once the common parameter exceeds a fixed threshold. -/
namespace TwoPointCorrelations

open Filter Finset

theorem minor_arc_actual_working_parameters (R₀ : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) →
      W ≤ Real.log (H:ℝ)^5 →
      let h := majorArcWorkingLength H W
      let P := W^(500000:ℕ)
      let Q := (h:ℝ)/W^3
      2 ≤ h ∧ 1 ≤ W ∧ W ≤ h ∧ 1 ≤ Real.log (h:ℝ) ∧
        1 ≤ Real.log (Real.log (h:ℝ)) ∧ Real.log (h:ℝ) ≤ W^(1/5:ℝ) ∧
        (∀ p ∈ mrtPrimeBand (mrtBandLower P Q 1) (mrtBandUpper Q 1),
          p ≠ 2 ∧ 2*R₀ ≤ p ∧ 2*W ≤ (p:ℝ) ∧ (p:ℝ) ≤ (h:ℝ)/W) := by
  have hlog : Tendsto (fun W:ℝ => Real.log W) atTop atTop := Real.tendsto_log_atTop
  filter_upwards [mrt_working_prime_parameters,major_arc_working_length_power 2,
    (hlog.comp hlog).eventually (eventually_ge_atTop (1:ℝ)),
    hlog.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop ((2*R₀:ℕ):ℝ)] with W hp hpower hLL hL hR
  intro H hH hLH hWH
  dsimp only
  obtain ⟨hW,hpar⟩ := hp
  obtain ⟨hP,hPQ,_,_,_,_,_⟩ := hpar H hH hLH hWH
  let h := majorArcWorkingLength H W
  let P := W^(500000:ℕ)
  let Q := (h:ℝ)/W^3
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hhpow : W^2 ≤ (h:ℝ) := hpower H hH hLH hWH
  have hWh : W ≤ (h:ℝ) := (le_self_pow₀ hW1 (by decide : (2:ℕ)≠0)).trans hhpow
  have hh : 2 ≤ h := by exact_mod_cast hW.trans hWh
  have hLh : 1 ≤ Real.log (h:ℝ) := hL.trans (Real.log_le_log hW0 hWh)
  have hLLh : 1 ≤ Real.log (Real.log (h:ℝ)) :=
    hLL.trans (Real.log_le_log (by linarith : 0 < Real.log W)
      (Real.log_le_log hW0 hWh))
  have hcap : Real.log (h:ℝ) ≤ W^(1/5:ℝ) := by
    have hl := Real.log_le_log (by exact_mod_cast (show 0<h by omega))
      (major_arc_working_length_exp_upper H hW0.le)
    simpa only [Real.log_exp] using hl
  refine ⟨hh,hW1,hWh,hLh,hLLh,hcap,?_⟩
  intro p hp
  have hPW : 2*W ≤ P :=
    (show 2*W ≤ W^2 by nlinarith only [hW]).trans
      (pow_le_pow_right₀ hW1 (by norm_num : (2:ℕ)≤500000))
  have hPR : ((2*R₀:ℕ):ℝ) ≤ P :=
    hR.trans (le_self_pow₀ hW1 (by decide : (500000:ℕ)≠0))
  have hQH : Q ≤ (h:ℝ)/W := div_le_div_of_nonneg_left (Nat.cast_nonneg h) hW0
    (le_self_pow₀ hW1 (by decide : (3:ℕ)≠0))
  exact major_arc_first_prime_range hP hPQ hPW hPR hQH hp

end TwoPointCorrelations

end OAI
