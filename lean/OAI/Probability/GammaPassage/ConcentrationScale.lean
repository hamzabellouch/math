import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace OAI

namespace GammaFPP.FiniteLocal

noncomputable def concentrationKappa (shape rate : ℝ) : ℝ :=
  min (rate/4) (1/(4*((16*(2 : ℝ)^shape/rate^2)+1)))

lemma concentrationKappa_bounds {shape rate : ℝ} (hr : 0 < rate) :
    0 < concentrationKappa shape rate ∧
      concentrationKappa shape rate ≤ rate/4 ∧
      concentrationKappa shape rate ≤ 1/4 ∧
      (16*(2 : ℝ)^shape/rate^2)*(concentrationKappa shape rate)^2 ≤ 1/16 := by
  let B : ℝ := 16*(2 : ℝ)^shape/rate^2
  let k := concentrationKappa shape rate
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hk : 0 < k := by dsimp [k, concentrationKappa]; positivity
  have hkr : k ≤ rate/4 := min_le_left _ _
  have hkd : k ≤ 1/(4*(B+1)) := min_le_right _ _
  have hd : 0 < 4*(B+1) := by linarith
  have hm : k*(4*(B+1)) ≤ 1 := (le_div_iff₀ hd).mp hkd
  have hBk : 0 ≤ B*k := mul_nonneg hB hk.le
  have hkquarter : k ≤ 1/4 := by nlinarith
  have hBkquarter : B*k ≤ 1/4 := by nlinarith
  have hprod := mul_le_mul hBkquarter hkquarter hk.le (by norm_num : (0 : ℝ) ≤ 1/4)
  refine ⟨hk, hkr, hkquarter, ?_⟩
  change B*k^2 ≤ 1/16
  nlinarith

end GammaFPP.FiniteLocal

end OAI
