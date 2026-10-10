import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import OAI.Geometry.NodalSets.Elliptic.RealFinitePositiveBounds

namespace OAI

namespace Yau
noncomputable section

def realWeakJetRadius (m : ℕ) : ℝ := 1/16+1/(16*((m:ℝ)+1))

lemma realWeakJetRadius_zero : realWeakJetRadius 0=1/8 := by norm_num [realWeakJetRadius]

lemma realWeakJetRadius_lower (m : ℕ) : (1:ℝ)/16 < realWeakJetRadius m := by
  dsimp [realWeakJetRadius]
  have h : 0 < 1/(16*((m:ℝ)+1)) := by positivity
  linarith only [h]

lemma realWeakJetRadius_upper (m : ℕ) : realWeakJetRadius m ≤ (1:ℝ)/8 := by
  have h : (1:ℝ)/(16*((m:ℝ)+1)) ≤ 1/16 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith only [Nat.cast_nonneg (α := ℝ) m]
  dsimp [realWeakJetRadius]
  linarith only [h]

lemma realWeakJetRadius_succ_lt (m : ℕ) : realWeakJetRadius (m+1) < realWeakJetRadius m := by
  have h : (1:ℝ)/(16*(((m+1:ℕ):ℝ)+1)) < 1/(16*((m:ℝ)+1)) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    push_cast
    linarith
  dsimp only [realWeakJetRadius]
  linarith only [h]

end
end Yau

end OAI
