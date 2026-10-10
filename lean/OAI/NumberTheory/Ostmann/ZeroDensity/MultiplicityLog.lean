import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.ZeroDensity.OccurrenceCount

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.ZeroDensity

theorem exists_localMultiplicity_log_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ Q H : ℕ, 0 < Q → 0 < H →
      localMultiplicityBound Q (H : ℝ) ≤ C*(1+Real.log ((Q : ℝ)*H)) := by
  let A : ℝ := 32*Erdos970.Erdos970Dependency.SiegelWalfisz.absoluteZetaTwo
  let L : ℝ := Real.log (55/52)
  have hB := Erdos970.Erdos970Dependency.SiegelWalfisz.one_le_absoluteZetaTwo
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hL : 0 < L := Real.log_pos (by norm_num : (1 : ℝ)<55/52)
  refine ⟨(Real.log A+1)/L, by positivity, ?_⟩
  intro Q H hQ hH
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hQH : (1 : ℝ) ≤ (Q : ℝ)*H := by nlinarith
  have hlog : 0 ≤ Real.log ((Q : ℝ)*H) := Real.log_nonneg hQH
  calc
    localMultiplicityBound Q (H : ℝ) ≤ Real.log (A*((Q : ℝ)*H))/L := by
      apply div_le_div_of_nonneg_right _ hL.le
      apply Real.log_le_log (by positivity)
      dsimp [A]
      nlinarith [mul_nonneg (show 0 ≤ Erdos970.Erdos970Dependency.SiegelWalfisz.absoluteZetaTwo*(Q : ℝ) by positivity)
        (show 0 ≤ (H : ℝ)-1 by linarith)]
    _ = (Real.log A+Real.log ((Q : ℝ)*H))/L := by
      rw [Real.log_mul (ne_of_gt hApos) (by positivity)]
    _ ≤ ((Real.log A+1)/L)*(1+Real.log ((Q : ℝ)*H)) := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hL.le
      nlinarith [mul_nonneg hlogA hlog]

end Ostmann.ZeroDensity

end

end OAI
