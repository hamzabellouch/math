import OAI.NumberTheory.EgyptianFractions.MainLowerAppend
import OAI.NumberTheory.EgyptianFractions.DenominatorBound
import OAI.NumberTheory.EgyptianFractions.LengthBasic
import OAI.NumberTheory.EgyptianFractions.EgyptianExistence

namespace OAI
noncomputable section
namespace Problem337

/-- The elementary lower half of the main order theorem, with an explicit
absolute constant, independent of the short-expansion upper construction. -/
theorem main_double_log_lower_bound (b : ℕ) (hb : 2 ≤ b) :
    (1 / 2 : ℝ) * Real.log (Real.log (b : ℝ)) ≤ (maxEgyptianLength b : ℝ) := by
  have ha : 1 ≤ b - 1 := by omega
  have hab : b - 1 < b := by omega
  obtain ⟨n, hn⟩ := egyptianLength_attained_of_exists
    (exists_strict_unit_fraction_sum (b - 1) b ha hab)
  have hden := MainLower.denominator_le_of_sum
    (fun s d hd hm hs => ordered_unit_denominator_bound d hd hm hs)
    hb n (fun i => le_trans (by decide : 1 ≤ 2) (hn.1 i)) hn.2.2
  have hlog := MainLower.log_log_le_twice hb hden
  have hmax : (egyptianLength (b - 1) b : ℝ) ≤ (maxEgyptianLength b : ℝ) := by
    exact_mod_cast egyptianLength_le_max ha hab
  nlinarith

end Problem337

end

end OAI
