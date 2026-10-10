import OAI.Combinatorics.HadwigerMatching.MinorBound
import OAI.Combinatorics.HadwigerMatching.ChromaticBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

namespace HadwigerMatching

/-- The matching–minor proposition: the Hadwiger bound and its chromatic
consequence when the independence and touching-matching numbers are small. -/
theorem full_matching_minor_proposition
    (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    let m : ℕ := Fintype.card V
    let h : ℕ := LinearListHadwiger.hadwigerNumber G
    let c : ℕ := HadwigerMatching.connectedMatchingNumber G
    (h : ℚ) ≤ ((m : ℚ) + 4 * (c : ℚ) + 2) / 3 ∧
      (G.indepNum ≤ 2 →
        (c : ℚ) < (m : ℚ) / 100 →
        5 ≤ m →
        (h : ℚ) < 26 * (m : ℚ) / 75 + 2 / 3 ∧
        26 * (m : ℚ) / 75 + 2 / 3 < (m : ℚ) / 2 ∧
        (m : ℚ) / 2 ≤ (G.chromaticNumber.toNat : ℚ)) := by
  dsimp only
  have hn := hadwiger_matching_bound G
  have hq : 3 * (LinearListHadwiger.hadwigerNumber G : ℚ) ≤
      (Fintype.card V : ℚ) + 4 * (connectedMatchingNumber G : ℚ) + 2 := by
    exact_mod_cast hn
  refine ⟨by linarith, ?_⟩
  intro hα hc hm
  have hm' : (5 : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast hm
  have hnχ := card_le_twice_chromaticNumber_of_indepNum G hα
  have hχ : (Fintype.card V : ℚ) ≤ 2 * (G.chromaticNumber.toNat : ℚ) := by
    exact_mod_cast hnχ
  refine ⟨?_, ?_, ?_⟩ <;> linarith

end HadwigerMatching

end OAI
