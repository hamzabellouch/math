import OAI.NumberTheory.TotientAsymptotic.TotientCountingEnvelope

namespace OAI

/-! Finite maxima for the dyadic counting envelope. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma dyadicTotientEnvelope_le_iff (J : ℕ) (T : ℝ) :
    dyadicTotientEnvelope J ≤ T ↔ 1 ≤ T ∧
      ∀ k ≤ J,V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k ≤ T := by
  unfold dyadicTotientEnvelope
  rw [max_le_iff,Finset.sup'_le_iff]
  simp only [Finset.mem_range,Nat.lt_add_one_iff]

lemma dyadicTotientEnvelope_maximum (J : ℕ) :
    dyadicTotientEnvelope J=1 ∨ ∃ k ≤ J,
      dyadicTotientEnvelope J=V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k := by
  classical
  let f := fun k : ℕ => V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k
  have hne : (Finset.range (J+1)).Nonempty := by simp
  obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup' hne f
  by_cases h : (Finset.range (J+1)).sup' hne f ≤ 1
  · left
    exact max_eq_left h
  · right
    refine ⟨k,by simpa only [Finset.mem_range,Nat.lt_add_one_iff] using hk,?_⟩
    change max 1 ((Finset.range (J+1)).sup' hne f)=f k
    rw [max_eq_right (le_of_not_ge h)]
    exact he

end TotientAsymptotic

end

end OAI
