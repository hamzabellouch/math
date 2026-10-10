import OAI.NumberTheory.TotientAsymptotic.FordComparisonBudget
import OAI.NumberTheory.TotientAsymptotic.ComparisonThreshold

namespace OAI

/-! Unconditional proof of the needed published Ford Lemma 5.1 specialization. -/
noncomputable section
namespace TotientAsymptotic

theorem fordLemma51Input : FordLemma51Input := by
  obtain ⟨A,C,M,R,hA,hC,hM,hR,hcount⟩ := ford_raw_count
  obtain ⟨A₁,M₁,hA₁,hM₁,hcount₁⟩ := ford_raw_count_one
  obtain ⟨y₀,hy₀,hthreshold⟩ := ford_comparison_threshold R hR
  let K := 1+216*A+216*A₁+M+M₁+C
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hAK : 216*A ≤ K := by dsimp [K]; linarith
  have hA₁K : 216*A₁ ≤ K := by dsimp [K]; linarith
  have hMK : M ≤ K := by dsimp [K]; linarith
  have hM₁K : M₁ ≤ K := by dsimp [K]; linarith
  have hCK : C ≤ K := by dsimp [K]; linarith
  refine ⟨K,y₀,by linarith,hy₀,?_⟩
  intro b y S D r Y U hy hp T hT
  have hy1 : 1 < y := hy₀.trans_le hy
  obtain ⟨hy2,hBy,hroot⟩ := hthreshold y hy
  by_cases hb : b=1
  · subst b
    exact (hcount₁ D r y S Y U hy2 hBy hp T hT).trans
      (ford_comparison_budget_one hp hy1 hA₁.le hM₁.le hK hA₁K hM₁K)
  · have hb2 : 2 ≤ b := by have := hp.1; omega
    exact (hcount b D r y S Y U hy2 hBy hb2 hp
      (hroot S (ford_scale_bounds hp).2) T hT).trans
      (ford_comparison_budget hp hy1 hA.le hM.le hC.le hK hAK hMK hCK)

end TotientAsymptotic

end

end OAI
