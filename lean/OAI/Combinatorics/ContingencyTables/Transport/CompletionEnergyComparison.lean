import OAI.Combinatorics.ContingencyTables.Transport.CompletionChainFlow

namespace OAI

/-! # From literal acceptance counts to weighted graph energy -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical
open CommonBasesFPRAS

variable {X I J : Type*} [Fintype X] [Nonempty X] [Fintype I] [Fintype J]

/-- This is the actual chain energy comparison. The half-acceptance
premise is supplied by the proved reference-star small-entry estimate. -/
theorem completionChain_energy_lower
    (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j)
    (Adj : X → X → Prop) (hsym : ∀ x y,Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ)
    (hdegree : ∀ x,(Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D:ℝ)*β ≤ 1/2)
    (haccept : ∀ x y,Adj x y → (blockCount R P x:ℝ)/2 ≤ acceptedCount R P x y)
    (H : X → ℝ) :
    β/(2*MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ)))*
      ((∑ x,∑ y,if Adj x y then min (blockCount R P x:ℝ) (blockCount R P y:ℝ)*
        (H x-H y)^2 else 0)/2) ≤
      (completionChain R P htotal Adj hsym β hβ D hdegree hproposal).energy H := by
  let Z := MetropolisChain.normalizer (fun z => (blockCount R P z:ℝ))
  have hZ : 0 < Z := MetropolisChain.normalizer_pos _
    (fun z => by exact_mod_cast blockCount_pos R P htotal z)
  have hterm (x y : X) :
      β/2*(if Adj x y then min (blockCount R P x:ℝ) (blockCount R P y:ℝ)*(H x-H y)^2 else 0) ≤
      if Adj x y then β*(acceptedCount R P x y:ℝ)*(H x-H y)^2 else 0 := by
    by_cases hxy : Adj x y
    · rw [ite_eq_left hxy,ite_eq_left hxy]
      have hm : min (blockCount R P x:ℝ) (blockCount R P y:ℝ)/2 ≤ acceptedCount R P x y :=
        (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (haccept x y hxy)
      have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hβ) (sq_nonneg (H x-H y))
      convert hs using 1
      all_goals ring
    · rw [ite_eq_right hxy,ite_eq_right hxy,mul_zero]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) =>
    Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset X)) => hterm x y))
  simp_rw [← Finset.mul_sum] at hsum
  rw [completionChain_energy]
  have hb := div_le_div_of_nonneg_right hsum (show 0 ≤ 2*Z by positivity)
  convert hb using 1
  all_goals
    dsimp only [Z]
    ring

end ContingencyTables.CompletionTranslation

end OAI
