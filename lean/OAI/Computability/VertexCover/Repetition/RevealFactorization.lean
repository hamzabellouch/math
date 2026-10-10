import Mathlib
import OAI.Computability.VertexCover.Repetition.PartialReveal

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                   
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealLeftFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (x : X) : ℝ :=
  match r with
  | Sum.inl u => if x = u then 1 else 0
  | Sum.inr v => μ.weight (x,v) / 2

def revealRightFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (y : Y) : ℝ :=
  match r with
  | Sum.inl u => μ.weight (u,y) / 2
  | Sum.inr v => if y = v then 1 else 0

omit [DecidableEq Y] in
theorem revealLeftFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (x : X) : 0 ≤ revealLeftFactor μ r x := by
  cases r with
  | inl u => simp only [revealLeftFactor]; split <;> norm_num
  | inr v => exact div_nonneg (μ.nonnegative _) (by norm_num)

omit [DecidableEq X] in
theorem revealRightFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (y : Y) : 0 ≤ revealRightFactor μ r y := by
  cases r with
  | inl u => exact div_nonneg (μ.nonnegative _) (by norm_num)
  | inr v => simp only [revealRightFactor]; split <;> norm_num

theorem revealLaw_factorization (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (x : X) (y : Y) :
    (revealLaw μ).weight ((x,y),r) =
      revealLeftFactor μ r x * revealRightFactor μ r y := by
  rw [revealLaw_weight]
  cases r with
  | inl u =>
    by_cases h : x = u
    · subst x; simp [revealLeftFactor, revealRightFactor]
    · simp [revealLeftFactor, revealRightFactor, h, Ne.symm h]
  | inr v =>
    by_cases h : y = v
    · subst y; simp [revealLeftFactor, revealRightFactor]
    · simp [revealLeftFactor, revealRightFactor, h, Ne.symm h]

def partialLeftFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (x : I → X) : ℝ :=
  ∏ i, revealLeftFactor μ (rest i) (x i.1)

def partialRightFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (y : I → Y) : ℝ :=
  ∏ i, revealRightFactor μ (rest i) (y i.1)

theorem partialRevealWeight_factorization (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    partialRevealWeight μ j rest u =
      μ.weight (u j) * partialLeftFactor μ j rest (fun i => (u i).1) *
        partialRightFactor μ j rest (fun i => (u i).2) := by
  have hpoint (i : {i : I // i ≠ j}) :
      (revealLaw μ).weight (u i.1,rest i) =
        revealLeftFactor μ (rest i) (u i.1).1 * revealRightFactor μ (rest i) (u i.1).2 :=
    revealLaw_factorization μ (rest i) (u i.1).1 (u i.1).2
  simp only [partialRevealWeight, partialLeftFactor, partialRightFactor,
    hpoint, Finset.prod_mul_distrib]
  ring

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
