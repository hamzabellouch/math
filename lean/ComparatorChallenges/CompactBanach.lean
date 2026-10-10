import Mathlib

namespace OAI

                                                                                
                                                                              
                                                                                
                                                     

universe u v
namespace CompactBanach

def DoublingAtMost {B : Type*} [MetricSpace B] (K : Set B) (bound : ℕ) : Prop :=
  ∀ x : K, ∀ r : ℝ, 0 < r →
    ∃ centers : Finset K, centers.card ≤ bound ∧
      ∀ y : K, dist y x < r → ∃ c ∈ centers, dist y c < r / ((2 : ℕ) : ℝ)

def AdmitsBiLipschitzEmbedding {B : Type*} [MetricSpace B] (K : Set B)
    (E : Type*) [MetricSpace E] : Prop :=
  ∃ f : K → E, ∃ a : ℝ, 0 < a ∧ ∃ D : ℝ, 1 ≤ D ∧
    ∀ x y : K, a * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ D * a * dist x y

                                                                       
theorem main : ∃ Λ : ℕ, ∀ (B : Type u) [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B], ¬ FiniteDimensional ℝ B →
    ∃ K : Set B, IsCompact K ∧ DoublingAtMost K Λ ∧
      ∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E], ¬ AdmitsBiLipschitzEmbedding K E := by
  sorry

end CompactBanach

end OAI
