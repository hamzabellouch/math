import OAI.NumberTheory.Ostmann.Construction.InitialMovingEarlyCost
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompactLeaf

namespace OAI

/-! # Ordinary energy with the genuine initial half-list cutoff -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingAmplitudeRegularEnergy_initial_le {J : Type}
    (P Pg I : Finset ℕ) (b d rinit : ℕ) (cb cd : ℝ)
    (sl sr : Fin d → P) (fallback : P)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (hμ0 : ∀ j a, 0 ≤ μ j a)
    (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ)
    (n r : ℕ) (hlen : 4 + r + 4 * n = rinit + rinit)
    (Q : MovingRegularSlot n r (b + b) → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) :
    movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback) g Dq S ψ X lo hi)
      φ G n r (b + b) Q greg ≤
    movingAmplitudeRegularEnergy P Pg I outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q (fun _ => movingCompactLeaf (V 0)) g Dq S ψ X lo hi)
      φ G n r (b + b) Q greg := by
  unfold movingAmplitudeRegularEnergy
  dsimp only
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : (∏ i, μ n (u i)) = 0
  · simp only [hu, zero_mul, le_refl]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Finset.prod_nonneg (fun i _ => hμ0 n (u i))) (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (hφ _)
  apply Finset.sum_le_sum
  intro a _
  let α := movingAmplitudePrior Pg n r (b + b) V (smoothGiantPrior Pg φ (G (n + 1)))
    (fun i => primeSubsetPrior P (Q i)) a
  have hα : 0 ≤ α := mul_nonneg (smoothGiantPrior_nonneg Pg φ (G (n + 1)) hφ a.1)
    (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (Q i) (a.2.1 i)))
  apply mul_le_mul_of_nonneg_left _ hα
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have he := movingTemplateCoefficient_original_initial_norm_le Subtype.val b d rinit cb cd
    sl sr fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n (4 + r)
    a.2.2.val (movingRestoreSample n r (b + b) u a.2.1) hlen p a.1
  rw [movingTemplateCoefficient_original_leaf_congr Subtype.val q outside μ
    childBound pivotBound V (fun s => if s = 0 then 0 else 1) (movingCompactLeaf (V 0))
    (fun s hs => by simp only [movingCompactLeaf, hs, ite_true]) g Dq S ψ X lo hi φ G
    n (4 + r) (b + b) a.2.2.val ((mem_transferFrequencyRange _ _).mp a.2.2.property)] at he
  exact he

end Ostmann

end OAI
