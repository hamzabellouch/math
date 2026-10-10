import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryCostLimit

namespace OAI

/-! # Summing the auxiliary costs without an extra logarithmic loss -/
namespace JointDickman
open Finset Filter
open scoped Classical Topology

lemma card_mul_sum_le_of_square {ι : Type*} (K : Finset ι) (F : ι → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hF : ∀ k ∈ K, (K.card:ℝ)^2*F k ≤ R) :
    (K.card:ℝ)*(∑ k ∈ K,F k) ≤ R := by
  by_cases hK : K.Nonempty
  · have hc : (0:ℝ)<K.card := by exact_mod_cast hK.card_pos
    apply (mul_le_mul_iff_right₀ hc).mp
    calc
      _ = ∑ k ∈ K,(K.card:ℝ)^2*F k := by rw [← mul_sum]; ring
      _ ≤ ∑ _k ∈ K,R := sum_le_sum hF
      _ = _ := by simp
  · have he : K=∅ := not_nonempty_iff_eq_empty.mp hK
    simpa only [he,card_empty,Nat.cast_zero,zero_mul] using hR

theorem auxiliary_cost_sum_bound (C H L : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    {α β : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : Finset ℕ) (a : ℕ → ℝ) (T b : ℝ),
      (K.card:ℝ) ≤ L*Real.log (N:ℝ) → 0 ≤ T → T ≤ N →
      (∀ k ∈ K, Real.exp (-1)*(N:ℝ)^α ≤ a k ∧ a k ≤ (N:ℝ)^β) →
      (K.card:ℝ)*(∑ k ∈ K,auxiliarySampleCost C H N N T (a k) b) ≤
        auxiliaryVanishingCost H L (α/2) β N+L^2*b^2*C/(α/2)^2 := by
  filter_upwards [auxiliary_cost_eventually_bound C H L hC hH hα,
    eventually_ge_atTop (1:ℕ)] with N hN hN1
  intro K a T b hK hT hTN ha
  apply card_mul_sum_le_of_square K _
  · exact add_nonneg (auxiliaryVanishingCost_nonneg hH (by exact_mod_cast hN1))
      (by positivity)
  · intro k hk
    exact hN T (a k) b K.card hT hTN (ha k hk).1 (ha k hk).2 (by positivity) hK

end JointDickman

end OAI
