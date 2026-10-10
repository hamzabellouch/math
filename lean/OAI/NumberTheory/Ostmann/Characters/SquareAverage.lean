import Mathlib.Algebra.Field.ZMod
import OAI.NumberTheory.Ostmann.Characters.SquarePullback

namespace OAI

/-!
# Domination of a uniform square-coset average

The square map on the unit group has fibers of size at most two. Its
pushforward therefore has density at most two against the uniform law.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_square_coset_le_twice {p : ℕ} [Fact p.Prime]
    (K : (ZMod p)ˣ) (f : (ZMod p)ˣ → ℝ) (hf : ∀ u, 0 ≤ f u) :
    (∑ z : (ZMod p)ˣ, f (K * z ^ 2)) ≤ 2 * ∑ u : (ZMod p)ˣ, f u := by
  classical
  have hmaps : ∀ z ∈ (Finset.univ : Finset (ZMod p)ˣ),
      K * z ^ 2 ∈ (Finset.univ : Finset (ZMod p)ˣ) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun z => f (K * z ^ 2)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  have heq : (Finset.univ.filter (fun z : (ZMod p)ˣ => K * z ^ 2 = u)) =
      Finset.univ.filter (fun z : (ZMod p)ˣ => z ^ 2 = K⁻¹ * u) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]
    · intro h
      rw [h, ← mul_assoc, mul_inv_cancel, one_mul]
  have hsum : (∑ z ∈ Finset.univ.filter (fun z : (ZMod p)ˣ => K * z ^ 2 = u),
      f (K * z ^ 2)) =
      ((Finset.univ.filter (fun z : (ZMod p)ˣ => z ^ 2 = K⁻¹ * u)).card : ℝ) * f u := by
    calc
      _ = ∑ _z ∈ Finset.univ.filter (fun z : (ZMod p)ˣ => K * z ^ 2 = u), f u := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [(Finset.mem_filter.mp hz).2]
      _ = _ := by simp only [heq, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  apply mul_le_mul_of_nonneg_right _ (hf u)
  exact_mod_cast unit_square_fiber_card_le_two Finset.univ (K⁻¹ * u)

/-- Inverting the sampling coordinate preserves the same square-coset bound. -/
theorem sum_inverse_square_coset_le_twice {p : ℕ} [Fact p.Prime]
    (K : (ZMod p)ˣ) (f : (ZMod p)ˣ → ℝ) (hf : ∀ u, 0 ≤ f u) :
    (∑ z : (ZMod p)ˣ, f (K * (z⁻¹) ^ 2)) ≤ 2 * ∑ u : (ZMod p)ˣ, f u := by
  have h := (Equiv.inv (ZMod p)ˣ).bijective.sum_comp
    (fun z => f (K * z ^ 2))
  change (∑ z : (ZMod p)ˣ, f (K * (z⁻¹) ^ 2)) = _ at h
  rw [h]
  exact sum_square_coset_le_twice K f hf

end Ostmann

end OAI
