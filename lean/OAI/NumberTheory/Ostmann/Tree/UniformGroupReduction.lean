import Mathlib.GroupTheory.Coset.Card
import OAI.NumberTheory.Ostmann.Arithmetic.SquareRootProbability

namespace OAI

/-! # Uniform unit reduction to a divisor of the frequency modulus -/

namespace Ostmann

open scoped BigOperators Classical

theorem surjective_group_sum {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f) (F : H → ℝ) :
    (∑ x : G, F (f x)) = (Fintype.card f.ker : ℝ) * ∑ y : H, F y := by
  have hcard (y : H) : (Finset.univ.filter (fun x : G => f x = y)).card =
      Fintype.card f.ker := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (MonoidHom.fiberEquivKerOfSurjective hf y)
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) (fun x => F (f x))]
  calc
    _ = ∑ y : H, (Fintype.card f.ker : ℝ) * F y := by
      apply Finset.sum_congr rfl
      intro y _
      calc
        _ = ∑ _x ∈ Finset.univ.filter (fun x : G => f x = y), F y :=
          Finset.sum_congr rfl fun _ hx => congrArg F (Finset.mem_filter.mp hx).2
        _ = _ := by simp [hcard]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem surjective_group_average {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f) (F : H → ℝ) :
    (Fintype.card G : ℝ)⁻¹ * (∑ x : G, F (f x)) =
      (Fintype.card H : ℝ)⁻¹ * ∑ y : H, F y := by
  have hc : (Fintype.card G : ℝ) =
      (Fintype.card f.ker : ℝ) * Fintype.card H := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      using surjective_group_sum f hf (fun _ => (1 : ℝ))
  have hk : (Fintype.card f.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [surjective_group_sum f hf F, hc, mul_inv_rev]
  field_simp

theorem unit_reduction_average {q Q : ℕ} [NeZero q] [NeZero Q] (h : q ∣ Q)
    (F : (ZMod q)ˣ → ℝ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ *
        (∑ x : (ZMod Q)ˣ, F (ZMod.unitsMap h x)) =
      (Fintype.card (ZMod q)ˣ : ℝ)⁻¹ * ∑ y : (ZMod q)ˣ, F y :=
  surjective_group_average (ZMod.unitsMap h) (ZMod.unitsMap_surjective h) F

theorem unit_reduction_square_probability_le {q Q : ℕ} [NeZero q] [NeZero Q]
    (h : q ∣ Q) (a : (ZMod q)ˣ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ *
        (∑ x : (ZMod Q)ˣ, if (ZMod.unitsMap h x) ^ 2 = a then (1 : ℝ) else 0) ≤
      2 * (q.divisors.card : ℝ) ^ 2 / q := by
  rw [unit_reduction_average h (fun x => if x ^ 2 = a then (1 : ℝ) else 0)]
  have hs : (∑ x : (ZMod q)ˣ, if x ^ 2 = a then (1 : ℝ) else 0) =
      (Nat.card {x : (ZMod q)ˣ // x ^ 2 = a} : ℝ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hs, mul_comm, ← div_eq_mul_inv]
  exact unit_square_probability_le q a

end Ostmann

end OAI
