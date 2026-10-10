import OAI.NumberTheory.Ostmann.Tree.UniformCoordinateAverage
import OAI.NumberTheory.Ostmann.Arithmetic.SquareLiftExclusions
import OAI.NumberTheory.Ostmann.Arithmetic.WeightedFlagComparison

namespace OAI

/-! # Dropping all prime-square exclusions in the uniform CRT fibers -/

namespace Ostmann
open scoped BigOperators Classical

theorem squareLiftPairs_card (p : ℕ) [Fact p.Prime] (x₀ y₀ : ZMod p) :
    Fintype.card (SquareLiftPairs p x₀ y₀) = p ^ 2 := by
  rw [Fintype.card_prod, card_squareReduction_fiber, card_squareReduction_fiber, pow_two]

theorem squareLiftPairs_nonempty (p : ℕ) [Fact p.Prime] (x₀ y₀ : ZMod p) :
    Nonempty (SquareLiftPairs p x₀ y₀) := by
  exact ⟨⟨⟨(x₀.val : ZMod (p ^ 2)), by simp only [squareReduction_natCast, ZMod.natCast_zmod_val]⟩, ⟨(y₀.val : ZMod (p ^ 2)), by simp only [squareReduction_natCast, ZMod.natCast_zmod_val]⟩⟩⟩

/-- A simultaneous lift comparison for a signed integrand. The remaining
arithmetic conditions can be included in `F`; they are never conditioned away. -/
theorem joint_square_lift_removed_mass_le {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (J : I → Type*) [∀ i, Fintype (J i)]
    (a b : ∀ i, J i → ZMod (p i ^ 2)) (x₀ y₀ : ∀ i, ZMod (p i))
    (hy : ∀ i, y₀ i ≠ 0)
    (hrow : ∀ i j, squareReduction (p i) (a i j) ≠ 0 ∨ squareReduction (p i) (b i j) ≠ 0)
    (hbase : ∀ i j, squareReduction (p i) (a i j) * x₀ i +
      squareReduction (p i) (b i j) * y₀ i = 0)
    (F : (∀ i, SquareLiftPairs (p i) (x₀ i) (y₀ i)) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    (Fintype.card (∀ i, SquareLiftPairs (p i) (x₀ i) (y₀ i)) : ℝ)⁻¹ *
      ‖(∑ x, if ∀ i j, a i j * (x i).1.1 + b i j * (x i).2.1 ≠ 0 then F x else 0) -
        ∑ x, F x‖ ≤ 2 * B * ∑ i, (Fintype.card (J i) : ℝ) / p i := by
  let X := fun i => SquareLiftPairs (p i) (x₀ i) (y₀ i)
  let : ∀ i, Nonempty (X i) := fun i => squareLiftPairs_nonempty _ _ _
  let bad := fun i (x : X i) => ∃ j, a i j * x.1.1 + b i j * x.2.1 = 0
  let w : ℝ := (Fintype.card (∀ i, X i) : ℝ)⁻¹
  have hw : 0 ≤ w := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hlocal (i : I) : (Fintype.card (X i) : ℝ)⁻¹ *
      (∑ x : X i, if bad i x then (1 : ℝ) else 0) ≤
      (Fintype.card (J i) : ℝ) / p i := by
    have h := square_lift_nonzero_rows_removed_mass_le (a i) (b i) (x₀ i) (y₀ i)
      (hy i) (hrow i) (hbase i) (fun _ => (1 : ℂ)) 1 (by norm_num) (by simp)
    rw [squareLiftPairs_card]
    simpa only [bad, X, ← Finset.sum_filter, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.cast_pow, norm_natCast, one_mul, div_eq_mul_inv, mul_comm] using h
  have hprob (i : I) : ∑ x : ∀ i, X i, w * (if bad i (x i) then (1 : ℝ) else 0) ≤
      (Fintype.card (J i) : ℝ) / p i := by
    rw [← Finset.mul_sum]
    exact (uniform_pi_coordinate_average X i (fun x => if bad i x then 1 else 0)).trans_le (hlocal i)
  let Ψ := fun (x : ∀ i, X i) (flags : I → Bool) => if ∀ i, flags i = true then F x else 0
  have h := weighted_flag_comparison_le (fun _ : ∀ i, X i => w) (fun _ => hw)
    (fun x i => decide (¬bad i (x i))) (fun _ _ => true)
    (fun i x => bad i (x i))
    (by intro x hx; funext i; simp [hx i]) Ψ B hB (by
      intro x flags
      dsimp only [Ψ]
      split_ifs
      · exact hF x
      · simpa using hB)
  have he (x : ∀ i, X i) : Ψ x (fun i => decide (¬bad i (x i))) =
      if ∀ i j, a i j * (x i).1.1 + b i j * (x i).2.1 ≠ 0 then F x else 0 := by
    simp only [Ψ, decide_eq_true_eq, bad, not_exists]
  simp only [he, Ψ, implies_true, ite_true] at h
  have hn : ‖∑ x : ∀ i, X i, (w : ℂ) *
      ((if ∀ i j, a i j * (x i).1.1 + b i j * (x i).2.1 ≠ 0 then F x else 0) - F x)‖ =
      w * ‖(∑ x, if ∀ i j, a i j * (x i).1.1 + b i j * (x i).2.1 ≠ 0 then F x else 0) -
        ∑ x, F x‖ := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hw]
  rw [hn] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hprob i) (by positivity))

end Ostmann

end OAI
