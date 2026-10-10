import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedNorm

namespace OAI

/-! # Pointwise costs of the actual regular multiplier -/

namespace Ostmann
open scoped Classical BigOperators

theorem guardedRegularMultiplier_le_prime_product {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (other : ∀ i, ZMod (p i)) (g : ∀ i, ZMod (p i) → ℂ)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i) (a b : ℕ) :
    0 ≤ guardedRegularMultiplier p active s other g a b ∧
      guardedRegularMultiplier p active s other g a b ≤ ∏ i, (p i : ℝ) := by
  have hlocal (i) (x : ZMod (p i)) : ‖g i x‖ ^ 2 ≤ (p i : ℝ) := by
    rw [← henergy i]
    exact Finset.single_le_sum (fun y _ => sq_nonneg ‖g i y‖) (Finset.mem_univ x)
  unfold guardedRegularMultiplier naturalRegularMultiplier
  split_ifs
  · constructor
    · exact Finset.prod_nonneg fun i _ => by split <;> positivity
    · apply Finset.prod_le_prod₀
      · intro i _
        split <;> positivity
      · intro i _
        cases active i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact_mod_cast (Fact.out : (p i).Prime).one_le
        · exact hlocal i _
  · exact ⟨le_rfl, Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)⟩

theorem movingReducedPair_with_regular_norm {σ I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (reg : J → ℕ) [∀ j, Fact (reg j).Prime]
    (value : σ → ℕ) (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i z, ‖g i z‖ ≤ p i)
    (Dq : Bool → ∀ i, (ZMod (p i))ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (hweight : ∀ b, ‖movingDataWeight (F b) (E b) (T b)‖ ≤ 1)
    (active : J → Bool) (s : ℤ) (other : ∀ j, ZMod (reg j))
    (greg : ∀ j, ZMod (reg j) → ℂ)
    (henergy : ∀ j, (∑ x : ZMod (reg j), ‖greg j x‖ ^ 2) = reg j) (a b : ℕ) :
    ‖movingReducedPairResidueCoefficient p value outside F E g Dq Finset.univ T nodes a b *
      (guardedRegularMultiplier reg active s other greg a b : ℂ)‖ ≤
        (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 * ∏ j, (reg j : ℝ) := by
  have hc := movingReducedPairResidueCoefficient_norm p value outside F E g Dq Finset.univ
    (fun i => (p i : ℝ)) (fun i _ => Nat.cast_nonneg _) (fun i _ => hg i) T nodes a b
  have hr := guardedRegularMultiplier_le_prime_product reg active s other greg henergy a b
  have hprod : 0 ≤ ∏ i, (p i : ℝ) ^ (2 ^ n) := by positivity
  have hcs : ‖movingReducedPairResidueCoefficient p value outside F E g Dq Finset.univ T nodes a b‖ ≤
      (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 := by
    apply hc.trans
    have hh := mul_le_mul (mul_le_mul_of_nonneg_right (hweight false) hprod)
      (mul_le_mul_of_nonneg_right (hweight true) hprod) (by positivity) (by positivity)
    simpa only [one_mul, pow_two] using hh
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.1]
  exact mul_le_mul hcs hr.2 hr.1 (sq_nonneg _)

end Ostmann

end OAI
