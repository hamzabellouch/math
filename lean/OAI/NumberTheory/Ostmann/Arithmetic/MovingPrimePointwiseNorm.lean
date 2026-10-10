import OAI.NumberTheory.Ostmann.Arithmetic.FrozenPrimeArithmeticNorm
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSpectatorNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorCost

namespace OAI

/-! # Pointwise costs for the literal two-prime arithmetic factors -/

namespace Ostmann
open scoped Classical BigOperators

private theorem finite_mean_norm_le {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℂ) (B : ℝ) (hf : ∀ a, ‖f a‖ ≤ B) :
    ‖(Fintype.card A : ℂ)⁻¹ * ∑ a, f a‖ ≤ B := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ _a : A, B :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hf a))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem movingFrequencyCorePrimeAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖movingFrequencyCorePrimeAverage value F E T R r input Q x y‖ ≤
      4 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  apply finite_mean_norm_le
  intro z
  have hcore : ‖movingFrequencyCore value F E T R z.1.val.val z.2.val.val‖ ≤
      ‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖ := by
    unfold movingFrequencyCore
    split_ifs
    · simp only [norm_mul, Complex.norm_conj, le_refl]
    · simp only [norm_zero]
      positivity
  have hw : ‖pageGiantWeight input Q r z.1.val.val x *
      pageGiantWeight input Q r z.2.val.val y‖ ≤ 4 := by
    rw [norm_mul]
    exact (mul_le_mul (pageGiantWeight_norm_le_two input Q r _ x hx)
      (pageGiantWeight_norm_le_two input Q r _ y hy) (norm_nonneg _) (by norm_num)).trans_eq
        (by norm_num)
  rw [norm_mul]
  exact (mul_le_mul hcore hw (norm_nonneg _) (by positivity)).trans_eq (mul_comm _ _)

theorem frozenBulkFrequencyPrime_norm_le {σ J : Type*}
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (childBound : ℕ → ℕ)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput)
    (Q : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (a : J → (ZMod r)ˣ) :
    ‖frozenBulkFrequencyPrime base slot outside F E T childBound R r input Q x y a‖ ≤
      4 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  unfold frozenBulkFrequencyPrime
  split_ifs
  · rw [one_mul]
    exact movingFrequencyCorePrimeAverage_norm_le _ F E T R r input Q x y hx hy
  · rw [zero_mul, norm_zero]
    positivity

theorem frozenBulkSpectatorPrime_norm_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ x, ‖g x‖ ≤ K)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) :
    ‖frozenBulkSpectatorPrime base n m t small samples D e g z‖ ≤ K ^ (2 ^ (n + 1)) := by
  apply finite_mean_norm_le
  exact fun a => frozenBulkSpectatorPair_norm_le base n m t small samples D e g K hK hg a z

theorem movingFrequencyPrimeAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖movingFrequencyPrimeAverage value outside F E T nodes R r input Q x y‖ ≤
      4 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  rw [movingFrequencyPrimeAverage_core]
  split_ifs
  · simpa only [one_mul] using
      movingFrequencyCorePrimeAverage_norm_le value F E T R r input Q x y hx hy
  · simp only [zero_mul, norm_zero]
    positivity

theorem movingSpectatorPrimeAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (q : ℕ) [Fact q.Prime] (g : ZMod q → ℂ) (D : Bool → (ZMod q)ˣ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ z, ‖g z‖ ≤ B) :
    ‖movingSpectatorPrimeAverage value q g D T‖ ≤ B ^ (2 ^ (n + 1)) := by
  apply finite_mean_norm_le
  intro z
  rw [movingSpectatorPairFactor, norm_mul, Complex.norm_conj]
  calc
    _ ≤ B ^ (2 ^ n) * B ^ (2 ^ n) :=
      mul_le_mul (movingModularSpectator_norm value q g (D false) B hB hg (T false) z.1 z.2)
        (movingModularSpectator_norm value q g (D true) B hB hg (T true) z.1 z.2)
        (norm_nonneg _) (pow_nonneg hB _)
    _ = _ := by rw [← pow_add, pow_succ]; congr 1; omega

theorem moving_frozen_prime_residue_coefficient_norm {σ J : Type*}
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ)
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (n m : ℕ) (data : Bool → MovingSlotData σ n) (childBound : ℕ → ℕ)
    (R : ℤ) (r : ℕ) [NeZero r] (P : PublishedProgressionInput) (Q : ℕ)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (hSp : ∀ i, (S i).card < p i)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List σ) n)
    (samples : Bool → MovingSampleSlots σ n)
    (twist : ∀ i, Bool → (ZMod (p i))ˣ)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (a : J → (ZMod r)ˣ) (z : ∀ i, TreeLeafIndex n × Fin m → (ZMod (p i))ˣ) :
    ‖frozenBulkFrequencyPrime base slot outside F E data childBound R r P Q x y a *
      ∏ i, frozenBulkSpectatorPrime base n m t small samples (twist i) perm
        (normalizedResidueTransform (S i)) (z i)‖ ≤
      (4 * (‖movingDataWeight (F false) (E false) (data false)‖ *
        ‖movingDataWeight (F true) (E true) (data true)‖)) *
          ∏ i, (p i : ℝ) ^ (2 ^ (n + 1)) := by
  rw [norm_mul, norm_prod]
  apply mul_le_mul
    (frozenBulkFrequencyPrime_norm_le base slot outside F E data childBound R r P Q x y hx hy a)
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ =>
      frozenBulkSpectatorPrime_norm_le base n m t small samples (twist i) perm
        (normalizedResidueTransform (S i)) (p i) (Nat.cast_nonneg _)
        (normalizedResidueTransform_norm_le_prime (S i) (hS i) (hSp i)) (z i)))
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)

end Ostmann

end OAI
