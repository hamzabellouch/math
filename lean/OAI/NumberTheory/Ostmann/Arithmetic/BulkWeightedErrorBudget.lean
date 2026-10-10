import OAI.NumberTheory.Ostmann.Arithmetic.IndexedBulkCellError
import OAI.NumberTheory.Ostmann.ZeroDensity.BulkProgressionRate

namespace OAI

/-! # Counting the actual cells and residues in the bulk comparison error -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem bulkPrimeErrorFactor_nonneg (P : PublishedProgressionInput) (Q : ℕ) (u : ℝ) :
    0 ≤ bulkPrimeErrorFactor P Q u := by
  unfold bulkPrimeErrorFactor
  have := P.errorConstant_nonneg
  positivity

theorem bulkPrimeErrorFactor_antitone (P : PublishedProgressionInput) {Q : ℕ} (hQ : 2 ≤ Q)
    {u v : ℝ} (huv : u ≤ v) : bulkPrimeErrorFactor P Q v ≤ bulkPrimeErrorFactor P Q u := by
  have hlog : 0 < Real.log (4 * (Q : ℝ)) := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hroot : -P.decay * Real.sqrt v ≤ -P.decay * Real.sqrt u :=
    mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt huv) (neg_nonpos.mpr P.decay_pos.le)
  have hpage : -P.kappa * v / Real.log (4 * (Q : ℝ)) ≤
      -P.kappa * u / Real.log (4 * (Q : ℝ)) := by
    apply div_le_div_of_nonneg_right _ hlog.le
    exact mul_le_mul_of_nonpos_left huv (neg_nonpos.mpr P.kappa_pos.le)
  unfold bulkPrimeErrorFactor
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hroot)
        (mul_nonneg (by norm_num) P.errorConstant_nonneg))
      (Real.exp_le_exp.mpr hpage))
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg huv)) (by norm_num))

theorem bulkKernelPairComparisonBudget_nonneg (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ)
    (n d r e : ℕ) (B D : ℝ) : 0 ≤ bulkKernelPairComparisonBudget ψ V lo hi n d r e B D := by
  unfold bulkKernelPairComparisonBudget
  positivity

/-- Every residue and real cell in the actual comparison is counted here;
only the smallest lower endpoint is used for the progression saving. -/
theorem bulk_weighted_error_budget {J Cell : Type*} [Fintype J] [Fintype Cell]
    (P : PublishedProgressionInput) {Q M : ℕ} [NeZero M] (hQ : 2 ≤ Q)
    (Z : J → ℝ) (hZ : ∀ j, 0 ≤ Z j)
    (a : (J → (ZMod M)ˣ) → ℂ) (A : ℝ) (hA : 0 ≤ A) (ha : ∀ z, ‖a z‖ ≤ A)
    (u : J → Cell → ℝ) (T : ℝ) (hu : ∀ j c, T ≤ u j c)
    (B : ℝ) (hB : 0 ≤ B) :
    (∏ j, Z j) * ∑ c : J → Cell, ∑ z : J → (ZMod M)ˣ, ‖a z‖ *
      (2 ^ Fintype.card J * ∑ j, B * bulkPrimeErrorFactor P Q (u j (c j))) ≤
    ((∏ j, Z j) * (Fintype.card Cell : ℝ) ^ Fintype.card J *
      (Fintype.card (ZMod M)ˣ : ℝ) ^ Fintype.card J * A *
      2 ^ Fintype.card J * (Fintype.card J : ℝ) * B) * bulkPrimeErrorFactor P Q T := by
  have hpoint (c : J → Cell) :
      2 ^ Fintype.card J * ∑ j, B * bulkPrimeErrorFactor P Q (u j (c j)) ≤
      2 ^ Fintype.card J * (Fintype.card J : ℝ) * B * bulkPrimeErrorFactor P Q T := by
    apply le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (bulkPrimeErrorFactor_antitone P hQ (hu j (c j))) hB) (by positivity))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring_nf
    rfl
  calc
    _ ≤ (∏ j, Z j) * ∑ _c : J → Cell, ∑ _z : J → (ZMod M)ˣ,
        A * (2 ^ Fintype.card J * (Fintype.card J : ℝ) * B * bulkPrimeErrorFactor P Q T) := by
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun j _ => hZ j)
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul (ha z) (hpoint c)
        (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
          mul_nonneg hB (bulkPrimeErrorFactor_nonneg P Q (u j (c j))))) hA
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, nsmul_eq_mul]
      ring

end Ostmann

end OAI
