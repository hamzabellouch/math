import OAI.NumberTheory.Ostmann.Arithmetic.BulkFrequencyRepresentative
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedAverageNorm

namespace OAI

/-! # The frequency/Page average on the fixed bulk residue representative -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem extend_eq_of_eq_off_range {σ J A : Type*} (e : J ↪ σ) (f : J → A)
    (v w : σ → A) (h : ∀ i ∉ Set.range e, v i = w i) :
    Function.extend e f v = Function.extend e f w := by
  funext i
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [e.injective.extend_apply, e.injective.extend_apply]
  · rw [Function.extend_apply' _ v i hi, Function.extend_apply' _ w i hi, h i hi]

noncomputable def movingFrequencyCorePageAverage {σ : Type*} (value : σ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) : ℂ :=
  (Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ *
    ∑ z : ZMod r × (ZMod r)ˣ,
      movingFrequencyCore value F E T R z.1.val z.2.val.val *
        pageGiantWeight input Q r z.2.val.val y

theorem movingFrequencyPageAverage_core {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyPageAverage value outside F E T nodes R r input Q y =
      (if ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds) then (1 : ℂ) else 0) *
      movingFrequencyCorePageAverage value F E T R r input Q y := by
  simp only [movingFrequencyPageAverage, movingFrequencyPairFactor_core,
    movingFrequencyCorePageAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem movingFrequencyCorePageAverage_bulk_residues {σ J : Type*}
    (base value : σ → ℕ) (e : J ↪ σ) (hv : ∀ i ∉ Set.range e, value i = base i)
    (r : ℕ) [NeZero r] (a : J → (ZMod r)ˣ)
    (ha : ∀ j, (value (e j) : ZMod r) = (a j : ZMod r))
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (hT : ∀ b j, (T b).CompensationAbsent (e j))
    (hR : ∀ b, (T b).frequencyProduct ∣ R) (hr : R ^ (n + 1) ∣ (r : ℤ))
    (input : PublishedProgressionInput) (Q : ℕ) (y : ℝ) :
    movingFrequencyCorePageAverage value F E T R r input Q y =
      movingFrequencyCorePageAverage (Function.extend e (fun j => (a j).val.val) base)
        F E T R r input Q y := by
  unfold movingFrequencyCorePageAverage
  apply congrArg ((Fintype.card (ZMod r × (ZMod r)ˣ) : ℂ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro z _
  rw [movingFrequencyCore_bulk_residues value e r a ha F E T R hf hT hR hr,
    extend_eq_of_eq_off_range e _ value base hv]

theorem movingFrequencyCorePageAverage_norm_le {σ : Type*} (value : σ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ)
    (y : ℝ) (hy : 0 ≤ y) :
    ‖movingFrequencyCorePageAverage value F E T R r input Q y‖ ≤
      2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) := by
  let B := 2 * (‖movingDataWeight (F false) (E false) (T false)‖ *
    ‖movingDataWeight (F true) (E true) (T true)‖)
  have hb (z : ZMod r × (ZMod r)ˣ) :
      ‖movingFrequencyCore value F E T R z.1.val z.2.val.val *
        pageGiantWeight input Q r z.2.val.val y‖ ≤ B := by
    unfold movingFrequencyCore
    split_ifs
    · rw [norm_mul, norm_mul, Complex.norm_conj]
      exact (mul_le_mul_of_nonneg_left (pageGiantWeight_norm_le_two input Q r _ y hy)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (mul_comm _ _)
    · simpa only [zero_mul, norm_zero] using
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hc : (Fintype.card (ZMod r × (ZMod r)ˣ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ZMod r × (ZMod r)ˣ) ≠ 0)
  rw [movingFrequencyCorePageAverage, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card (ZMod r × (ZMod r)ˣ) : ℝ)⁻¹ * ∑ _z : ZMod r × (ZMod r)ˣ, B :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => hb z))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end Ostmann

end OAI
