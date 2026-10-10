import OAI.NumberTheory.Ostmann.Construction.WordCharacterRemoval
import OAI.NumberTheory.Ostmann.Construction.TopWordBinScale

namespace OAI

/-! # The sampled bin and cell restrictions give the formal product window -/

namespace Ostmann

open scoped BigOperators Classical

theorem wordCopy_log_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {k m : ℕ}
    (z : ((Fin k → P) × (Fin m → P)) × ((Fin k → P) × (Fin m → P))) :
    Real.log (∏ i, (wordCopyEquiv P k m z i : ℝ)) =
      (∑ i, Real.log (z.1.1 i : ℝ)) + (∑ i, Real.log (z.1.2 i : ℝ)) +
        (∑ i, Real.log (z.2.1 i : ℝ)) + (∑ i, Real.log (z.2.2 i : ℝ)) := by
  rw [Real.log_prod (fun i _ => by exact_mod_cast (hP _ (wordCopyEquiv P k m z i).property).ne_zero)]
  let f : P → ℝ := fun p => Real.log (p : ℝ)
  change (∑ i, f (Fin.append (Fin.append z.1.1 z.1.2)
    (Fin.append z.2.1 z.2.2) i)) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  dsimp [f]
  ring

theorem harmonic_word_log_error (P : Finset ℕ) {n : ℕ} (Q : Fin n → Finset ℕ)
    (x : Fin n → P) (hx : productPrior (fun i => primeSubsetPrior P (Q i)) x ≠ 0)
    (T e : Fin n → ℝ)
    (he : ∀ i p, p ∈ Q i → |Real.log (p : ℝ) - T i| ≤ e i) :
    |(∑ i, Real.log (x i : ℝ)) - ∑ i, T i| ≤ ∑ i, e i := by
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  exact he i _ (primeSubsetPrior_support P (Q i) (x i)
    ((Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)))

/-- Both sampled word copies have the selected bin. Both cell copies retain
exactly their original supports; the full formal product has bounded log error. -/
theorem word_event_log_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {B : Type*} {k m : ℕ} (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (bin : (Fin k → P) → B) (b : B) (J W : ℝ) (T e : Fin m → ℝ)
    (hbin : ∀ w, productPrior (fun i => primeSubsetPrior P (Q i)) w ≠ 0 →
      bin w = b → |(∑ i, Real.log (w i : ℝ)) - J| ≤ W)
    (hcells : ∀ i p, p ∈ R i → |Real.log (p : ℝ) - T i| ≤ e i)
    (x : Fin ((k + m) + (k + m)) → P)
    (hx : x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b) :
    |Real.log (∏ i, (x i : ℝ)) - (2 * J + 2 * ∑ i, T i)| ≤
      2 * W + 2 * ∑ i, e i := by
  let z := (wordCopyEquiv P k m).symm x
  have hz : wordCopyEquiv P k m z = x := Equiv.apply_symm_apply _ _
  obtain ⟨_, hb, hw⟩ := Finset.mem_filter.mp hx
  change (bin z.1.1 = b ∧ bin z.2.1 = b) at hb
  rw [← hz, wordCopyPrior] at hw
  have h₁ := (mul_ne_zero_iff.mp hw).1
  have h₂ := (mul_ne_zero_iff.mp hw).2
  have hc₁ := harmonic_word_log_error P R z.1.2 (mul_ne_zero_iff.mp h₁).2 T e hcells
  have hc₂ := harmonic_word_log_error P R z.2.2 (mul_ne_zero_iff.mp h₂).2 T e hcells
  have hb₁ := hbin z.1.1 (mul_ne_zero_iff.mp h₁).1 hb.1
  have hb₂ := hbin z.2.1 (mul_ne_zero_iff.mp h₂).1 hb.2
  rw [← hz, wordCopy_log_product P hP]
  have h := abs_add_le
    (((∑ i, Real.log (z.1.1 i : ℝ)) - J) + ((∑ i, Real.log (z.1.2 i : ℝ)) - ∑ i, T i))
    (((∑ i, Real.log (z.2.1 i : ℝ)) - J) + ((∑ i, Real.log (z.2.2 i : ℝ)) - ∑ i, T i))
  have h₁' := abs_add_le ((∑ i, Real.log (z.1.1 i : ℝ)) - J)
    ((∑ i, Real.log (z.1.2 i : ℝ)) - ∑ i, T i)
  have h₂' := abs_add_le ((∑ i, Real.log (z.2.1 i : ℝ)) - J)
    ((∑ i, Real.log (z.2.2 i : ℝ)) - ∑ i, T i)
  have heq : (∑ i, Real.log (z.1.1 i : ℝ)) + (∑ i, Real.log (z.1.2 i : ℝ)) +
      (∑ i, Real.log (z.2.1 i : ℝ)) + (∑ i, Real.log (z.2.2 i : ℝ)) -
      (2 * J + 2 * ∑ i, T i) =
      (((∑ i, Real.log (z.1.1 i : ℝ)) - J) + ((∑ i, Real.log (z.1.2 i : ℝ)) - ∑ i, T i)) +
      (((∑ i, Real.log (z.2.1 i : ℝ)) - J) + ((∑ i, Real.log (z.2.2 i : ℝ)) - ∑ i, T i)) := by ring
  rw [heq]
  linarith

theorem product_window_of_log_error (M X D E : ℝ) (hM : 0 < M) (hX : 0 < X)
    (hlog : |Real.log M - (Real.log X + D)| ≤ E) :
    X * Real.exp (D - E) ≤ M ∧ M ≤ X * Real.exp (D + E) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hlog
  constructor
  · have h := Real.exp_le_exp.mpr (show Real.log X + (D - E) ≤ Real.log M by linarith)
    simpa only [Real.exp_add, Real.exp_log hX, Real.exp_log hM] using h
  · have h := Real.exp_le_exp.mpr (show Real.log M ≤ Real.log X + (D + E) by linarith)
    simpa only [Real.exp_add, Real.exp_log hX, Real.exp_log hM] using h

/-- The clipped finite bin has the ordinary floor error on its valid support. -/
theorem wordLogBin_log_error {m : ℕ} (τ : ℝ) (ℓ : Fin (m + 1) → ℝ)
    (hlo : 0 ≤ ∑ i, ℓ i) (hhi : (∑ i, ℓ i) ≤ 4 * τ) :
    |(∑ i, ℓ i) - (wordLogBin τ ℓ).val| ≤ 1 := by
  rw [wordLogBin_val τ ℓ hhi]
  have h₁ := Nat.floor_le hlo
  have h₂ := Nat.lt_floor_add_one (∑ i, ℓ i)
  apply abs_le.mpr
  constructor <;> linarith

theorem word_event_product_window (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {B : Type*} {k m : ℕ} (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (bin : (Fin k → P) → B) (b : B) (J W : ℝ) (T e : Fin m → ℝ)
    (hbin : ∀ w, productPrior (fun i => primeSubsetPrior P (Q i)) w ≠ 0 →
      bin w = b → |(∑ i, Real.log (w i : ℝ)) - J| ≤ W)
    (hcells : ∀ i p, p ∈ R i → |Real.log (p : ℝ) - T i| ≤ e i)
    (X D E : ℝ) (hX : 0 < X)
    (hcenter : |2 * J + 2 * (∑ i, T i) - (Real.log X + D)| ≤ E)
    (x : Fin ((k + m) + (k + m)) → P)
    (hx : x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b) :
    X * Real.exp (D - (2 * W + 2 * (∑ i, e i) + E)) ≤ ∏ i, (x i : ℝ) ∧
      (∏ i, (x i : ℝ)) ≤ X * Real.exp (D + (2 * W + 2 * (∑ i, e i) + E)) := by
  have hw := word_event_log_product P hP Q R bin b J W T e hbin hcells x hx
  apply product_window_of_log_error _ X D _
    (Finset.prod_pos (fun i _ => by exact_mod_cast (hP _ (x i).property).pos)) hX
  have hh := (abs_add_le (Real.log (∏ i, (x i : ℝ)) - (2 * J + 2 * ∑ i, T i))
    (2 * J + 2 * (∑ i, T i) - (Real.log X + D))).trans (add_le_add hw hcenter)
  simpa only [sub_add_sub_cancel] using hh

end Ostmann

end OAI
