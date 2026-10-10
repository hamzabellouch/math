import Mathlib

namespace OAI

namespace UniformKServer
/-- Downward rounding at every label other than the reserved allowed label.
The reserved label receives the remainder, exactly as in Section 02. -/
noncomputable def roundedRow {k : ℕ} (q : Fin k → ℝ) (j₀ : Fin k) (B : ℕ)
    (j : Fin k) : ℝ :=
  if j = j₀ then
    1 - ∑ i ∈ Finset.univ.erase j₀, (⌊(B : ℝ) * q i⌋₊ : ℝ) / B
  else (⌊(B : ℝ) * q j⌋₊ : ℝ) / B


theorem floor_fraction_bounds {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ j, 0 ≤ q j) (B : ℕ) (hB : 0 < B) (j : Fin k) :
    0 ≤ (⌊(B : ℝ) * q j⌋₊ : ℝ) / B ∧
    (⌊(B : ℝ) * q j⌋₊ : ℝ) / B ≤ q j ∧
    q j - (⌊(B : ℝ) * q j⌋₊ : ℝ) / B ≤ 1 / B := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hf := Nat.floor_le (mul_nonneg (le_of_lt hb) (hq j))
  have hg := Nat.lt_floor_add_one ((B : ℝ) * q j)
  refine ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hb), ?_, ?_⟩
  · exact (div_le_iff₀ hb).2 (by simpa [mul_comm] using hf)
  · apply (le_div_iff₀ hb).2
    have hb0 : (B : ℝ) ≠ 0 := ne_of_gt hb
    field_simp
    simp only [mul_comm (q j) (B : ℝ)]
    linarith

theorem round_row_sum {k : ℕ} (q : Fin k → ℝ)
    (j₀ : Fin k) (B : ℕ) : ∑ j, roundedRow q j₀ B j = 1 := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀)]
  simp only [roundedRow, ↓reduceIte]
  have he : ∑ x ∈ Finset.univ.erase j₀,
      (if x = j₀ then 1 - ∑ i ∈ Finset.univ.erase j₀,
        (⌊(B : ℝ) * q i⌋₊ : ℝ) / B
       else (⌊(B : ℝ) * q x⌋₊ : ℝ) / B) =
      ∑ x ∈ Finset.univ.erase j₀, (⌊(B : ℝ) * q x⌋₊ : ℝ) / B := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.ne_of_mem_erase hi]
  rw [he]
  ring

theorem round_row_nonneg {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hs : ∑ j, q j = 1)
    (j₀ : Fin k) (B : ℕ) (hB : 0 < B) (j : Fin k) :
    0 ≤ roundedRow q j₀ B j := by
  classical
  unfold roundedRow
  split_ifs
  · have hd : ∑ i ∈ Finset.univ.erase j₀,
        (⌊(B : ℝ) * q i⌋₊ : ℝ) / B ≤ ∑ i ∈ Finset.univ.erase j₀, q i :=
      Finset.sum_le_sum (fun i _ => (floor_fraction_bounds q hq B hB i).2.1)
    have ht := Finset.sum_erase_add Finset.univ q (Finset.mem_univ j₀)
    rw [hs] at ht
    have := hq j₀
    linarith
  · exact (floor_fraction_bounds q hq B hB j).1


noncomputable def rowLoss {k : ℕ} (q : Fin k → ℝ)
    (j₀ : Fin k) (B : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.erase j₀, (q i - (⌊(B : ℝ) * q i⌋₊ : ℝ) / B)

theorem rowLoss_bounds {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ j, 0 ≤ q j) (j₀ : Fin k) (B : ℕ) (hB : 0 < B) :
    0 ≤ rowLoss q j₀ B ∧ rowLoss q j₀ B ≤ k / (B : ℝ) := by
  classical
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  refine ⟨Finset.sum_nonneg (fun j _ => sub_nonneg.mpr
    (floor_fraction_bounds q hq B hB j).2.1), ?_⟩
  calc
    rowLoss q j₀ B ≤ ∑ _i ∈ Finset.univ.erase j₀, (1 : ℝ) / B :=
      Finset.sum_le_sum (fun i _ => (floor_fraction_bounds q hq B hB i).2.2)
    _ ≤ ∑ _i : Fin k, (1 : ℝ) / B :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun _ _ _ => div_nonneg (by norm_num) (le_of_lt hb))
    _ = k / (B : ℝ) := by simp [div_eq_mul_inv]

theorem round_reserve {k : ℕ} (q : Fin k → ℝ)
    (hs : ∑ j, q j = 1) (j₀ : Fin k) (B : ℕ) :
    roundedRow q j₀ B j₀ = q j₀ + rowLoss q j₀ B := by
  classical
  have ht := Finset.sum_erase_add Finset.univ q (Finset.mem_univ j₀)
  rw [hs] at ht
  simp only [roundedRow, ↓reduceIte, rowLoss, Finset.sum_sub_distrib]
  linarith

theorem round_row_expectation {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hs : ∑ j, q j = 1) (j₀ : Fin k)
    (B : ℕ) (hB : 0 < B) (v : Fin k → ℝ) (T : ℝ)
    (hv : ∀ j, 0 ≤ v j ∧ v j ≤ T) :
    (∑ j, roundedRow q j₀ B j * v j) ≤
      (∑ j, q j * v j) + k / (B : ℝ) * T := by
  classical
  have hothers : (∑ i ∈ Finset.univ.erase j₀, roundedRow q j₀ B i * v i) ≤
      ∑ i ∈ Finset.univ.erase j₀, q i * v i := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (hv i).1
    simpa [roundedRow, Finset.ne_of_mem_erase hi] using
      (floor_fraction_bounds q hq B hB i).2.1
  have hsum := Finset.sum_erase_add Finset.univ (fun i => q i * v i)
    (Finset.mem_univ j₀)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀), round_reserve q hs]
  have hl := rowLoss_bounds q hq j₀ B hB
  have hlt := mul_le_mul_of_nonneg_left (hv j₀).2 hl.1
  have hT : 0 ≤ T := le_trans (hv j₀).1 (hv j₀).2
  have hlt' := mul_le_mul_of_nonneg_right hl.2 hT
  nlinarith


end UniformKServer




end OAI
