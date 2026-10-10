import OAI.NumberTheory.TwoPoint.Bounds.ProgressionFourier

namespace OAI

/-!
# Sampling the published short-interval estimate

For integral short lengths, a moving short sum is constant on each unit
cell of its origin. Thus its published integral controls the actual finite
sum of integer origins, with outer cutoff `Y+1`. The progression restriction
is an average of fixed frequencies and has total coefficient mass one.
-/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma shortExponentialSum_on_unit_cell (b : ℕ → ℂ) (D : ℕ) (α : ℝ)
    (v : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (v : ℝ) (v + 1)) :
    shortExponentialSum b D α y = shortExponentialSum b D α v := by
  have hy0 : 0 ≤ y := (Nat.cast_nonneg v).trans hy.1
  have hf := Nat.floor_eq_on_Ico v y hy
  unfold shortExponentialSum
  rw [Nat.floor_add_natCast hy0, hf, Nat.floor_natCast,
    Nat.floor_add_natCast (Nat.cast_nonneg v) D, Nat.floor_natCast]

lemma shortExponentialSum_unit_integrable (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) :
    IntervalIntegrable (fun y => ‖shortExponentialSum b D α y‖)
      volume (v : ℝ) (v + 1) := by
  apply (intervalIntegrable_const : IntervalIntegrable
    (fun _ : ℝ => ‖shortExponentialSum b D α v‖) volume (v : ℝ) (v + 1)).congr_uIoo
  intro y hy
  rw [Set.uIoo_of_le (by linarith : (v : ℝ) ≤ v + 1)] at hy
  exact congrArg norm (shortExponentialSum_on_unit_cell b D α v ⟨hy.1.le, hy.2⟩).symm

lemma integral_shortExponentialSum_unit (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) :
    (∫ y in (v : ℝ)..(v + 1), ‖shortExponentialSum b D α y‖) =
      ‖shortExponentialSum b D α v‖ := by
  calc
    _ = ∫ _y in (v : ℝ)..(v + 1), ‖shortExponentialSum b D α v‖ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
      intro y hy
      exact congrArg norm (shortExponentialSum_on_unit_cell b D α v ⟨hy.1.le, hy.2⟩)
    _ = _ := by simp

/-- Exact unit-cell decomposition, with no endpoint error. -/
theorem shortExponentialIntegral_eq_sum (b : ℕ → ℂ) (X D : ℕ) (α : ℝ) :
    shortExponentialIntegral b X D α =
      ∑ v ∈ range X, ‖shortExponentialSum b D α v‖ := by
  unfold shortExponentialIntegral
  symm
  calc
    _ = ∑ v ∈ range X, ∫ y in (v : ℝ)..((v + 1 : ℕ) : ℝ),
        ‖shortExponentialSum b D α y‖ := by
      apply sum_congr rfl
      intro v _
      simpa only [Nat.cast_add, Nat.cast_one] using
        (integral_shortExponentialSum_unit b D α v).symm
    _ = _ := by
      simpa only [Nat.cast_zero] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun n : ℕ => (n : ℝ)) (n := X)
          (fun v _ => by simpa only [Nat.cast_add, Nat.cast_one] using
            shortExponentialSum_unit_integrable b D α v))

/-- The positive integer origins used in the manuscript occupy all but
the first unit cell of the published integral. -/
theorem sum_positive_shortExponentialSum_le (b : ℕ → ℂ) (Y D : ℕ) (α : ℝ) :
    (∑ v ∈ range Y, ‖shortExponentialSum b D α (v + 1 : ℕ)‖) ≤
      shortExponentialIntegral b (Y + 1) D α := by
  rw [shortExponentialIntegral_eq_sum, sum_range_succ']
  exact le_add_of_nonneg_right (norm_nonneg _)

lemma sum_Icc_shift (f : ℕ → ℂ) (v D : ℕ) :
    (∑ n ∈ Icc (v + 1) (v + D), f n) = ∑ m ∈ range D, f (v + m + 1) := by
  symm
  apply sum_bij (fun m _ => v + m + 1)
  · intro m hm
    simp only [mem_range] at hm
    simp only [mem_Icc]
    omega
  · intro m hm n hn he
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    refine ⟨n - (v + 1), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro m _
    rfl

lemma shortExponentialSum_at_nat (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortExponentialSum b D α v =
      ∑ n ∈ Icc (v + 1) (v + D), b n * additiveCharacter α n := by
  simp only [shortExponentialSum, Nat.floor_natCast,
    Nat.floor_add_natCast (Nat.cast_nonneg v) D]

lemma additiveCharacter_nat_add (α : ℝ) (m n : ℕ) :
    additiveCharacter α (m + n) = additiveCharacter α m * additiveCharacter α n := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_additiveCharacter (α : ℝ) (n : ℕ) : ‖additiveCharacter α n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- The short Fourier polynomial indexed by increments `1,...,D`. -/
noncomputable def shortWindowSum (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) : ℂ :=
  ∑ m ∈ range D, b (v + m + 1) * additiveCharacter α (m + 1)

lemma shortExponentialSum_eq_window (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortExponentialSum b D α v = additiveCharacter α v * shortWindowSum b D α v := by
  rw [shortExponentialSum_at_nat, sum_Icc_shift]
  unfold shortWindowSum
  rw [mul_sum]
  apply sum_congr rfl
  intro m _
  rw [show v + m + 1 = v + (m + 1) by omega, additiveCharacter_nat_add]
  ring

lemma norm_shortExponentialSum_eq_window (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    ‖shortExponentialSum b D α v‖ = ‖shortWindowSum b D α v‖ := by
  rw [shortExponentialSum_eq_window, norm_mul, norm_additiveCharacter, one_mul]

/-- A uniform fixed-frequency integral bound controls every progression
class of actual discrete windows, including nonunit classes. -/
theorem progression_short_sum_from_integral (b : ℕ → ℂ) (D Y l : ℕ)
    [NeZero l] (a : ZMod l) (α K : ℝ)
    (hK : ∀ β : ℝ, shortExponentialIntegral b (Y + 1) D β ≤ K) :
    (∑ v ∈ range Y, ‖∑ n ∈ Icc (v + 2) (v + 1 + D),
      if (n : ZMod l) = a then b n * additiveCharacter α n else 0‖) ≤ K := by
  calc
    _ ≤ ∑ v ∈ range Y, (l : ℝ)⁻¹ * ∑ j : ZMod l,
        ‖∑ n ∈ Icc (v + 2) (v + 1 + D),
          b n * additiveCharacter (α + (j.val : ℝ) / l) n‖ :=
      sum_le_sum (fun v _ => norm_progression_fourier_le _ b l a α)
    _ = (l : ℝ)⁻¹ * ∑ j : ZMod l, ∑ v ∈ range Y,
        ‖shortExponentialSum b D (α + (j.val : ℝ) / l) (v + 1 : ℕ)‖ := by
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro v _
      rw [shortExponentialSum_at_nat]
    _ ≤ (l : ℝ)⁻¹ * ∑ _j : ZMod l, K := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum (fun j _ =>
        (sum_positive_shortExponentialSum_le b Y D _).trans (hK _))
    _ = K := by
      simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      have hl : (l : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne l
      field_simp

/-- Published MRT Theorem 1.3 applied to the actual progression windows. -/
theorem MRTLiouvilleShortInput.progression_integer_windows
    (hMRT : MRTLiouvilleShortInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y D l : ℕ), 10 ≤ D → D ≤ Y + 1 →
      ∀ [NeZero l] (a : ZMod l) (α : ℝ),
        (∑ v ∈ range Y, ‖∑ n ∈ Icc (v + 2) (v + 1 + D),
          if (n : ZMod l) = a then liouville n * additiveCharacter α n else 0‖) ≤
          C * (D : ℝ) * (Y + 1 : ℕ) * mrtShortError (Y + 1) D := by
  obtain ⟨C, hC, hbound⟩ := hMRT
  refine ⟨C, hC, ?_⟩
  intro Y D l hD hDY _ a α
  exact progression_short_sum_from_integral liouville D Y l a α _
    (fun β => hbound (Y + 1) D hD hDY β)

end TwoPointCorrelations

end OAI
