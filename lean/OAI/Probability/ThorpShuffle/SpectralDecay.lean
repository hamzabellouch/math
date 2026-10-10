import OAI.Probability.ThorpShuffle.Support

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem half_weight_sum (d : ℕ) :
    (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1)) = 1 - (1 / 2 : ℝ) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

theorem half_weight_geometric_identity (γ : ℝ) (d t : ℕ) (hdt : d ≤ t) :
    (2 * γ - 1) *
        (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j)) =
      γ ^ t - (1 / 2 : ℝ) ^ d * γ ^ (t - d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hd : d ≤ t := by omega
    have ht : t - d = (t - 1 - d) + 1 := by omega
    have ht' : t - (d + 1) = t - 1 - d := by omega
    rw [Finset.sum_range_succ, mul_add, ih hd, ht, ht', pow_succ, pow_succ]
    ring

theorem half_weight_geometric_bound (β γ : ℝ) (d t : ℕ)
    (hγ : 0 ≤ γ) (hrel : 1 - β ≤ 2 * γ - 1) (hdt : d ≤ t) :
    (1 - β) *
        (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j)) ≤ γ ^ t := by
  have hs : 0 ≤ ∑ j ∈ Finset.range d,
      (1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j) := by positivity
  calc
    _ ≤ (2 * γ - 1) *
        (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j)) :=
      mul_le_mul_of_nonneg_right hrel hs
    _ = γ ^ t - (1 / 2 : ℝ) ^ d * γ ^ (t - d) :=
      half_weight_geometric_identity γ d t hdt
    _ ≤ γ ^ t := sub_le_self _ (by positivity)

theorem spectral_track_unroll (d : ℕ) (H : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hstep : ∀ t j, j < d → H (t + 1) j =
      H t (j + 1) + (1 / 2 : ℝ) ^ (j + 1) * b t)
    (t j k : ℕ) (hjk : j + k ≤ d) (hkt : k ≤ t) :
    H t j = H (t - k) (j + k) +
      ∑ r ∈ Finset.range k, (1 / 2 : ℝ) ^ (j + r + 1) * b (t - 1 - r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ t := by omega
    have hjk' : j + k ≤ d := by omega
    rw [ih hjk' hk, Finset.sum_range_succ]
    have ht : t - k = (t - 1 - k) + 1 := by omega
    have hj : j + k < d := by omega
    rw [ht, hstep _ _ hj]
    have ht' : t - (k + 1) = t - 1 - k := by omega
    rw [ht']
    simp only [Nat.add_assoc]
    ring

theorem energy_of_spectral_tracks (d : ℕ) (H : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hstep : ∀ t j, j < d → H (t + 1) j =
      H t (j + 1) + (1 / 2 : ℝ) ^ (j + 1) * b t)
    (hzero : ∀ t, H t d = 0) (t : ℕ) (ht : d ≤ t) :
    H t 0 = ∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * b (t - 1 - j) := by
  simpa only [zero_add, hzero] using
    spectral_track_unroll d H b hstep t 0 d (by omega) ht

theorem scalar_decay (d : ℕ) (E b : ℕ → ℝ) (β γ η : ℝ)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hγ : 0 < γ) (hγ₁ : γ ≤ 1)
    (hrel : 1 - β ≤ 2 * γ - 1) (hη : 0 ≤ η)
    (hE : ∀ t, E t ≤ 1)
    (henergy : ∀ t, d ≤ t → E t =
      ∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * b (t - 1 - j))
    (hnoise : ∀ s, d ≤ s → b s ≤ (1 - β) * E s + η) :
    ∀ t, E t ≤ γ ^ t / γ ^ (2 * d) + η / β := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t ≤ 2 * d
    · have hp : γ ^ (2 * d) ≤ γ ^ t := pow_le_pow_of_le_one hγ.le hγ₁ ht
      have hquot : (1 : ℝ) ≤ γ ^ t / γ ^ (2 * d) :=
        (le_div_iff₀ (pow_pos hγ _)).mpr (by simpa using hp)
      have hc : 0 ≤ η / β := div_nonneg hη hβ.le
      linarith [hE t]
    · have hdt : d ≤ t := by omega
      rw [henergy t hdt]
      have hbound :
          (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * b (t - 1 - j)) ≤
          ∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) *
            ((1 - β) * (γ ^ (t - 1 - j) / γ ^ (2 * d) + η / β) + η) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjd := Finset.mem_range.mp hj
        have hsd : d ≤ t - 1 - j := by omega
        have hst : t - 1 - j < t := by omega
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (hnoise _ hsd).trans
          (add_le_add (mul_le_mul_of_nonneg_left (ih _ hst)
            (show 0 ≤ 1 - β by linarith)) (le_refl η))
      have hconstant : (1 - β) * (η / β) + η = η / β := by
        field_simp
        ring
      have hsplit :
          (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) *
            ((1 - β) * (γ ^ (t - 1 - j) / γ ^ (2 * d) + η / β) + η)) =
          ((1 - β) * (∑ j ∈ Finset.range d,
            (1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j))) / γ ^ (2 * d) +
          (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1)) * (η / β) := by
        calc
          _ = ∑ j ∈ Finset.range d,
              (((1 - β) * ((1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j))) /
                γ ^ (2 * d) + (1 / 2 : ℝ) ^ (j + 1) * (η / β)) := by
            apply Finset.sum_congr rfl
            intro j _
            linear_combination (1 / 2 : ℝ) ^ (j + 1) * hconstant
          _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
              ← Finset.sum_mul]
      rw [hsplit] at hbound
      have hgeom := half_weight_geometric_bound β γ d t hγ.le hrel hdt
      have hgeom' := div_le_div_of_nonneg_right hgeom (pow_nonneg hγ.le (2 * d))
      have hc : (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1)) * (η / β) ≤ η / β := by
        rw [half_weight_sum]
        have hz : 0 ≤ (1 / 2 : ℝ) ^ d := by positivity
        have hηβ : 0 ≤ η / β := div_nonneg hη hβ.le
        nlinarith
      linarith

theorem eight_block_geometric_choice : (31 / 32 : ℝ) ^ 198 ≤ (1 / 2 : ℝ) ^ 8 := by
  norm_num

end Conditional

end Thorp

end

end OAI
