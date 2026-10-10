import Mathlib

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothSelector

def clip (x : ℝ) : ℝ := max 0 (min 1 x)

@[fun_prop] theorem clip_continuous : Continuous clip := by unfold clip; fun_prop

theorem clip_nonneg (x : ℝ) : 0 ≤ clip x := le_max_left _ _
theorem clip_le_one (x : ℝ) : clip x ≤ 1 := max_le zero_le_one (min_le_left _ _)
theorem clip_mono : Monotone clip := fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)
theorem clip_of_nonpos {x : ℝ} (hx : x ≤ 0) : clip x = 0 := by
  unfold clip; rw [max_eq_left (le_trans (min_le_right _ _) hx)]
theorem clip_of_one_le {x : ℝ} (hx : 1 ≤ x) : clip x = 1 := by
  unfold clip; rw [min_eq_left hx, max_eq_right zero_le_one]

/-- The consecutive ramp differences form an exact finite partition on a grid. -/
def hat (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) : ℝ :=
  clip (t/δ + N - i + 1) - clip (t/δ + N - i)

@[fun_prop] theorem hat_continuous (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) :
    Continuous (hat N δ i) := by unfold hat; fun_prop

theorem hat_nonneg (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    0 ≤ hat N δ i t := by
  unfold hat
  exact sub_nonneg.mpr (clip_mono (by linarith))

theorem hats_sum (N : ℕ) (δ t : ℝ) :
    ∑ i : Fin (2*N+1), hat N δ i t = clip (t/δ+N+1)-clip (t/δ-N) := by
  unfold hat
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    clip (t/δ+N-i+1)-clip (t/δ+N-i)) (2*N+1)]
  have he (i : ℕ) : clip (t/δ+N-i+1)-clip (t/δ+N-i) =
      clip (t/δ+N-i+1)-clip (t/δ+N-(i+1:ℕ)+1) := by push_cast; ring_nf
  simp_rw [he]
  rw [Finset.sum_range_sub']
  push_cast
  congr 1 <;> congr 1 <;> ring

theorem hats_sum_le_one (N : ℕ) (δ t : ℝ) :
    ∑ i : Fin (2*N+1), hat N δ i t ≤ 1 := by
  rw [hats_sum]
  linarith [clip_le_one (t/δ+N+1),clip_nonneg (t/δ-N)]

theorem hats_sum_eq_one {N : ℕ} {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ N*δ) :
    ∑ i : Fin (2*N+1), hat N δ i t = 1 := by
  rw [hats_sum]
  have ht' := abs_le.mp ht
  have hp : t/δ-N ≤ 0 := by
    have := (div_le_iff₀ hδ).mpr ht'.2
    linarith
  have hn : 1 ≤ t/δ+N+1 := by
    have : -(N:ℝ) ≤ t/δ := (le_div_iff₀ hδ).mpr (by linarith [ht'.1])
    linarith
  rw [clip_of_one_le hn,clip_of_nonpos hp,sub_zero]

def middle (N : ℕ) : Fin (2*N+1) := ⟨N, by omega⟩

def weight (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) : ℝ :=
  hat N δ i t + if i = middle N then 1-∑ j, hat N δ j t else 0

@[fun_prop] theorem weight_continuous (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) :
    Continuous (weight N δ i) := by
  unfold weight
  split_ifs <;> fun_prop

theorem weight_nonneg (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    0 ≤ weight N δ i t := by
  unfold weight
  split_ifs <;> linarith [hat_nonneg N δ i t, hats_sum_le_one N δ t]

@[simp] theorem weight_sum (N : ℕ) (δ t : ℝ) : ∑ i, weight N δ i t = 1 := by
  simp [weight, Finset.sum_add_distrib]

def center (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) : ℝ := 1+δ*(i-N)

@[simp] theorem center_middle (N : ℕ) (δ : ℝ) : center N δ (middle N) = 1 := by
  simp [center,middle]

theorem hat_local {N : ℕ} {δ t : ℝ} {i : Fin (2*N+1)} (hδ : 0 < δ)
    (hi : hat N δ i t ≠ 0) : |center N δ i-(1+t)| < δ := by
  have hlo : -1 < t/δ+N-i := by
    by_contra hn
    have h : t/δ+N-i+1 ≤ 0 := by linarith
    have h' : t/δ+N-i ≤ 0 := by linarith
    exact hi (by simp [hat,clip_of_nonpos h,clip_of_nonpos h'])
  have hhi : t/δ+N-i < 1 := by
    by_contra hn
    have h : 1 ≤ t/δ+N-i := le_of_not_gt hn
    have h' : 1 ≤ t/δ+N-i+1 := by linarith
    exact hi (by simp [hat,clip_of_one_le h,clip_of_one_le h'])
  have hcancel : t/δ*δ = t := div_mul_cancel₀ _ hδ.ne'
  rw [abs_lt]
  dsimp [center]
  constructor <;> nlinarith [mul_pos hδ (sub_pos.mpr hlo),mul_pos hδ (sub_pos.mpr hhi)]

theorem hat_support {N : ℕ} {δ t : ℝ} {i : Fin (2*N+1)} (hδ : 0 < δ)
    (hi : hat N δ i t ≠ 0) : |t| ≤ (N+1)*δ := by
  have hh := abs_lt.mp (hat_local hδ hi)
  have hi0 : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  have hiN : (i:ℝ) ≤ 2*N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have h1 := mul_nonneg hδ.le hi0
  have h2 := mul_nonneg hδ.le (sub_nonneg.mpr hiN)
  rw [abs_le]
  dsimp [center] at hh
  constructor <;> nlinarith

theorem hat_compactSupport {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (i : Fin (2*N+1)) :
    HasCompactSupport (hat N δ i) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(N+1)*δ) (b := (N+1)*δ))
  intro x hx
  by_contra hn
  have hh := abs_le.mp (hat_support hδ hn)
  exact hx ⟨by linarith [hh.1],hh.2⟩

end SmoothSelector
end SquareRootDegree

end

end OAI
