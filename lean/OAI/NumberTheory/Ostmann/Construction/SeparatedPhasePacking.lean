import Mathlib.Data.Fintype.Prod
import OAI.NumberTheory.Ostmann.Preliminaries.PhaseDistance

namespace OAI

/-! # A finite reciprocal-distance bound for separated centered phases -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def centeredPhaseBin (r : ℕ) (x : ℝ) : Bool × ℕ :=
  (decide (x < 0), ⌊2 * (r : ℝ) * |x|⌋₊)

private theorem same_sign_abs_difference (x y : ℝ)
    (hs : decide (x < 0) = decide (y < 0)) :
    |(|x| - |y|)| = |x - y| := by
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  · rw [abs_of_neg hx, abs_of_neg hy]
    have heq : -x - -y = -(x - y) := by ring
    rw [heq, abs_neg]
  · simp [hx, hy] at hs
  · simp [hx, hy] at hs
  · rw [abs_of_nonneg (le_of_not_gt hx), abs_of_nonneg (le_of_not_gt hy)]

theorem centeredPhaseBin_injective {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (r : ℕ) (hr : 0 < r)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 / (2 * (r : ℝ)) ≤ |f i - f j|) :
    Set.InjOn (fun i => centeredPhaseBin r (f i)) S := by
  intro i hi j hj heq
  by_contra hij
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hs := congrArg Prod.fst heq
  have hb := congrArg Prod.snd heq
  have hfi : (⌊2 * (r : ℝ) * |f i|⌋₊ : ℝ) ≤ 2 * (r : ℝ) * |f i| :=
    Nat.floor_le (by positivity)
  have hfj : (⌊2 * (r : ℝ) * |f j|⌋₊ : ℝ) ≤ 2 * (r : ℝ) * |f j| :=
    Nat.floor_le (by positivity)
  have hfi' := Nat.lt_floor_add_one (2 * (r : ℝ) * |f i|)
  have hfj' := Nat.lt_floor_add_one (2 * (r : ℝ) * |f j|)
  change ⌊2 * (r : ℝ) * |f i|⌋₊ = ⌊2 * (r : ℝ) * |f j|⌋₊ at hb
  rw [hb] at hfi hfi'
  have hclose : |(2 * (r : ℝ) * |f i|) - (2 * (r : ℝ) * |f j|)| < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith
  rw [← mul_sub, abs_mul, abs_of_pos (show 0 < 2 * (r : ℝ) by positivity),
    same_sign_abs_difference (f i) (f j) hs] at hclose
  have hfar := (div_le_iff₀ (show 0 < 2 * (r : ℝ) by positivity)).mp (hsep i hi j hj hij)
  nlinarith

/-- Each signed distance bin contains at most one point. The zero bin costs
N; all other bins cost r/k. This is the finite harmonic estimate needed for
one rational-approximation block. -/
theorem separated_phase_weight_sum {ι : Type*} (S : Finset ι) (f w : ι → ℝ)
    (r : ℕ) (N : ℝ) (hr : 0 < r) (hN : 0 ≤ N)
    (hsize : ∀ i ∈ S, |f i| ≤ 1 / 2)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 / (2 * (r : ℝ)) ≤ |f i - f j|)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hupper : ∀ i ∈ S, w i ≤ N)
    (hdist : ∀ i ∈ S, 2 * |f i| * w i ≤ 1) :
    ∑ i ∈ S, w i ≤
      2 * ∑ k ∈ Finset.range (r + 1), if k = 0 then N else (r : ℝ) / k := by
  let bin := fun i => centeredPhaseBin r (f i)
  let B := fun k : ℕ => if k = 0 then N else (r : ℝ) / k
  have hB : ∀ k, 0 ≤ B k := by
    intro k
    dsimp [B]
    split_ifs <;> positivity
  have hinj : Set.InjOn bin S := centeredPhaseBin_injective S f r hr hsep
  have hmem : ∀ i ∈ S, bin i ∈ (Finset.univ : Finset Bool).product (Finset.range (r + 1)) := by
    intro i hi
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_range.mpr ?_⟩
    have hfloor : (⌊2 * (r : ℝ) * |f i|⌋₊ : ℝ) ≤ 2 * (r : ℝ) * |f i| :=
      Nat.floor_le (by positivity)
    have hb : (⌊2 * (r : ℝ) * |f i|⌋₊ : ℝ) ≤ r := by
      have hh := hsize i hi
      nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
    have hk : ⌊2 * (r : ℝ) * |f i|⌋₊ ≤ r := by exact_mod_cast hb
    exact Nat.lt_succ_of_le hk
  have hpoint : ∀ i ∈ S, w i ≤ B (bin i).2 := by
    intro i hi
    let k := (bin i).2
    change w i ≤ if k = 0 then N else (r : ℝ) / k
    by_cases hk : k = 0
    · simpa only [hk, ite_true] using hupper i hi
    · rw [ite_eq_right hk]
      have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      apply (le_div_iff₀ hkpos).mpr
      have hfloor : (k : ℝ) ≤ 2 * (r : ℝ) * |f i| := Nat.floor_le (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hfloor (hw i hi)
      have hbound := mul_le_mul_of_nonneg_left (hdist i hi) (Nat.cast_nonneg r)
      nlinarith
  calc
    _ ≤ ∑ i ∈ S, B (bin i).2 := Finset.sum_le_sum hpoint
    _ = ∑ b ∈ S.image bin, B b.2 := (Finset.sum_image (f := fun b : Bool × ℕ => B b.2) hinj).symm
    _ ≤ ∑ b ∈ (Finset.univ : Finset Bool).product (Finset.range (r + 1)), B b.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        exact hmem i hi
      · intro b _ _
        exact hB b.2
    _ = _ := by rw [Finset.product_eq_sprod, Finset.sum_product]; simp [B, two_mul]

end Ostmann

end OAI
