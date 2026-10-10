import OAI.Analysis.Cotype.GroupedPolynomial
import OAI.Analysis.Cotype.CoefficientTarget
import Mathlib.Data.Nat.Choose.Bounds

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

theorem cutoff_power_bound {m : ℕ} (hd : 4 ≤ degreeCutoff m)
    (hm : degreeCutoff m < m) : (m : ℝ) ≤ (2 : ℝ) ^ (degreeCutoff m - 2) := by
  have hc : 2 * Real.logb 2 (m : ℝ) ≤ (degreeCutoff m : ℝ) := Nat.le_ceil _
  have hsub : ((degreeCutoff m - 2 : ℕ) : ℝ) = (degreeCutoff m : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hl : Real.logb 2 (m : ℝ) ≤ ((degreeCutoff m - 2 : ℕ) : ℝ) := by
    rw [hsub]
    have hd' : (4 : ℝ) ≤ degreeCutoff m := by exact_mod_cast hd
    linarith
  have hp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  simpa only [Real.rpow_natCast] using
    (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hp).mp hl

theorem deleted_coefficient_majorant {m d k l : ℕ} (hd : 4 ≤ d)
    (hm : (m : ℝ) ≤ (2 : ℝ) ^ (d-2)) (hk : d < k) (hl : d < l) :
    Real.sqrt ((m.choose k : ℝ) * (m.choose l : ℝ)) * (1/2 : ℝ)^(k*l) ≤
      (1/2 : ℝ)^k * (1/2 : ℝ)^l := by
  have hkl : k+l ≤ k*l := by nlinarith
  have hexp : (d-2)*(k+l) ≤ 2*(k*l-k-l) := by
    have hd2 : d-2+2=d := by omega
    have hsub : k*l-k-l+(k+l)=k*l := by omega
    have h1 := Nat.mul_le_mul_right l (show d ≤ k by omega)
    have h2 := Nat.mul_le_mul_right k (show d ≤ l by omega)
    nlinarith
  have hchoose (i : ℕ) : (m.choose i : ℝ) ≤ (m : ℝ)^i := by
    exact_mod_cast Nat.choose_le_pow m i
  have hsq : (m.choose k : ℝ) * (m.choose l : ℝ) ≤ ((2 : ℝ)^(k*l-k-l))^2 := by
    calc
      _ ≤ (m : ℝ)^k * (m : ℝ)^l := mul_le_mul (hchoose k) (hchoose l)
        (Nat.cast_nonneg _) (by positivity)
      _ = (m : ℝ)^(k+l) := (pow_add _ _ _).symm
      _ ≤ ((2 : ℝ)^(d-2))^(k+l) := pow_le_pow_left₀ (Nat.cast_nonneg _) hm _
      _ = (2 : ℝ)^((d-2)*(k+l)) := (pow_mul _ _ _).symm
      _ ≤ (2 : ℝ)^(2*(k*l-k-l)) := pow_le_pow_right₀ (by norm_num) hexp
      _ = ((2 : ℝ)^(k*l-k-l))^2 := by rw [mul_comm 2, pow_mul]
  have hsqrt : Real.sqrt ((m.choose k : ℝ) * (m.choose l : ℝ)) ≤ (2 : ℝ)^(k*l-k-l) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
  calc
    _ ≤ (2 : ℝ)^(k*l-k-l) * (1/2 : ℝ)^(k*l) :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ = (1/2 : ℝ)^k * (1/2 : ℝ)^l := by
      have he : k*l = (k*l-k-l)+(k+l) := by omega
      nth_rw 2 [he]
      rw [pow_add, ← mul_assoc]
      have hi : (2 : ℝ)^(k*l-k-l) * (1/2 : ℝ)^(k*l-k-l) = 1 := by
        rw [← mul_pow]; norm_num
      rw [hi, one_mul, pow_add]

theorem positive_half_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), if 0 < k then (1/2 : ℝ)^k else 0) =
      1 - (1/2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.succ_pos, ite_true, pow_succ]
    ring

variable {m : ℕ}

def deletedTail (f : SignMatrix m → ℝ) (d : ℕ) (s u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
    if d < k ∧ d < l then Ckl f k l * s^k * u^l * (1/2 : ℝ)^(k*l) else 0

def truncatedGrouped (f : SignMatrix m → ℝ) (d : ℕ) (s u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
    if k ≤ d ∨ l ≤ d then Ckl f k l * s^k * u^l * (1/2 : ℝ)^(k*l) else 0

theorem grouped_sub_truncated (f : SignMatrix m → ℝ) (d : ℕ) (s u : ℝ) :
    groupedPolynomial f s u (1/2) - truncatedGrouped f d s u = deletedTail f d s u := by
  simp only [groupedPolynomial, Fintype.card_fin, truncatedGrouped, deletedTail,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hk : k ≤ d <;> by_cases hl : l ≤ d <;> simp [hk, hl]

theorem deletedTail_bound {f : SignMatrix m → ℝ} {M s u : ℝ} {d : ℕ}
    (hM : 0 ≤ M) (hf : ∀ S, |f S| ≤ M) (hd : 4 ≤ d)
    (hm : (m : ℝ) ≤ (2 : ℝ)^(d-2)) (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    |deletedTail f d s u| ≤ M := by
  let w := fun k : ℕ => if 0 < k then (1/2 : ℝ)^k else 0
  have hw : ∀ k, 0 ≤ w k := by intro k; dsimp [w]; split_ifs <;> positivity
  have hterm (k l : ℕ) :
      |if d < k ∧ d < l then Ckl f k l * s^k * u^l * (1/2 : ℝ)^(k*l) else 0| ≤
        M * w k * w l := by
    split_ifs with h
    · obtain ⟨hk, hl⟩ := h
      have hs' : |s|^k ≤ 1 := pow_le_one₀ (abs_nonneg _) hs
      have hu' : |u|^l ≤ 1 := pow_le_one₀ (abs_nonneg _) hu
      have hc := Ckl_bound hM hf k l
      simp only [Fintype.card_fin] at hc
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (1/2:ℝ)^(k*l))]
      dsimp [w]
      rw [ite_eq_left (by omega : 0 < k), ite_eq_left (by omega : 0 < l)]
      calc
        _ ≤ (M * Real.sqrt ((m.choose k : ℝ) * (m.choose l : ℝ))) * 1 * 1 *
            (1/2 : ℝ)^(k*l) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul hc hs' (by positivity) (by positivity)) hu'
              (by positivity) (by positivity)) (by positivity)
        _ = M * (Real.sqrt ((m.choose k : ℝ) * (m.choose l : ℝ)) *
            (1/2 : ℝ)^(k*l)) := by ring
        _ ≤ M * ((1/2 : ℝ)^k * (1/2 : ℝ)^l) :=
          mul_le_mul_of_nonneg_left (deleted_coefficient_majorant hd hm hk hl) hM
        _ = _ := by ring
    · simp only [abs_zero]
      exact mul_nonneg (mul_nonneg hM (hw k)) (hw l)
  have hwle : (∑ k ∈ Finset.range (m+1), w k) ≤ 1 := by
    dsimp [w]; rw [positive_half_sum]; linarith [show (0:ℝ) ≤ (1/2:ℝ)^m by positivity]
  have hwn : 0 ≤ ∑ k ∈ Finset.range (m+1), w k := Finset.sum_nonneg (fun k _ => hw k)
  calc
    _ ≤ ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
        |if d < k ∧ d < l then Ckl f k l * s^k * u^l * (1/2 : ℝ)^(k*l) else 0| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1), M * w k * w l :=
      Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hterm k l))
    _ = M * (∑ k ∈ Finset.range (m+1), w k) * (∑ l ∈ Finset.range (m+1), w l) := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ M * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hwle hM) hwle hwn (by positivity)
    _ = M := by ring

theorem truncatedGrouped_bound {f : SignMatrix m → ℝ} {M s u : ℝ}
    (ho : IsOdd f) (hr : RankOneSupported f) (hM : 0 ≤ M)
    (hf : ∀ S, |f S| ≤ M) (hd : 4 ≤ degreeCutoff m) (hm : degreeCutoff m < m)
    (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    |truncatedGrouped f (degreeCutoff m) s u| ≤ 2*M := by
  have he := grouped_sub_truncated f (degreeCutoff m) s u
  have hh := groupedPolynomial_bound ho hr hf hs hu
  have ht := deletedTail_bound hM hf hd (cutoff_power_bound hd hm) hs hu
  rw [show truncatedGrouped f (degreeCutoff m) s u =
    groupedPolynomial f s u (1/2) - deletedTail f (degreeCutoff m) s u by linarith]
  exact (abs_sub _ _).trans (by linarith)

end Cotype

end

end OAI
