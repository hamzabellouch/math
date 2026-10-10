import OAI.Combinatorics.ProgressionColoring.AdaptiveMesh
import OAI.Combinatorics.ProgressionColoring.RationalGridMultiplicity
import Mathlib.Data.Int.Interval

namespace OAI

/-! Exact short-arc counts for a shifted rational grid.  The integer lift
below counts the actual points, including closed arc endpoints. -/

namespace QuantitativeVanDerWaerden

open Finset

theorem rho_eq_abs_centered_half_shift (x : ℝ) :
    rho x = |centered (x + 1 / 2)| := by
  let t := centered x
  have ht := centered_mem x
  have hx : x + 1 / 2 = (t + 1 / 2) + (⌊x + 1 / 2⌋ : ℤ) := by
    dsimp [t, centered]
    ring
  rw [hx, centered_add_int]
  change 1 / 2 - |t| = |centered (t + 1 / 2)|
  by_cases hneg : t < 0
  · rw [centered_eq_of_mem (by dsimp [t]; linarith [ht.1]) (by linarith),
      abs_of_neg hneg, abs_of_nonneg (by dsimp [t]; linarith [ht.1])]
    ring
  · have hnonneg : 0 ≤ t := le_of_not_gt hneg
    have he : t + 1 / 2 = (t - 1 / 2) + ((1 : ℤ) : ℝ) := by push_cast; ring
    rw [he, centered_add_int,
      centered_eq_of_mem (by linarith) (by dsimp [t]; linarith [ht.2]),
      abs_of_nonneg hnonneg, abs_of_nonpos (by dsimp [t]; linarith [ht.2])]
    ring

theorem integer_interval_card_le {lo hi : ℝ} (hlo : lo ≤ hi) :
    ((Icc ⌈lo⌉ ⌊hi⌋).card : ℝ) ≤ hi - lo + 1 := by
  have hi' := Int.lt_floor_add_one hi
  have hceil : ⌈lo⌉ ≤ ⌊hi⌋ + 1 := Int.ceil_le.mpr (by push_cast; linarith)
  have hc : ((Icc ⌈lo⌉ ⌊hi⌋).card : ℝ) =
      (⌊hi⌋ : ℝ) + 1 - (⌈lo⌉ : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le ⌈lo⌉ ⌊hi⌋ hceil
  rw [hc]
  linarith [Int.floor_le hi, Int.le_ceil lo]

noncomputable def rationalGridLift (s : ℕ) (y : ℝ) (j : Fin s) : ℤ :=
  (j.val : ℤ) - (s : ℤ) * ⌊y + (j.val : ℝ) / s + 1 / 2⌋

theorem rationalGridLift_identity {s : ℕ} (hs : 0 < s) (y : ℝ) (j : Fin s) :
    (s : ℝ) * centered (y + (j.val : ℝ) / s) =
      (s : ℝ) * y + rationalGridLift s y j := by
  have hsR : (s : ℝ) ≠ 0 := by positivity
  dsimp [rationalGridLift, centered]
  push_cast
  field_simp
  ring

theorem rationalGridLift_injective {s : ℕ} (hs : 0 < s) (y : ℝ) :
    Function.Injective (rationalGridLift s y) := by
  intro i j hij
  let n : ℤ := ⌊y + (i.val : ℝ) / s + 1 / 2⌋ -
    ⌊y + (j.val : ℝ) / s + 1 / 2⌋
  have hn : (i.val : ℝ) - j.val = (s : ℝ) * n := by
    have hR := congrArg (fun z : ℤ => (z : ℝ)) hij
    dsimp [rationalGridLift] at hR
    dsimp [n]
    push_cast at hR ⊢
    nlinarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hi : (i.val : ℝ) < s := by exact_mod_cast i.isLt
  have hj : (j.val : ℝ) < s := by exact_mod_cast j.isLt
  have hi0 : (0 : ℝ) ≤ i.val := by positivity
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  have hnsmall : |(n : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hnzero := integer_eq_zero_of_abs_lt_one hnsmall
  rw [hnzero, Int.cast_zero, mul_zero] at hn
  apply Fin.ext
  exact_mod_cast (sub_eq_zero.mp hn)

/-- An equally spaced shifted grid has at most `2*e*s+1` points in a
closed circle arc of radius `e`.  This remains true for large radii. -/
theorem uniform_grid_centered_count_le (s : ℕ) (hs : 0 < s) (y e : ℝ)
    (he : 0 ≤ e) :
    (((univ : Finset (Fin s)).filter
      (fun j => |centered (y + (j.val : ℝ) / s)| ≤ e)).card : ℝ) ≤
      2 * e * s + 1 := by
  classical
  let lo := (s : ℝ) * (-e - y)
  let hi := (s : ℝ) * (e - y)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlh : lo ≤ hi := by dsimp [lo, hi]; nlinarith
  have hcard : ((univ : Finset (Fin s)).filter
      (fun j => |centered (y + (j.val : ℝ) / s)| ≤ e)).card ≤
      (Icc ⌈lo⌉ ⌊hi⌋).card := by
    apply card_le_card_of_injOn (rationalGridLift s y)
    · intro j hj
      have hj' := abs_le.mp (mem_filter.mp hj).2
      have hrep := rationalGridLift_identity hs y j
      apply mem_Icc.mpr
      constructor
      · apply Int.ceil_le.mpr
        dsimp [lo]
        nlinarith [mul_nonneg hsR.le (sub_nonneg.mpr hj'.1)]
      · apply Int.le_floor.mpr
        dsimp [hi]
        nlinarith [mul_nonneg hsR.le (sub_nonneg.mpr hj'.2)]
    · exact (rationalGridLift_injective hs y).injOn
  have hcardR : (((univ : Finset (Fin s)).filter
      (fun j => |centered (y + (j.val : ℝ) / s)| ≤ e)).card : ℝ) ≤
      ((Icc ⌈lo⌉ ⌊hi⌋).card : ℝ) := by exact_mod_cast hcard
  have hbound := hcardR.trans (integer_interval_card_le hlh)
  dsimp [lo, hi] at hbound
  nlinarith

theorem uniform_grid_rho_count_le (s : ℕ) (hs : 0 < s) (y η : ℝ)
    (hη : 0 ≤ η) :
    (((univ : Finset (Fin s)).filter
      (fun j => rho (y + (j.val : ℝ) / s) ≤ 2 * η)).card : ℝ) ≤
      4 * η * s + 1 := by
  have h := uniform_grid_centered_count_le s hs (y + 1 / 2) (2 * η)
    (by positivity)
  have heq : (fun j : Fin s => rho (y + (j.val : ℝ) / s) ≤ 2 * η) =
      (fun j : Fin s => |centered (y + 1 / 2 + (j.val : ℝ) / s)| ≤ 2 * η) := by
    funext j
    rw [rho_eq_abs_centered_half_shift]
    congr 3
    ring
  have hf : (univ.filter (fun j : Fin s => rho (y + (j.val : ℝ) / s) ≤ 2 * η)) =
      (univ.filter (fun j : Fin s =>
        |centered (y + 1 / 2 + (j.val : ℝ) / s)| ≤ 2 * η)) := by
    apply filter_congr
    intro j _
    exact Iff.of_eq (congrFun heq j)
  rw [hf]
  nlinarith

theorem rational_grid_rho_closed_count_le (h a : ℕ) (hh : 0 < h) (y η : ℝ)
    (hη : 0 ≤ η) :
    (((univ : Finset (Fin h)).filter
      (fun z => rho (y + (z.val : ℝ) * a / h) ≤ 2 * η)).card : ℝ) ≤
      (h : ℝ) * (4 * η + 1 / (h / Nat.gcd h a : ℕ)) := by
  classical
  let d := Nat.gcd h a
  let s := h / d
  have hs : 0 < s := Nat.div_gcd_pos_of_pos_left a hh
  have hsR : (s : ℝ) ≠ 0 := by positivity
  have hperiod : ∀ x (n : ℤ), (rho (x + n) ≤ 2 * η) ↔ (rho x ≤ 2 * η) := by
    intro x n
    rw [rho_add_int]
  have hc := card_filter_rational_grid_periodic h a hh
    (fun x => rho x ≤ 2 * η) hperiod y
  have hcR : (((univ : Finset (Fin h)).filter
      (fun z => rho (y + (z.val : ℝ) * a / h) ≤ 2 * η)).card : ℝ) =
      (d : ℝ) * (((univ : Finset (Fin s)).filter
        (fun j => rho (y + (j.val : ℝ) / s) ≤ 2 * η)).card : ℝ) := by
    exact_mod_cast hc
  have hbound := uniform_grid_rho_count_le s hs y η hη
  have hf : (h : ℝ) = (d : ℝ) * s := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left h a)).symm
  change _ ≤ (h : ℝ) * (4 * η + 1 / (s : ℝ))
  calc
    _ = (d : ℝ) * (((univ : Finset (Fin s)).filter
        (fun j => rho (y + (j.val : ℝ) / s) ≤ 2 * η)).card : ℝ) := hcR
    _ ≤ (d : ℝ) * (4 * η * s + 1) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (h : ℝ) * (4 * η + 1 / (s : ℝ)) := by
      rw [hf]
      field_simp

/-- Strict cut-neighborhood version used for nonregular positions. -/
theorem rational_grid_rho_count_le (h a : ℕ) (hh : 0 < h) (y η : ℝ)
    (hη : 0 ≤ η) :
    (((univ : Finset (Fin h)).filter
      (fun z => rho (y + (z.val : ℝ) * a / h) < 2 * η)).card : ℝ) ≤
      (h : ℝ) * (4 * η + 1 / (h / Nat.gcd h a : ℕ)) := by
  classical
  have hsub : ((univ : Finset (Fin h)).filter
      (fun z => rho (y + (z.val : ℝ) * a / h) < 2 * η)) ⊆
      ((univ : Finset (Fin h)).filter
        (fun z => rho (y + (z.val : ℝ) * a / h) ≤ 2 * η)) := by
    intro z hz
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hz).2.le⟩
  have hcard : (((univ : Finset (Fin h)).filter
      (fun z => rho (y + (z.val : ℝ) * a / h) < 2 * η)).card : ℝ) ≤
      (((univ : Finset (Fin h)).filter
        (fun z => rho (y + (z.val : ℝ) * a / h) ≤ 2 * η)).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hcard.trans (rational_grid_rho_closed_count_le h a hh y η hη)

end QuantitativeVanDerWaerden

end OAI
