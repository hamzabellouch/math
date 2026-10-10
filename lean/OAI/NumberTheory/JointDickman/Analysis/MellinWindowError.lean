import OAI.NumberTheory.JointDickman.Analysis.MellinWindowSupport
import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicBoundaryWidths

namespace OAI

/-! # Uniform error of smoothing a hard logarithmic window -/
namespace JointDickman
open Finset

/-- Only integers in the two transition strips can see a nonconstant profile. -/
lemma logarithmicWindowProfile_bad_card {η δ x : ℝ}
    (hη : 0 < η) (hηhalf : η < 1/2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : 0 < x) :
    (((Ioc ⌊x⌋₊ ⌊x * Real.exp δ⌋₊).filter fun n : ℕ =>
      logarithmicWindowProfile η hη hηhalf
        ((Real.log x + δ - Real.log (n : ℝ)) / δ) ≠ 1).card : ℝ) ≤
          8 * η * δ * x + 2 := by
  let W := Ioc ⌊x⌋₊ ⌊x * Real.exp δ⌋₊
  let B := W.filter fun n : ℕ => logarithmicWindowProfile η hη hηhalf
    ((Real.log x + δ - Real.log (n : ℝ)) / δ) ≠ 1
  let L := Ioc ⌊x⌋₊ ⌊x * Real.exp (η * δ)⌋₊
  let U := Ioc ⌊x * Real.exp ((1 - η) * δ)⌋₊ ⌊x * Real.exp δ⌋₊
  have hsub : B ⊆ L ∪ U := by
    intro n hn
    obtain ⟨hnW, hnB⟩ := mem_filter.mp hn
    obtain ⟨hnlo, hnhi⟩ := mem_Ioc.mp hnW
    have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnlo
    have hn0 : 0 < (n : ℝ) := hx.trans hxn
    by_cases hlo : (n : ℝ) ≤ x * Real.exp (η * δ)
    · exact mem_union_left U (mem_Ioc.mpr ⟨hnlo, Nat.le_floor hlo⟩)
    · by_cases hhi : x * Real.exp ((1 - η) * δ) < (n : ℝ)
      · exact mem_union_right L (mem_Ioc.mpr
          ⟨(Nat.floor_lt (mul_nonneg hx.le (Real.exp_pos _).le)).mpr hhi, hnhi⟩)
      · exact False.elim (hnB (logarithmicWindowProfile_one_of_inside
          hη hηhalf hδ hx hn0 (le_of_not_ge hlo) (le_of_not_gt hhi)))
  have hcard : (B.card : ℝ) ≤ (L.card : ℝ) + (U.card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le L U)
  exact hcard.trans (logarithmic_boundary_card hx.le hη.le (by linarith) hδ.le hδ1)

/-- The hard window differs from the smooth Mellin packet by an arbitrarily
small fixed profile error and the explicit integer endpoint error. -/
theorem logarithmicWindowAverage_mellinPacket_error (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {K N : ℕ} {η δ x : ℝ}
    (hη : 0 < η) (hηhalf : η < 1/2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : 0 < x)
    (hK : K ≤ ⌊x⌋₊) (hN : ⌊x * Real.exp δ⌋₊ ≤ N) :
    ‖logarithmicWindowAverage f δ (Real.log x) -
      mellinPacket (Ioc K N) f
        (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
        (Real.log x + δ)‖ ≤ 16 * η + 4 / (δ * x) := by
  let W := Ioc ⌊x⌋₊ ⌊x * Real.exp δ⌋₊
  let w := fun n : ℕ => logarithmicWindowProfile η hη hηhalf
    ((Real.log x + δ - Real.log (n : ℝ)) / δ)
  let B := W.filter fun n : ℕ => w n ≠ 1
  have hsum : (∑ n ∈ W, (f n / (n : ℂ) - (f n / (n : ℂ)) * w n)) =
      ∑ n ∈ B, (f n / (n : ℂ) - (f n / (n : ℂ)) * w n) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro n hn hnB
    have hw : w n = 1 := by
      by_contra h
      exact hnB (mem_filter.mpr ⟨hn, h⟩)
    rw [hw, mul_one, sub_self]
  have hterm (n : ℕ) (hn : n ∈ B) :
      ‖f n / (n : ℂ) - (f n / (n : ℂ)) * w n‖ ≤ 2 / x := by
    have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt (mem_Ioc.mp (mem_filter.mp hn).1).1
    have hn0 : 0 < (n : ℝ) := hx.trans hxn
    have hrecip : ‖f n / (n : ℂ)‖ ≤ 1 / x := by
      rw [norm_div, Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right (hf n) hn0.le).trans
        (one_div_le_one_div_of_le hx hxn.le)
    have hw : ‖w n‖ ≤ 1 := logarithmicWindowProfile_norm_le _ _ _ _
    calc
      _ ≤ ‖f n / (n : ℂ)‖ + ‖(f n / (n : ℂ)) * w n‖ := norm_sub_le _ _
      _ ≤ 1 / x + (1 / x) * 1 := by
        rw [norm_mul]
        exact add_le_add hrecip (mul_le_mul hrecip hw (norm_nonneg _) (by positivity))
      _ = 2 / x := by ring
  have hnorm : ‖∑ n ∈ W, (f n / (n : ℂ) - (f n / (n : ℂ)) * w n)‖ ≤
      (B.card : ℝ) * (2 / x) := by
    rw [hsum]
    exact (norm_sum_le _ _).trans ((sum_le_sum hterm).trans_eq (by simp))
  have hcard : (B.card : ℝ) ≤ 8 * η * δ * x + 2 :=
    logarithmicWindowProfile_bad_card hη hηhalf hδ hδ1 hx
  rw [mellinPacket_logarithmicWindow_support f hη hηhalf hδ hx hK hN]
  unfold logarithmicWindowAverage
  rw [Real.exp_add, Real.exp_log hx, ← sub_div, ← sum_sub_distrib,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  calc
    _ ≤ ((B.card : ℝ) * (2 / x)) / δ := div_le_div_of_nonneg_right hnorm hδ.le
    _ ≤ ((8 * η * δ * x + 2) * (2 / x)) / δ := by gcongr
    _ = 16 * η + 4 / (δ * x) := by field_simp; ring

end JointDickman

end OAI
