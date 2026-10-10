import OAI.MeasureTheory.Falconer.Recursion.ProfileEndpointStability
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

/-! Inward rounding of profile intervals to a fixed finite scale grid. -/
namespace Falconer

noncomputable def profileGridLeft (n : ℕ) (a : ℝ) : ℝ := (⌈(n : ℝ)*a⌉ : ℝ)/(n : ℝ)
noncomputable def profileGridRight (n : ℕ) (b : ℝ) : ℝ := (⌊(n : ℝ)*b⌋ : ℝ)/(n : ℝ)

theorem profileGridLeft_bounds {n : ℕ} (hn : 0 < n) (a : ℝ) :
    a ≤ profileGridLeft n a ∧ profileGridLeft n a ≤ a+1/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · apply (le_div_iff₀ hnR).2
    simpa only [mul_comm] using Int.le_ceil ((n : ℝ)*a)
  · apply (div_le_iff₀ hnR).2
    have hb := (Int.ceil_lt_add_one ((n : ℝ)*a)).le
    have he : (a+1/(n : ℝ))*(n : ℝ) = (n : ℝ)*a+1 := by field_simp
    rw [he]
    exact hb

theorem profileGridRight_bounds {n : ℕ} (hn : 0 < n) (b : ℝ) :
    b-1/(n : ℝ) ≤ profileGridRight n b ∧ profileGridRight n b ≤ b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · apply (le_div_iff₀ hnR).2
    have hb := (Int.lt_floor_add_one ((n : ℝ)*b)).le
    have he : (b-1/(n : ℝ))*(n : ℝ) = (n : ℝ)*b-1 := by field_simp
    rw [he]
    linarith
  · apply (div_le_iff₀ hnR).2
    simpa only [mul_comm] using Int.floor_le ((n : ℝ)*b)

theorem profileGrid_interval_bounds {n : ℕ} (hn : 0 < n) (a h : ℝ) :
    profileGridRight n (a+h)-profileGridLeft n a ≤ h ∧
    h-2/(n : ℝ) ≤ profileGridRight n (a+h)-profileGridLeft n a ∧
    |profileGridLeft n a-a| ≤ 1/(n : ℝ) ∧
    |profileGridRight n (a+h)-(a+h)| ≤ 1/(n : ℝ) := by
  have hl := profileGridLeft_bounds hn a
  have hr := profileGridRight_bounds hn (a+h)
  have he : 2/(n : ℝ) = 2*(1/(n : ℝ)) := by ring
  refine ⟨by linarith,by rw [he]; linarith,?_,?_⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hl.1)]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hr.2)]
    linarith

end Falconer

end OAI
