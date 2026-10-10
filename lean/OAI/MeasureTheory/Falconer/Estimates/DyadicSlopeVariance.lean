import OAI.MeasureTheory.Falconer.Estimates.DyadicSlopeEnergy

namespace OAI

/-! Exact variance and selection of a small energy increment for dyadic slopes. -/
namespace Falconer
open scoped BigOperators

noncomputable def dyadicSlopeVariance (f : ℝ → ℝ) (a h c : ℝ) : ℕ → ℝ
  | 0 => (intervalSecantSlope f a h-c)^2
  | n+1 => (dyadicSlopeVariance f a (h/2) c n + dyadicSlopeVariance f (a+h/2) (h/2) c n)/2

theorem dyadicSlopeVariance_nonneg (f : ℝ → ℝ) (a h c : ℝ) (n : ℕ) :
    0 ≤ dyadicSlopeVariance f a h c n := by
  induction n generalizing a h with
  | zero => exact sq_nonneg _
  | succ n ih => exact div_nonneg (add_nonneg (ih _ _) (ih _ _)) (by norm_num)

theorem dyadicSlopeVariance_eq (f : ℝ → ℝ) (a c : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    dyadicSlopeVariance f a h c n =
      dyadicSlopeEnergy f a h n-2*c*intervalSecantSlope f a h+c^2 := by
  induction n generalizing a h with
  | zero => dsimp [dyadicSlopeVariance,dyadicSlopeEnergy]; ring
  | succ n ih =>
    rw [dyadicSlopeVariance,ih a (half_pos hh),ih (a+h/2) (half_pos hh)]
    have he := intervalSecantSlope_children f a hh.ne'
    change (_+_)/2 = (_+_)/2-2*c*intervalSecantSlope f a h+c^2
    calc
      _ = (dyadicSlopeEnergy f a (h/2) n+dyadicSlopeEnergy f (a+h/2) (h/2) n)/2 -
          c*(intervalSecantSlope f a (h/2)+intervalSecantSlope f (a+h/2) (h/2))+c^2 := by ring
      _ = _ := by rw [he]; ring

theorem dyadicSlopeVariance_centered (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    dyadicSlopeVariance f a h (intervalSecantSlope f a h) n =
      dyadicSlopeEnergy f a h n-dyadicSlopeEnergy f a h 0 := by
  rw [dyadicSlopeVariance_eq f a _ hh n]
  dsimp [dyadicSlopeEnergy]
  ring

theorem dyadicSlopeEnergy_block_telescoping (f : ℝ → ℝ) (a h : ℝ) (m L : ℕ) :
    (∑ j ∈ Finset.range L, (dyadicSlopeEnergy f a h ((j+1)*m)-dyadicSlopeEnergy f a h (j*m))) =
      dyadicSlopeEnergy f a h (L*m)-dyadicSlopeEnergy f a h 0 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ,ih]; ring

theorem exists_small_dyadic_energy_increment {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h : ℝ} (hh : 0 < h) (m L : ℕ) (hL : 0 < L) :
    ∃ j < L, dyadicSlopeEnergy f a h ((j+1)*m)-dyadicSlopeEnergy f a h (j*m) ≤ 4/(L : ℝ) := by
  by_contra he
  push Not at he
  have hs := Finset.sum_lt_sum_of_nonempty
    (show (Finset.range L).Nonempty from ⟨0,Finset.mem_range.mpr hL⟩)
    (fun j hj => he j (Finset.mem_range.mp hj))
  rw [dyadicSlopeEnergy_block_telescoping] at hs
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have heq : (∑ _j ∈ Finset.range L, (4/(L : ℝ))) = 4 := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    exact mul_div_cancel₀ 4 hLR.ne'
  rw [heq] at hs
  linarith [dyadicSlopeEnergy_le_four hf a hh (L*m),dyadicSlopeEnergy_nonneg f a h 0]

theorem dyadicSlopeVariance_recenter (f : ℝ → ℝ) (a c : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    dyadicSlopeVariance f a h c n =
      dyadicSlopeVariance f a h (intervalSecantSlope f a h) n+(intervalSecantSlope f a h-c)^2 := by
  rw [dyadicSlopeVariance_eq f a c hh n,dyadicSlopeVariance_eq f a _ hh n]
  ring

theorem dyadicSlopeVariance_child_le (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    (dyadicSlopeVariance f a (h/2) (intervalSecantSlope f a (h/2)) n+
      (intervalSecantSlope f a (h/2)-intervalSecantSlope f a h)^2)/2 ≤
        dyadicSlopeVariance f a h (intervalSecantSlope f a h) (n+1) ∧
    (dyadicSlopeVariance f (a+h/2) (h/2) (intervalSecantSlope f (a+h/2) (h/2)) n+
      (intervalSecantSlope f (a+h/2) (h/2)-intervalSecantSlope f a h)^2)/2 ≤
        dyadicSlopeVariance f a h (intervalSecantSlope f a h) (n+1) := by
  rw [dyadicSlopeVariance]
  have hl := dyadicSlopeVariance_recenter f a (intervalSecantSlope f a h) (half_pos hh) n
  have hr := dyadicSlopeVariance_recenter f (a+h/2) (intervalSecantSlope f a h) (half_pos hh) n
  rw [hl,hr]
  constructor <;> nlinarith [dyadicSlopeVariance_nonneg f a (h/2) (intervalSecantSlope f a (h/2)) n,
    dyadicSlopeVariance_nonneg f (a+h/2) (h/2) (intervalSecantSlope f (a+h/2) (h/2)) n,
    sq_nonneg (intervalSecantSlope f a (h/2)-intervalSecantSlope f a h),
    sq_nonneg (intervalSecantSlope f (a+h/2) (h/2)-intervalSecantSlope f a h)]

end Falconer

end OAI
