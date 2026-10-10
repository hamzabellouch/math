import OAI.Combinatorics.Crossing.AxisGenericPositions

namespace OAI

noncomputable section
namespace Zarankiewicz

def axisIntervalLo (r : ℕ) (i : Fin r) : ℝ := if i.val < r/2 then 2*(i.val : ℝ)+1 else -(2*(i.val : ℝ)+2)
def axisIntervalHi (r : ℕ) (i : Fin r) : ℝ := if i.val < r/2 then 2*(i.val : ℝ)+2 else -(2*(i.val : ℝ)+1)

theorem axisInterval_nonempty (r : ℕ) (i : Fin r) : axisIntervalLo r i < axisIntervalHi r i := by
  unfold axisIntervalLo axisIntervalHi
  split_ifs <;> linarith

theorem axisInterval_abs_bounds (r : ℕ) (i : Fin r) (x : ℝ)
    (hx : x ∈ Set.Ioo (axisIntervalLo r i) (axisIntervalHi r i)) :
    2*(i.val : ℝ)+1 < |x| ∧ |x| < 2*(i.val : ℝ)+2 := by
  have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  by_cases h : i.val < r/2
  · simp only [axisIntervalLo,axisIntervalHi,ite_eq_left h,Set.mem_Ioo] at hx
    rw [abs_of_pos (by linarith [hx.1])]
    exact hx
  · simp only [axisIntervalLo,axisIntervalHi,ite_eq_right h,Set.mem_Ioo] at hx
    rw [abs_of_neg (by linarith [hx.2])]
    constructor <;> linarith [hx.1,hx.2]

theorem axisInterval_sign (r : ℕ) (i : Fin r) (x : ℝ)
    (hx : x ∈ Set.Ioo (axisIntervalLo r i) (axisIntervalHi r i)) :
    (0 < x ↔ i.val < r/2) ∧ (x < 0 ↔ r/2 ≤ i.val) := by
  have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  by_cases h : i.val < r/2
  · simp only [axisIntervalLo,axisIntervalHi,ite_eq_left h,Set.mem_Ioo] at hx
    have hp : 0 < x := by linarith [hx.1]
    simp [hp,h,not_lt_of_ge hp.le,Nat.not_le.mpr h]
  · simp only [axisIntervalLo,axisIntervalHi,ite_eq_right h,Set.mem_Ioo] at hx
    have hn : x < 0 := by linarith [hx.2]
    simp [hn,h,not_lt_of_ge hn.le,Nat.le_of_not_gt h]

theorem axisInterval_ne_zero (r : ℕ) (i : Fin r) (x : ℝ)
    (hx : x ∈ Set.Ioo (axisIntervalLo r i) (axisIntervalHi r i)) : x ≠ 0 := by
  have hh := (axisInterval_abs_bounds r i x hx).1
  intro he
  rw [he,abs_zero] at hh
  have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  linarith

theorem axisInterval_abs_strictMono (r : ℕ) (x : Fin r → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (axisIntervalLo r i) (axisIntervalHi r i)) :
    StrictMono (fun i => |x i|) := by
  intro i k hik
  have hi := (axisInterval_abs_bounds r i (x i) (hx i)).2
  have hk := (axisInterval_abs_bounds r k (x k) (hx k)).1
  have hik' : (i.val : ℝ)+1 ≤ (k.val : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hik)
  linarith

theorem axisInterval_injective (r : ℕ) (x : Fin r → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (axisIntervalLo r i) (axisIntervalHi r i)) : Function.Injective x := by
  intro i k hik
  exact (axisInterval_abs_strictMono r x hx).injective (congrArg abs hik)

end Zarankiewicz

end

end OAI
