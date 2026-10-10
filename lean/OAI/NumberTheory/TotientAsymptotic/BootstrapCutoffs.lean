import OAI.NumberTheory.TotientAsymptotic.TwoCoordinateCount

namespace OAI

/-! Fixed cutoffs for the initial two-coordinate counting bootstrap. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def bootstrapTop (b : ℝ) : ℕ := ⌊b-Real.log (20*b)⌋₊-1

def bootstrapBottom (b : ℝ) : ℕ := ⌊b/100000000⌋₊

lemma eventually_bootstrap_log_budget (D : ℝ) : ∀ᶠ b : ℝ in atTop,
    10000*(Real.log (20*b)+|D|+Real.log (b+1)+10) ≤ b := by
  have hlog := Real.isLittleO_log_id_atTop.bound (show (0:ℝ)<1/40000 by norm_num)
  let E := Real.log 20+|D|+Real.log 2+10
  filter_upwards [hlog,eventually_ge_atTop (1:ℝ),eventually_ge_atTop (20000*E)] with b hb hb1 hbE
  have hb0 : 0 < b := by linarith
  have hl : Real.log b ≤ b/40000 := by
    have hh := (le_abs_self (Real.log b)).trans (by simpa only [Real.norm_eq_abs,abs_of_pos hb0,id_eq] using hb)
    linarith
  have hp : Real.log (b+1) ≤ Real.log 2+Real.log b := by
    have hh := Real.log_le_log (by linarith : 0 < b+1) (show b+1 ≤ 2*b by linarith)
    rwa [Real.log_mul (by norm_num : (2:ℝ)≠0) hb0.ne'] at hh
  rw [Real.log_mul (by norm_num : (20:ℝ)≠0) hb0.ne']
  dsimp [E] at hbE
  linarith

lemma bootstrap_cutoff_bounds {b : ℝ} (hb : 300000000 ≤ b)
    (hl : Real.log (20*b)+2 ≤ b/10000) :
    2 ≤ bootstrapBottom b ∧ bootstrapBottom b ≤ bootstrapTop b ∧
      (bootstrapBottom b:ℝ)+2 ≤ b/2 ∧ (bootstrapTop b:ℝ) ≤ b ∧
      b-Real.log (20*b)-2 ≤ bootstrapTop b ∧
      Real.exp (bootstrapTop b) ≤ Real.exp b/(20*b) := by
  have hb0 : 0 < b := by linarith
  have hlog0 : 0 ≤ Real.log (20*b) := Real.log_nonneg (by linarith)
  have ht : 2 ≤ b-Real.log (20*b) := by linarith
  have hfloor2 : 2 ≤ ⌊b-Real.log (20*b)⌋₊ := Nat.le_floor ht
  have hbot2 : 2 ≤ bootstrapBottom b := by
    apply Nat.le_floor
    linarith
  have hbotup : (bootstrapBottom b:ℝ) ≤ b/100000000 := Nat.floor_le (by positivity)
  have htopup : (bootstrapTop b:ℝ) ≤ b-Real.log (20*b) := by
    have hs : bootstrapTop b ≤ ⌊b-Real.log (20*b)⌋₊ := Nat.sub_le _ _
    exact (Nat.cast_le.mpr hs).trans (Nat.floor_le (by linarith))
  have htoplow : b-Real.log (20*b)-2 ≤ bootstrapTop b := by
    dsimp [bootstrapTop]
    rw [Nat.cast_sub (by omega : 1 ≤ ⌊b-Real.log (20*b)⌋₊),Nat.cast_one]
    linarith [Nat.sub_one_lt_floor (b-Real.log (20*b))]
  refine ⟨hbot2,?_,by linarith,by linarith,htoplow,?_⟩
  · exact_mod_cast (show (bootstrapBottom b:ℝ) ≤ bootstrapTop b by linarith)
  · calc
      _ ≤ Real.exp (b-Real.log (20*b)) := Real.exp_le_exp.mpr htopup
      _ = _ := by rw [Real.exp_sub,Real.exp_log (by positivity : 0 < 20*b)]

end TotientAsymptotic

end

end OAI
