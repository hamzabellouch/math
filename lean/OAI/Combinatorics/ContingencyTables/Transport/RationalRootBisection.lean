import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace OAI

/-! # Fixed-depth rational bisection for the correction power of two -/

namespace ContingencyTables.RationalRootBisection

noncomputable section

/-- Every branch compares exact rational powers. The loop count is the
explicit depth, independent of the comparison outcomes. -/
def interval (c : ℚ) (s : ℕ) : ℕ → ℚ × ℚ
  | 0 => (0,8)
  | n+1 =>
    let ab := interval c s n
    let m := (ab.1+ab.2)/2
    if m^s ≤ c then (m,ab.2) else (ab.1,m)

def midpoint (c : ℚ) (s n : ℕ) : ℚ :=
  ((interval c s n).1+(interval c s n).2)/2

/-- The target is used only in correctness, never by the algorithm. -/
theorem interval_contains (c : ℚ) (s : ℕ) (hs : 0 < s) (t : ℝ)
    (ht : 0 ≤ t) (ht8 : t ≤ 8) (hroot : t^s=(c:ℝ)) (n : ℕ) :
    0 ≤ ((interval c s n).1:ℝ) ∧ ((interval c s n).1:ℝ) ≤ t ∧
      t ≤ ((interval c s n).2:ℝ) ∧ ((interval c s n).2:ℝ) ≤ 8 := by
  induction n with
  | zero => simpa only [interval,Rat.cast_zero,Rat.cast_ofNat] using ⟨le_refl 0,ht,ht8,le_refl 8⟩
  | succ n ih =>
    let ab := interval c s n
    let m : ℚ := (ab.1+ab.2)/2
    have hm0 : (0:ℝ) ≤ m := by
      dsimp only [m]
      push_cast
      change 0 ≤ (((interval c s n).1:ℝ)+((interval c s n).2:ℝ))/2
      linarith [ih.1,ih.2.1,ih.2.2.1]
    have hml : ((ab.1:ℚ):ℝ) ≤ m := by
      dsimp only [m,ab]
      push_cast
      linarith [ih.2.1,ih.2.2.1]
    have hmu : (m:ℝ) ≤ ab.2 := by
      dsimp only [m,ab]
      push_cast
      linarith [ih.2.1,ih.2.2.1]
    change 0 ≤ ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).1:ℝ) ∧
      ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).1:ℝ) ≤ t ∧
      t ≤ ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).2:ℝ) ∧
      ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).2:ℝ) ≤ 8
    by_cases h : m^s ≤ c
    · simp only [h,ite_true]
      have hp : (m:ℝ)^s ≤ t^s := by rw [hroot]; exact_mod_cast h
      exact ⟨hm0,le_of_pow_le_pow_left₀ hs.ne' ht hp,ih.2.2.1,ih.2.2.2⟩
    · simp only [h,ite_false]
      have hp : t^s < (m:ℝ)^s := by rw [hroot]; exact_mod_cast (lt_of_not_ge h)
      exact ⟨ih.1,ih.2.1,(lt_of_pow_lt_pow_left₀ s hm0 hp).le,hmu.trans ih.2.2.2⟩

lemma interval_width (c : ℚ) (s n : ℕ) :
    (interval c s n).2-(interval c s n).1=8/(2:ℚ)^n := by
  induction n with
  | zero => norm_num [interval]
  | succ n ih =>
    simp only [interval,pow_succ]
    split_ifs <;> dsimp only
    all_goals
      have hn : (2:ℚ)^n≠0 := pow_ne_zero _ (by norm_num)
      field_simp [hn] at ih ⊢
      nlinarith

/-- A fixed depth yields an absolute error certificate for every rational
power comparison path. -/
theorem midpoint_error (c : ℚ) (s : ℕ) (hs : 0 < s) (t : ℝ)
    (ht : 0 ≤ t) (ht8 : t ≤ 8) (hroot : t^s=(c:ℝ)) (n : ℕ) :
    |(midpoint c s n:ℝ)-t| ≤ 8/(2:ℝ)^n := by
  have hb := interval_contains c s hs t ht ht8 hroot n
  have hw : ((interval c s n).2:ℝ)-((interval c s n).1:ℝ)=8/(2:ℝ)^n := by
    have hh := congrArg (fun q : ℚ => (q:ℝ)) (interval_width c s n)
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using hh
  unfold midpoint
  push_cast
  exact abs_le.mpr ⟨by linarith [hb.2.1,hb.2.2.1],by linarith [hb.2.1,hb.2.2.1]⟩

end

end ContingencyTables.RationalRootBisection

end OAI
