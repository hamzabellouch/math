import Mathlib
import OAI.MathematicalPhysics.SheetFlows.JetCalculus

namespace OAI

/-! SheetFlows rational balls. -/

section
open Set Filter
open scoped Topology BigOperators
namespace Solenoidal

abbrev QBall := ℚ × ℚ

namespace QBall

def Contains (a : QBall) (x : ℝ) : Prop := |(a.1:ℝ)-x| ≤ (a.2:ℝ)

def point (q : ℚ) : QBall := (q,0)
def add (a b : QBall) : QBall := (a.1+b.1,a.2+b.2)
def neg (a : QBall) : QBall := (-a.1,a.2)
def mul (a b : QBall) : QBall :=
  (a.1*b.1, |a.1| *b.2 + |b.1| *a.2 + a.2*b.2)
def pow (a : QBall) : ℕ → QBall
  | 0 => point 1
  | n+1 => mul (pow a n) a

theorem radius_nonneg {a : QBall} {x : ℝ} (h : a.Contains x) : 0 ≤ a.2 := by
  exact_mod_cast (abs_nonneg _).trans h

@[simp] theorem point_contains (q : ℚ) : (point q).Contains (q:ℝ) := by
  simp [Contains,point]

theorem add_contains {a b : QBall} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (add a b).Contains (x+y) := by
  dsimp [Contains,add]
  push_cast
  calc
    |(a.1:ℝ)+b.1-(x+y)| = |((a.1:ℝ)-x)+((b.1:ℝ)-y)| := by ring_nf
    _ ≤ |(a.1:ℝ)-x|+|(b.1:ℝ)-y| := abs_add_le _ _
    _ ≤ (a.2:ℝ)+b.2 := add_le_add ha hb

theorem neg_contains {a : QBall} {x : ℝ} (ha : a.Contains x) :
    (neg a).Contains (-x) := by
  simpa only [Contains,neg,Rat.cast_neg,neg_sub_neg,← sub_eq_add_neg,abs_sub_comm] using ha

theorem mul_contains {a b : QBall} {x y : ℝ} (ha : a.Contains x) (hb : b.Contains y) :
    (mul a b).Contains (x*y) := by
  have har : (0:ℝ) ≤ a.2 := by exact_mod_cast radius_nonneg ha
  have hbr : (0:ℝ) ≤ b.2 := by exact_mod_cast radius_nonneg hb
  have hx : |x| ≤ |(a.1:ℝ)|+a.2 := by
    calc
      |x| = |(a.1:ℝ)-((a.1:ℝ)-x)| := by ring_nf
      _ ≤ |(a.1:ℝ)|+|(a.1:ℝ)-x| := abs_sub _ _
      _ ≤ _ := add_le_add le_rfl ha
  dsimp [Contains,mul]
  push_cast
  calc
    |(a.1:ℝ)*b.1-x*y| = |(a.1:ℝ)*((b.1:ℝ)-y) + ((a.1:ℝ)-x)*y| := by ring_nf
    _ ≤ |(a.1:ℝ)*((b.1:ℝ)-y)| + |((a.1:ℝ)-x)*y| := abs_add_le _ _
    _ = |(a.1:ℝ)| *|(b.1:ℝ)-y| + |(a.1:ℝ)-x| *|y| := by simp only [abs_mul]
    _ ≤ |(a.1:ℝ)| *b.2 + a.2*(|(b.1:ℝ)|+b.2) := by
      have hy : |y| ≤ |(b.1:ℝ)|+b.2 := by
        calc
          |y| = |(b.1:ℝ)-((b.1:ℝ)-y)| := by ring_nf
          _ ≤ |(b.1:ℝ)|+|(b.1:ℝ)-y| := abs_sub _ _
          _ ≤ _ := add_le_add le_rfl hb
      exact add_le_add (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
        (mul_le_mul ha hy (abs_nonneg _) har)
    _ = _ := by ring

theorem pow_contains {a : QBall} {x : ℝ} (ha : a.Contains x) (n : ℕ) :
    (pow a n).Contains (x^n) := by
  induction n with
  | zero => simpa [QBall.pow] using point_contains 1
  | succ n ih => simpa only [pow,pow_succ] using mul_contains ih ha

structure Approximates (A : ℕ → QBall) (x : ℝ) : Prop where
  contains : ∀ n, (A n).Contains x
  radius : Tendsto (fun n => ((A n).2:ℝ)) atTop (𝓝 0)

theorem Approximates.center {A : ℕ → QBall} {x : ℝ} (h : Approximates A x) :
    Tendsto (fun n => ((A n).1:ℝ)) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => h.contains n) h.radius

theorem approximates_point (q : ℚ) : Approximates (fun _ => point q) (q:ℝ) :=
  ⟨fun _ => point_contains q, by simp [point]⟩

theorem Approximates.add {A B : ℕ → QBall} {x y : ℝ}
    (ha : Approximates A x) (hb : Approximates B y) :
    Approximates (fun n => add (A n) (B n)) (x+y) := by
  refine ⟨fun n => add_contains (ha.contains n) (hb.contains n), ?_⟩
  simpa [QBall.add] using ha.radius.add hb.radius

theorem Approximates.neg {A : ℕ → QBall} {x : ℝ} (h : Approximates A x) :
    Approximates (fun n => neg (A n)) (-x) :=
  ⟨fun n => neg_contains (h.contains n),h.radius⟩

theorem Approximates.mul {A B : ℕ → QBall} {x y : ℝ}
    (ha : Approximates A x) (hb : Approximates B y) :
    Approximates (fun n => mul (A n) (B n)) (x*y) := by
  refine ⟨fun n => mul_contains (ha.contains n) (hb.contains n), ?_⟩
  simpa [QBall.mul] using ((ha.center.abs.mul hb.radius).add
    (hb.center.abs.mul ha.radius)).add (ha.radius.mul hb.radius)

theorem Approximates.pow {A : ℕ → QBall} {x : ℝ}
    (h : Approximates A x) (m : ℕ) :
    Approximates (fun n => pow (A n) m) (x^m) := by
  induction m with
  | zero => simpa [QBall.pow] using approximates_point 1
  | succ m hm => simpa [QBall.pow,pow_succ] using hm.mul h

def taylor (q : ℚ) (n : ℕ) : ℚ := ∑ m ∈ Finset.range n, q^m / (m.factorial:ℚ)

def smallExp (q : ℚ) (n : ℕ) : QBall :=
  (taylor q (n+1), 2*(1/2:ℚ)^(n+1))

theorem smallExp_approximates (q : ℚ) (hq : |q| ≤ 1/2) :
    Approximates (smallExp q) (Real.exp (q:ℝ)) := by
  have hq' : |(q:ℝ)| ≤ 1/2 := by
    have h : ((|q|:ℚ):ℝ) ≤ ((1/2:ℚ):ℝ) := Rat.cast_le.mpr hq
    simpa using h
  refine ⟨?_, ?_⟩
  · intro n
    have he := Real.exp_bound (show |(q:ℝ)| ≤ 1 by linarith) (Nat.succ_pos n)
    have hf : (1:ℝ) ≤ (n+1).factorial := by exact_mod_cast (n+1).factorial_pos
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast Nat.succ_pos n
    have hb : (((n+1).succ:ℕ):ℝ) / ((n+1).factorial * (n+1:ℕ)) ≤ 2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      push_cast
      have := mul_le_mul_of_nonneg_right hf (show (0:ℝ) ≤ n+1 by positivity)
      nlinarith
    have hp := pow_le_pow_left₀ (abs_nonneg (q:ℝ)) hq' (n+1)
    have hg := he.trans (mul_le_mul hp hb (by positivity) (by positivity))
    simpa [Contains,smallExp,taylor,abs_sub_comm,mul_comm] using hg
  · have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).mul_const (1/2:ℝ)
    simpa [smallExp,pow_succ] using hh.const_mul 2

def expScale (q : ℚ) : ℕ := 2 * (q.num.natAbs+1)
def expApprox (q : ℚ) (n : ℕ) : QBall :=
  pow (smallExp (q / (expScale q:ℚ)) n) (expScale q)

theorem expScale_pos (q : ℚ) : 0 < expScale q := by unfold expScale; omega

theorem expScale_large (q : ℚ) : |q / (expScale q:ℚ)| ≤ 1/2 := by
  have hden : (1:ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have hn : |q| ≤ (q.num.natAbs:ℚ) := by
    have hnum : |(q.num:ℚ)| = (q.num.natAbs:ℚ) := by
      cases h : q.num with
      | ofNat n => simp
      | negSucc n => simp [Int.negSucc_eq]
    calc
      |q| = |(q.num:ℚ)| / q.den := by
        conv_lhs => rw [← Rat.num_div_den q]
        rw [abs_div,abs_of_nonneg (show (0:ℚ) ≤ (q.den:ℚ) by positivity)]
      _ ≤ |(q.num:ℚ)| := div_le_self (abs_nonneg _) hden
      _ = _ := hnum
  rw [abs_div,abs_of_pos (show (0:ℚ) < (expScale q:ℚ) by exact_mod_cast expScale_pos q),
    div_le_iff₀ (show (0:ℚ) < (expScale q:ℚ) by exact_mod_cast expScale_pos q)]
  dsimp [expScale]
  push_cast
  linarith

theorem expApprox_approximates (q : ℚ) :
    Approximates (expApprox q) (Real.exp (q:ℝ)) := by
  have h := (smallExp_approximates _ (expScale_large q)).pow (expScale q)
  have he : Real.exp ((q / (expScale q:ℚ):ℚ):ℝ) ^ expScale q = Real.exp (q:ℝ) := by
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    field_simp [(show (expScale q:ℝ) ≠ 0 by exact_mod_cast (expScale_pos q).ne')]
  exact he ▸ h

def clampInv (a : QBall) : QBall := ((max (1/32) a.1)⁻¹,512*a.2)

theorem clampInv_contains {a : QBall} {x : ℝ} (ha : a.Contains x) (hx : 1/16 ≤ x) :
    (clampInv a).Contains x⁻¹ := by
  have hcl : |max (1/32:ℝ) a.1 - x| ≤ (a.2:ℝ) := by
    rcases le_total (1/32:ℝ) a.1 with h | h
    · rw [max_eq_right h]; exact ha
    · rw [max_eq_left h,abs_of_nonpos (by linarith)]
      have hh := (neg_le_abs ((a.1:ℝ)-x)).trans ha
      linarith
  have hc : (1/32:ℝ) ≤ max (1/32:ℝ) a.1 := le_max_left _ _
  have hcpos : 0 < max (1/32:ℝ) a.1 := by linarith
  have hxpos : 0 < x := by linarith
  have hd : (1/512:ℝ) ≤ max (1/32:ℝ) a.1 * x := by nlinarith
  have hdiv : |(max (1/32:ℝ) a.1)⁻¹ - x⁻¹| =
      |max (1/32:ℝ) a.1 - x| / (max (1/32:ℝ) a.1 * x) := by
    rw [inv_sub_inv hcpos.ne' hxpos.ne',abs_div,abs_sub_comm,abs_of_pos (mul_pos hcpos hxpos)]
  simp only [Contains,clampInv,Rat.cast_inv,Rat.cast_max,Rat.cast_div,Rat.cast_one,
    Rat.cast_ofNat,Rat.cast_mul]
  rw [hdiv]
  apply (div_le_iff₀ (mul_pos hcpos hxpos)).mpr
  have hr : (0:ℝ) ≤ a.2 := by exact_mod_cast radius_nonneg ha
  nlinarith

theorem Approximates.clampInv {A : ℕ → QBall} {x : ℝ}
    (h : Approximates A x) (hx : 1/16 ≤ x) :
    Approximates (fun n => clampInv (A n)) x⁻¹ := by
  refine ⟨fun n => clampInv_contains (h.contains n) hx, ?_⟩
  simpa [QBall.clampInv] using h.radius.const_mul 512

def flatApprox (m : ℕ) (q : ℚ) (n : ℕ) : QBall :=
  if q ≤ 0 then point 0 else
    mul (point (q⁻¹^m)) (expApprox (-q⁻¹) n)

theorem flatApprox_approximates (m : ℕ) (q : ℚ) :
    Approximates (flatApprox m q) (flatJet (Polynomial.X^m) (q:ℝ)) := by
  unfold flatApprox
  by_cases hq : q ≤ 0
  · have hq' : (q:ℝ) ≤ 0 := by exact_mod_cast hq
    simpa [hq,flatJet,expNegInvGlue.zero_of_nonpos hq'] using approximates_point 0
  · have hq' : ¬ (q:ℝ) ≤ 0 := by exact_mod_cast hq
    have h := (approximates_point (q⁻¹^m)).mul (expApprox_approximates (-q⁻¹))
    simpa [hq,flatJet,expNegInvGlue,hq'] using h

def reciprocalApprox (q : ℚ) (n : ℕ) : QBall :=
  clampInv (add (flatApprox 0 q n) (flatApprox 0 (1-q) n))

theorem reciprocalApprox_approximates (q : ℚ) :
    Approximates (reciprocalApprox q) (transitionReciprocal (q:ℝ)) := by
  have hlow : (1/16:ℝ) ≤ expNegInvGlue q + expNegInvGlue (1-q) := by
    have hb := transitionReciprocal_bound (q:ℝ)
    have hp := Real.smoothTransition.pos_denom (q:ℝ)
    rw [transitionReciprocal,abs_of_pos (inv_pos.mpr hp)] at hb
    have := (div_le_iff₀ hp).mp (show 1 / _ ≤ 16 by simpa [one_div] using hb)
    linarith
  have h := ((flatApprox_approximates 0 q).add
    (flatApprox_approximates 0 (1-q))).clampInv
  simp only [flatJet,pow_zero,Polynomial.map_one,Polynomial.eval_one,one_mul,
    Rat.cast_sub,Rat.cast_one] at h
  exact h hlow

end QBall
end Solenoidal
end

end OAI
