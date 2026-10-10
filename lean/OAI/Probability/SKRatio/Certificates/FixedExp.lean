import Mathlib

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate.Fixed

def S : ℤ := 1000000000000000000000000
structure I where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def Mem (A : I) (x : ℝ) : Prop := (A.lo:ℝ)/(S:ℝ) ≤ x ∧ x ≤ (A.hi:ℝ)/(S:ℝ)
def round (a b : ℚ) : I := ⟨⌊a*(S:ℚ)⌋,⌈b*(S:ℚ)⌉⟩
def sq (A : I) : I := ⟨(max 0 A.lo)^2/S,(A.hi^2+S)/S⟩
def iter : ℕ → I → I
  | 0,A => A
  | n+1,A => iter n (sq A)
def expBounds (a b : ℚ) : I :=
  iter 30 (round (1+a/1073741824) (1/(1-b/1073741824)))

lemma S_pos : (0:ℝ) < S := by norm_num [S]
lemma mem_round {a b : ℚ} {x : ℝ} (hx : (a:ℝ) ≤ x ∧ x ≤ b) : Mem (round a b) x := by
  have hl : (⌊a*(S:ℚ)⌋:ℚ) ≤ a*(S:ℚ) := Int.floor_le _
  have hu : b*(S:ℚ) ≤ (⌈b*(S:ℚ)⌉:ℚ) := Int.le_ceil _
  have hl' : (⌊a*(S:ℚ)⌋:ℝ) ≤ (a:ℝ)*(S:ℝ) := by exact_mod_cast hl
  have hu' : (b:ℝ)*(S:ℝ) ≤ (⌈b*(S:ℚ)⌉:ℝ) := by exact_mod_cast hu
  exact ⟨((div_le_iff₀ S_pos).mpr hl').trans hx.1,hx.2.trans ((le_div_iff₀ S_pos).mpr hu')⟩

lemma mem_sq {A : I} {x : ℝ} (hx : Mem A x) (hp : 0 ≤ x) : Mem (sq A) (x^2) := by
  have hl0 : (0:ℝ) ≤ (max 0 A.lo : ℤ)/(S:ℝ) := div_nonneg (by positivity) S_pos.le
  have hl : ((max 0 A.lo : ℤ):ℝ)/(S:ℝ) ≤ x := by
    rw [Int.cast_max,Int.cast_zero,←max_div_div_right S_pos.le]
    exact max_le (by simpa using hp) hx.1
  have hu0 : (0:ℝ) ≤ (A.hi:ℝ)/(S:ℝ) := hp.trans hx.2
  have hl2 := (sq_le_sq₀ hl0 hp).mpr hl
  have hu2 := (sq_le_sq₀ hp hu0).mpr hx.2
  have hL : ((max 0 A.lo)^2/S)*S ≤ (max 0 A.lo)^2 := Int.ediv_mul_le _ (by norm_num [S])
  have hU : A.hi^2 ≤ ((A.hi^2+S)/S)*S := by
    have hh := Int.lt_ediv_mul (A.hi^2+S) (by norm_num [S] : (0:ℤ) < S)
    linarith only [hh]
  have hL' : ((max 0 A.lo)^2/S:ℤ)*(S:ℝ) ≤ ((max 0 A.lo:ℤ):ℝ)^2 := by exact_mod_cast hL
  have hU' : (A.hi:ℝ)^2 ≤ ((A.hi^2+S)/S:ℤ)*(S:ℝ) := by exact_mod_cast hU
  refine ⟨?_,?_⟩
  · change (((max 0 A.lo)^2/S:ℤ):ℝ)/(S:ℝ) ≤ x^2
    apply le_trans _ hl2
    rw [div_pow,div_le_div_iff₀ S_pos (sq_pos_of_pos S_pos)]
    nlinarith only [mul_le_mul_of_nonneg_right hL' S_pos.le]
  · change x^2 ≤ (((A.hi^2+S)/S:ℤ):ℝ)/(S:ℝ)
    apply le_trans hu2
    rw [div_pow,div_le_div_iff₀ (sq_pos_of_pos S_pos) S_pos]
    nlinarith only [mul_le_mul_of_nonneg_right hU' S_pos.le]

lemma mem_iter {A : I} {x : ℝ} (hx : Mem A x) (hp : 0 ≤ x) (n : ℕ) :
    Mem (iter n A) (x^(2^n)) := by
  induction n generalizing A x with
  | zero => simpa only [iter,pow_zero,pow_one] using hx
  | succ n hn =>
    have h := hn (mem_sq hx hp) (sq_nonneg x)
    simpa only [iter,←pow_mul,show (2:ℕ)^(n+1) = 2*2^n by rw [pow_succ,Nat.mul_comm]] using h

lemma mem_expBounds {a b : ℚ} {x : ℝ} (hx : (a:ℝ) ≤ x ∧ x ≤ b)
    (hb : b < 1073741824) : Mem (expBounds a b) (exp x) := by
  have hhi : (b:ℝ) < 1073741824 := by exact_mod_cast hb
  have hr : Mem (round (1+a/1073741824) (1/(1-b/1073741824))) (exp (x/1073741824)) := by
    apply mem_round
    push_cast
    constructor
    · have ht := add_one_le_exp (x/1073741824)
      linarith only [hx.1,ht]
    · have hden : 0 < 1-(b:ℝ)/1073741824 := by linarith
      have hz : 1-(b:ℝ)/1073741824 ≤ exp (-(x/1073741824)) := by
        have ht := add_one_le_exp (-(x/1073741824))
        linarith only [hx.2,ht]
      have h := one_div_le_one_div_of_le hden hz
      simpa only [exp_neg,one_div,inv_inv] using h
  have he : exp (x/1073741824)^(2^30) = exp x := by
    rw [←exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [←he]
  exact mem_iter hr (exp_pos _).le 30
end SKRatio.Certificate.Fixed

end

end OAI
