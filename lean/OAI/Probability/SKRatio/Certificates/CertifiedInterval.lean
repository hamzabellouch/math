import Mathlib
import OAI.Probability.SKRatio.Certificates.FixedExp

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate

@[reducible] def scale : ℚ := 10000000000000000000000

def down (q : ℚ) : ℚ := (⌊q*scale⌋ : ℚ)/scale
def up (q : ℚ) : ℚ := (⌈q*scale⌉ : ℚ)/scale

lemma down_le (q : ℚ) : (down q : ℝ) ≤ q := by
  have h : (down q : ℚ) ≤ q := by
    unfold down
    exact (div_le_iff₀ (by norm_num : (0:ℚ) < scale)).mpr (Int.floor_le _)
  exact_mod_cast h

lemma le_up (q : ℚ) : (q : ℝ) ≤ up q := by
  have h : q ≤ up q := by
    unfold up
    exact (le_div_iff₀ (by norm_num : (0:ℚ) < scale)).mpr (Int.le_ceil _)
  exact_mod_cast h

structure Box where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace Box

def Mem (A : Box) (x : ℝ) : Prop := (A.lo:ℝ) ≤ x ∧ x ≤ A.hi
instance : Membership ℝ Box := ⟨fun A x => A.Mem x⟩

def rat (q : ℚ) : Box := ⟨q,q⟩
def round (a b : ℚ) : Box := ⟨down a,up b⟩
def add (A B : Box) : Box := ⟨A.lo+B.lo,A.hi+B.hi⟩
def neg (A : Box) : Box := ⟨-A.hi,-A.lo⟩
def sub (A B : Box) : Box := add A (neg B)
def mul (A B : Box) : Box := round
  (min (min (A.lo*B.lo) (A.lo*B.hi)) (min (A.hi*B.lo) (A.hi*B.hi)))
  (max (max (A.lo*B.lo) (A.lo*B.hi)) (max (A.hi*B.lo) (A.hi*B.hi)))
def inv (A : Box) : Option Box := if 0 < A.lo then some (round (1/A.hi) (1/A.lo)) else none

def sq (A : Box) : Box := round
  (if 0 ≤ A.lo then A.lo^2 else if A.hi ≤ 0 then A.hi^2 else 0)
  (max (A.lo^2) (A.hi^2))

def squareIter : ℕ → Box → Box
  | 0,A => A
  | k+1,A => squareIter k (sq A)

def exp (A : Box) : Option Box :=
  if A.hi < 1073741824 then
    let B := Fixed.expBounds A.lo A.hi
    some ⟨(B.lo:ℚ)/(Fixed.S:ℚ),(B.hi:ℚ)/(Fixed.S:ℚ)⟩
  else none

lemma mem_rat (q : ℚ) : (q:ℝ) ∈ rat q := ⟨le_rfl,le_rfl⟩
lemma mem_round {x : ℝ} {a b : ℚ} (hx : (a:ℝ) ≤ x ∧ x ≤ b) : x ∈ round a b :=
  ⟨(down_le a).trans hx.1,hx.2.trans (le_up b)⟩
lemma mem_add {A B : Box} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B) : x+y ∈ add A B := by
  change _ ∧ _
  simp only [add,Rat.cast_add]
  exact ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩
lemma mem_neg {A : Box} {x : ℝ} (hx : x ∈ A) : -x ∈ neg A := by
  change _ ∧ _
  simp only [neg,Rat.cast_neg]
  exact ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩
lemma mem_sub {A B : Box} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B) : x-y ∈ sub A B := by
  exact mem_add hx (mem_neg hy)

lemma four_products {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hlo : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*c ∧
      min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*d ∧
      min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*c ∧
      min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*d := by
    simp only [min_le_iff,le_refl,or_true,true_or,and_self]
  have hhi : a*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) ∧
      a*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) ∧
      b*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) ∧
      b*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
    simp only [le_max_iff,le_refl,or_true,true_or,and_self]
  have lower {L : ℝ} (h : L ≤ a*c ∧ L ≤ a*d ∧ L ≤ b*c ∧ L ≤ b*d) : L ≤ x*y := by
    rcases le_total 0 y with hp | hn
    · have ha : L ≤ a*y := by
        rcases le_total 0 a with hap | han
        · exact h.1.trans (mul_le_mul_of_nonneg_left hy.1 hap)
        · exact h.2.1.trans (mul_le_mul_of_nonpos_left hy.2 han)
      exact ha.trans (mul_le_mul_of_nonneg_right hx.1 hp)
    · have hb : L ≤ b*y := by
        rcases le_total 0 b with hbp | hbn
        · exact h.2.2.1.trans (mul_le_mul_of_nonneg_left hy.1 hbp)
        · exact h.2.2.2.trans (mul_le_mul_of_nonpos_left hy.2 hbn)
      exact hb.trans (mul_le_mul_of_nonpos_right hx.2 hn)
  have upper {U : ℝ} (h : a*c ≤ U ∧ a*d ≤ U ∧ b*c ≤ U ∧ b*d ≤ U) : x*y ≤ U := by
    rcases le_total 0 y with hp | hn
    · have hb : b*y ≤ U := by
        rcases le_total 0 b with hbp | hbn
        · exact (mul_le_mul_of_nonneg_left hy.2 hbp).trans h.2.2.2
        · exact (mul_le_mul_of_nonpos_left hy.1 hbn).trans h.2.2.1
      exact (mul_le_mul_of_nonneg_right hx.2 hp).trans hb
    · have ha : a*y ≤ U := by
        rcases le_total 0 a with hap | han
        · exact (mul_le_mul_of_nonneg_left hy.2 hap).trans h.2.1
        · exact (mul_le_mul_of_nonpos_left hy.1 han).trans h.1
      exact (mul_le_mul_of_nonpos_right hx.1 hn).trans ha
  exact ⟨lower hlo,upper hhi⟩

lemma mem_mul {A B : Box} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B) : x*y ∈ mul A B := by
  apply mem_round
  simp only [Rat.cast_min,Rat.cast_max,Rat.cast_mul]
  exact four_products hx hy

lemma mem_inv {A B : Box} {x : ℝ} (hx : x ∈ A) (he : inv A=some B) : x⁻¹ ∈ B ∧ x ≠ 0 := by
  unfold inv at he
  split_ifs at he with hp
  · cases he
    have hp' : 0 < (A.lo:ℝ) := by exact_mod_cast hp
    have hx' : 0 < x := hp'.trans_le hx.1
    have hh : 0 < (A.hi:ℝ) := hx'.trans_le hx.2
    refine ⟨mem_round ?_,hx'.ne'⟩
    simp only [one_div,Rat.cast_inv]
    exact ⟨inv_anti₀ hx' hx.2,inv_anti₀ hp' hx.1⟩

lemma mem_sq {A : Box} {x : ℝ} (hx : x ∈ A) : x^2 ∈ sq A := by
  apply mem_round
  constructor
  · split_ifs with hp hn
    · rw [Rat.cast_pow]
      exact (sq_le_sq₀ (by exact_mod_cast hp) (by exact (show (0:ℝ) ≤ A.lo from by exact_mod_cast hp).trans hx.1)).mpr hx.1
    · rw [Rat.cast_pow]
      have hn' : (A.hi:ℝ) ≤ 0 := by exact_mod_cast hn
      nlinarith [hx.2]
    · simpa using sq_nonneg x
  · simp only [Rat.cast_max,Rat.cast_pow]
    rcases le_total 0 x with hp | hn
    · exact (show x^2 ≤ (A.hi:ℝ)^2 from (sq_le_sq₀ hp (hp.trans hx.2)).mpr hx.2).trans (le_max_right _ _)
    · have ha : (A.lo:ℝ) ≤ 0 := hx.1.trans hn
      exact (show x^2 ≤ (A.lo:ℝ)^2 by nlinarith [hx.1]).trans (le_max_left _ _)

lemma mem_squareIter {A : Box} {x : ℝ} (hx : x ∈ A) (k : ℕ) : x^(2^k) ∈ squareIter k A := by
  induction k generalizing A x with
  | zero => simpa [squareIter] using hx
  | succ k hk =>
    have h := hk (mem_sq hx)
    simpa only [squareIter,←pow_mul,show (2:ℕ)^(k+1) = 2*2^k by rw [pow_succ,Nat.mul_comm]] using h

lemma mem_exp {A B : Box} {x : ℝ} (hx : x ∈ A) (he : exp A=some B) : Real.exp x ∈ B := by
  unfold exp at he
  split_ifs at he with hh
  cases he
  have hb := Fixed.mem_expBounds hx hh
  change _ ∧ _
  simp only [Rat.cast_div,Rat.cast_intCast]
  exact hb

end Box
end SKRatio.Certificate

end

end OAI
