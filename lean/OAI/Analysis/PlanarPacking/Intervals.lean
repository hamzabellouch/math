import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

def precision : ℤ := 10^30
lemma precision_pos : (0:ℝ) < precision := by norm_num [precision]

structure RBox where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr
structure CBox where
  re : RBox
  im : RBox
  deriving DecidableEq, Repr

def RBox.Contains (a : RBox) (x : ℝ) : Prop :=
  (a.lo:ℝ) ≤ precision*x ∧ precision*x ≤ (a.hi:ℝ)
def CBox.Contains (a : CBox) (x : ℂ) : Prop := a.re.Contains x.re ∧ a.im.Contains x.im

def mulLo (a b : RBox) : ℤ :=
  min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))
def mulHi (a b : RBox) : ℤ :=
  max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))

def RBox.AddCheck (a b c : RBox) : Prop := c.lo ≤ a.lo+b.lo ∧ a.hi+b.hi ≤ c.hi
instance (a b c : RBox) : Decidable (a.AddCheck b c) := inferInstanceAs (Decidable (_ ∧ _))
def RBox.MulCheck (a b c : RBox) : Prop := c.lo*precision ≤ mulLo a b ∧ mulHi a b ≤ c.hi*precision
instance (a b c : RBox) : Decidable (a.MulCheck b c) := inferInstanceAs (Decidable (_ ∧ _))

def CBox.AddCheck (a b c : CBox) : Prop := a.re.AddCheck b.re c.re ∧ a.im.AddCheck b.im c.im
instance (a b c : CBox) : Decidable (a.AddCheck b c) := inferInstanceAs (Decidable (_ ∧ _))
def CBox.MulCheck (a b c : CBox) : Prop :=
  c.re.lo*precision ≤ mulLo a.re b.re-mulHi a.im b.im ∧
  mulHi a.re b.re-mulLo a.im b.im ≤ c.re.hi*precision ∧
  c.im.lo*precision ≤ mulLo a.re b.im+mulLo a.im b.re ∧
  mulHi a.re b.im+mulHi a.im b.re ≤ c.im.hi*precision
instance (a b c : CBox) : Decidable (a.MulCheck b c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

lemma between_mul {a b y x L U : ℝ} (hy : a ≤ y ∧ y ≤ b)
    (ha : L ≤ x*a ∧ x*a ≤ U) (hb : L ≤ x*b ∧ x*b ≤ U) :
    L ≤ x*y ∧ x*y ≤ U := by
  rcases le_total 0 x with hx | hx
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_left hy.1 hx),
      (mul_le_mul_of_nonneg_left hy.2 hx).trans hb.2⟩
  · exact ⟨hb.1.trans (mul_le_mul_of_nonpos_left hy.2 hx),
      (mul_le_mul_of_nonpos_left hy.1 hx).trans ha.2⟩
lemma real_mul_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  apply between_mul hy
  · rw [mul_comm x c]
    apply between_mul hx <;> constructor <;> simp only [mul_comm c, le_max_iff, min_le_iff, le_refl] <;> tauto
  · rw [mul_comm x d]
    apply between_mul hx <;> constructor <;> simp only [mul_comm d, le_max_iff, min_le_iff, le_refl] <;> tauto

lemma mul_bounds {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (mulLo a b:ℝ) ≤ (precision:ℝ)^2*(x*y) ∧
      (precision:ℝ)^2*(x*y) ≤ (mulHi a b:ℝ) := by
  convert real_mul_bounds hx hy using 1 <;> push_cast [mulLo,mulHi] <;> ring_nf

lemma RBox.add_contains {a b c : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.AddCheck b c) : c.Contains (x+y) := by
  have h₁ : (c.lo:ℝ) ≤ a.lo+b.lo := by exact_mod_cast hc.1
  have h₂ : (a.hi:ℝ)+b.hi ≤ c.hi := by exact_mod_cast hc.2
  constructor <;> nlinarith only [hx.1,hx.2,hy.1,hy.2,h₁,h₂]

lemma RBox.mul_contains {a b c : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.MulCheck b c) : c.Contains (x*y) := by
  have hh := mul_bounds hx hy
  have h₁ : (c.lo:ℝ)*precision ≤ mulLo a b := by exact_mod_cast hc.1
  have h₂ : (mulHi a b:ℝ) ≤ c.hi*precision := by exact_mod_cast hc.2
  constructor
  · exact (mul_le_mul_iff_right₀ precision_pos).mp (by nlinarith only [hh.1,h₁])
  · exact (mul_le_mul_iff_right₀ precision_pos).mp (by nlinarith only [hh.2,h₂])

lemma CBox.add_contains {a b c : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.AddCheck b c) : c.Contains (x+y) :=
  ⟨RBox.add_contains hx.1 hy.1 hc.1,RBox.add_contains hx.2 hy.2 hc.2⟩
lemma CBox.mul_contains {a b c : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.MulCheck b c) : c.Contains (x*y) := by
  have hrr := mul_bounds hx.1 hy.1
  have hri := mul_bounds hx.1 hy.2
  have hir := mul_bounds hx.2 hy.1
  have hii := mul_bounds hx.2 hy.2
  have h₁ : (c.re.lo:ℝ)*precision ≤ (mulLo a.re b.re:ℝ)-(mulHi a.im b.im:ℝ) := by exact_mod_cast hc.1
  have h₂ : (mulHi a.re b.re:ℝ)-(mulLo a.im b.im:ℝ) ≤ (c.re.hi:ℝ)*precision := by exact_mod_cast hc.2.1
  have h₃ : (c.im.lo:ℝ)*precision ≤ (mulLo a.re b.im:ℝ)+(mulLo a.im b.re:ℝ) := by exact_mod_cast hc.2.2.1
  have h₄ : (mulHi a.re b.im:ℝ)+(mulHi a.im b.re:ℝ) ≤ (c.im.hi:ℝ)*precision := by exact_mod_cast hc.2.2.2
  constructor <;> constructor
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_re]
    nlinarith only [hrr.1,hii.2,h₁]
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_re]
    nlinarith only [hrr.2,hii.1,h₂]
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_im]
    nlinarith only [hri.1,hir.1,h₃]
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_im]
    nlinarith only [hri.2,hir.2,h₄]


def RBox.RatCheck (a : RBox) (m n : ℤ) : Prop :=
  0 < n ∧ a.lo*n ≤ precision*m ∧ precision*m ≤ a.hi*n
instance (a : RBox) (m n : ℤ) : Decidable (a.RatCheck m n) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
lemma RBox.rat_contains {a : RBox} {m n : ℤ} (h : a.RatCheck m n) :
    a.Contains ((m:ℝ)/n) := by
  have hn : (0:ℝ) < n := by exact_mod_cast h.1
  have h₁ : (a.lo:ℝ)*n ≤ precision*m := by exact_mod_cast h.2.1
  have h₂ : (precision:ℝ)*m ≤ a.hi*n := by exact_mod_cast h.2.2
  constructor
  · rw [← mul_div_assoc]; exact (le_div_iff₀ hn).mpr h₁
  · rw [← mul_div_assoc]; exact (div_le_iff₀ hn).mpr h₂

def CBox.RatCheck (a : CBox) (mr nr mi ni : ℤ) : Prop :=
  a.re.RatCheck mr nr ∧ a.im.RatCheck mi ni
instance (a : CBox) (mr nr mi ni : ℤ) : Decidable (a.RatCheck mr nr mi ni) :=
  inferInstanceAs (Decidable (_ ∧ _))
lemma CBox.rat_contains {a : CBox} {mr nr mi ni : ℤ} (h : a.RatCheck mr nr mi ni) :
    a.Contains ((mr:ℂ)/nr + (mi:ℂ)/ni*Complex.I) := by
  constructor
  · simpa using RBox.rat_contains h.1
  · simpa using RBox.rat_contains h.2

def RBox.neg (a : RBox) : RBox := ⟨-a.hi,-a.lo⟩
def CBox.neg (a : CBox) : CBox := ⟨a.re.neg,a.im.neg⟩
lemma RBox.neg_contains {a : RBox} {x : ℝ} (hx : a.Contains x) : a.neg.Contains (-x) := by
  simpa [Contains,neg,mul_neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)
lemma CBox.neg_contains {a : CBox} {z : ℂ} (hz : a.Contains z) : a.neg.Contains (-z) :=
  ⟨RBox.neg_contains hz.1,RBox.neg_contains hz.2⟩

def RBox.ScaleCheck (a c : RBox) (m n : ℤ) : Prop :=
  0 < n ∧ c.lo*n ≤ min (m*a.lo) (m*a.hi) ∧ max (m*a.lo) (m*a.hi) ≤ c.hi*n
instance (a c : RBox) (m n : ℤ) : Decidable (a.ScaleCheck c m n) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

lemma RBox.scale_contains {a c : RBox} {x : ℝ} {m n : ℤ} (hx : a.Contains x)
    (hc : a.ScaleCheck c m n) : c.Contains (((m:ℝ)/n)*x) := by
  have hn : (0:ℝ) < n := by exact_mod_cast hc.1
  have h₁ : (c.lo:ℝ)*n ≤ min ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) := by exact_mod_cast hc.2.1
  have h₂ : max ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) ≤ (c.hi:ℝ)*n := by exact_mod_cast hc.2.2
  have hh : min ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) ≤ (m:ℝ)*(precision*x) ∧
      (m:ℝ)*(precision*x) ≤ max ((m:ℝ)*a.lo) ((m:ℝ)*a.hi) := by
    apply between_mul hx <;> simp
  constructor
  · apply (mul_le_mul_iff_right₀ hn).mp
    convert h₁.trans hh.1 using 1 <;> field_simp
  · apply (mul_le_mul_iff_right₀ hn).mp
    convert hh.2.trans h₂ using 1 <;> field_simp

def CBox.ScaleCheck (a c : CBox) (m n : ℤ) : Prop :=
  a.re.ScaleCheck c.re m n ∧ a.im.ScaleCheck c.im m n
instance (a c : CBox) (m n : ℤ) : Decidable (a.ScaleCheck c m n) := inferInstanceAs (Decidable (_ ∧ _))
lemma CBox.scale_contains {a c : CBox} {z : ℂ} {m n : ℤ} (hz : a.Contains z)
    (hc : a.ScaleCheck c m n) : c.Contains (((m:ℂ)/n)*z) := by
  constructor
  · simpa using RBox.scale_contains hz.1 hc.1
  · simpa using RBox.scale_contains hz.2 hc.2

def RBox.InvCheck (a c : RBox) : Prop :=
  0 < a.lo ∧ 0 ≤ c.lo ∧ 0 ≤ c.hi ∧ c.lo*a.hi ≤ precision^2 ∧ precision^2 ≤ c.hi*a.lo
instance (a c : RBox) : Decidable (a.InvCheck c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
lemma RBox.inv_contains {a c : RBox} {x : ℝ} (hx : a.Contains x)
    (hc : a.InvCheck c) : c.Contains x⁻¹ := by
  have ha : (0:ℝ) < a.lo := by exact_mod_cast hc.1
  have hcl : (0:ℝ) ≤ c.lo := by exact_mod_cast hc.2.1
  have hcu : (0:ℝ) ≤ c.hi := by exact_mod_cast hc.2.2.1
  have h₁ : (c.lo:ℝ)*a.hi ≤ (precision:ℝ)^2 := by exact_mod_cast hc.2.2.2.1
  have h₂ : (precision:ℝ)^2 ≤ (c.hi:ℝ)*a.lo := by exact_mod_cast hc.2.2.2.2
  have hp := precision_pos
  have hx0 : 0 < x := by nlinarith only [hx.1,ha,hp]
  constructor <;> rw [← div_eq_mul_inv]
  · apply (le_div_iff₀ hx0).mpr
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [mul_le_mul_of_nonneg_left hx.2 hcl,h₁]
  · apply (div_le_iff₀ hx0).mpr
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [mul_le_mul_of_nonneg_left hx.1 hcu,h₂]


def RBox.bound (a : RBox) : ℤ := max |a.lo| |a.hi|
lemma RBox.abs_bound {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (precision:ℝ)*|x| ≤ (a.bound:ℝ) := by
  rw [← abs_of_pos precision_pos,← abs_mul,abs_le]
  have h₁ : -(a.bound:ℝ) ≤ (a.lo:ℝ) := by
    have hh := (neg_abs_le a.lo).trans (le_refl a.lo)
    have hu : |a.lo| ≤ a.bound := le_max_left _ _
    exact_mod_cast (neg_le_neg hu).trans hh
  have h₂ : (a.hi:ℝ) ≤ (a.bound:ℝ) := by
    exact_mod_cast (le_abs_self a.hi).trans (le_max_right |a.lo| |a.hi|)
  exact ⟨h₁.trans hx.1,hx.2.trans h₂⟩

def CBox.NormCheck (a : CBox) (n : ℤ) : Prop := a.re.bound+a.im.bound ≤ precision*n
instance (a : CBox) (n : ℤ) : Decidable (a.NormCheck n) := inferInstanceAs (Decidable (_ ≤ _))
lemma CBox.norm_le {a : CBox} {z : ℂ} {n : ℤ} (hz : a.Contains z) (hc : a.NormCheck n) :
    ‖z‖ ≤ (n:ℝ) := by
  have h₁ := RBox.abs_bound hz.1
  have h₂ := RBox.abs_bound hz.2
  have hc' : (a.re.bound:ℝ)+a.im.bound ≤ (precision:ℝ)*n := by exact_mod_cast hc
  have hh := mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im z) precision_pos.le
  apply (mul_le_mul_iff_right₀ precision_pos).mp
  nlinarith only [h₁,h₂,hc',hh]

def CBox.WidenCheck (a c : CBox) (n : ℤ) : Prop :=
  c.re.lo ≤ a.re.lo-n ∧ a.re.hi+n ≤ c.re.hi ∧
  c.im.lo ≤ a.im.lo-n ∧ a.im.hi+n ≤ c.im.hi
instance (a c : CBox) (n : ℤ) : Decidable (a.WidenCheck c n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
lemma CBox.widen_contains {a c : CBox} {z w : ℂ} {n : ℤ} (hz : a.Contains z)
    (herr : (precision:ℝ)*‖w-z‖ ≤ (n:ℝ)) (hc : a.WidenCheck c n) : c.Contains w := by
  have hr : (precision:ℝ)*|(w-z).re| ≤ (n:ℝ) :=
    (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm (w-z)) precision_pos.le).trans herr
  have hi : (precision:ℝ)*|(w-z).im| ≤ (n:ℝ) :=
    (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm (w-z)) precision_pos.le).trans herr
  have hra : |(precision:ℝ)*(w-z).re| ≤ (n:ℝ) := by simpa [abs_mul,abs_of_pos precision_pos] using hr
  have hia : |(precision:ℝ)*(w-z).im| ≤ (n:ℝ) := by simpa [abs_mul,abs_of_pos precision_pos] using hi
  rcases abs_le.mp hra with ⟨hrl,hru⟩
  rcases abs_le.mp hia with ⟨hil,hiu⟩
  have h₁ : (c.re.lo:ℝ) ≤ (a.re.lo:ℝ)-n := by exact_mod_cast hc.1
  have h₂ : (a.re.hi:ℝ)+n ≤ (c.re.hi:ℝ) := by exact_mod_cast hc.2.1
  have h₃ : (c.im.lo:ℝ) ≤ (a.im.lo:ℝ)-n := by exact_mod_cast hc.2.2.1
  have h₄ : (a.im.hi:ℝ)+n ≤ (c.im.hi:ℝ) := by exact_mod_cast hc.2.2.2
  simp only [Complex.sub_re] at hrl hru
  simp only [Complex.sub_im] at hil hiu
  exact ⟨⟨by nlinarith only [hz.1.1,hrl,h₁],by nlinarith only [hz.1.2,hru,h₂]⟩,
    ⟨by nlinarith only [hz.2.1,hil,h₃],by nlinarith only [hz.2.2,hiu,h₄]⟩⟩

noncomputable def expHorner (z : ℂ) (k : ℕ) : ℕ → ℂ
  | 0 => (k.factorial:ℂ)⁻¹
  | n+1 => (k.factorial:ℂ)⁻¹ + z*expHorner z (k+1) n

lemma expHorner_eq (z : ℂ) (k n : ℕ) :
    expHorner z k n = ∑ i ∈ Finset.range (n+1), z^i/((k+i).factorial:ℂ) := by
  induction n generalizing k with
  | zero => simp [expHorner]
  | succ n ih =>
    rw [expHorner,ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero,Nat.add_zero,one_div]
    rw [add_comm,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ']
    simp only [Nat.add_assoc,Nat.add_comm 1 i,mul_div_assoc]

lemma exp_small_error {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (precision:ℝ)*‖Complex.exp z-expHorner z 0 32‖ ≤ 1 := by
  rw [expHorner_eq]
  simp only [Nat.zero_add]
  have hh := Complex.exp_bound hz (n:=33) (by norm_num)
  have hp : ‖z‖^33 ≤ (1:ℝ) := pow_le_one₀ (norm_nonneg _) hz
  have hc : (34:ℝ)*((33).factorial*33:ℝ)⁻¹ ≤ 1/10^30 := by norm_num
  have hb : ‖Complex.exp z-∑ n ∈ Finset.range 33, z^n/(n.factorial:ℂ)‖ ≤ 1/10^30 :=
    hh.trans ((mul_le_of_le_one_left (by positivity) hp).trans hc)
  dsimp [precision]
  norm_num
  nlinarith only [hb]

lemma horner_step {a b p m c : CBox} {z : ℂ} {k n : ℕ}
    (hz : a.Contains z) (hb : b.Contains (expHorner z (k+1) n))
    (hp : p.RatCheck 1 (k.factorial:ℤ) 0 1) (hm : a.MulCheck b m)
    (hc : p.AddCheck m c) : c.Contains (expHorner z k (n+1)) := by
  have hr : p.Contains ((k.factorial:ℂ)⁻¹) := by simpa using CBox.rat_contains hp
  exact CBox.add_contains hr (CBox.mul_contains hz hb hm) hc

lemma exp_from_horner {a b c : CBox} {z : ℂ} (hz : a.Contains z)
    (hn : a.NormCheck 1) (hb : b.Contains (expHorner z 0 32))
    (hc : b.WidenCheck c 1) : c.Contains (Complex.exp z) := by
  apply CBox.widen_contains hb _ hc
  simpa using exp_small_error (by simpa using CBox.norm_le hz hn)

lemma power_mul {a b c : CBox} {z : ℂ} {j k : ℕ}
    (ha : a.Contains (z^j)) (hb : b.Contains (z^k)) (hc : a.MulCheck b c) :
    c.Contains (z^(j+k)) := by rw [pow_add]; exact CBox.mul_contains ha hb hc


lemma CBox.inv_checked {a c : CBox} {rr ii den dinv : RBox} {z : ℂ}
    (hz : a.Contains z) (hrr : a.re.MulCheck a.re rr) (hii : a.im.MulCheck a.im ii)
    (hs : rr.AddCheck ii den) (hi : den.InvCheck dinv)
    (hr : a.re.MulCheck dinv c.re) (him : a.im.neg.MulCheck dinv c.im) :
    c.Contains z⁻¹ := by
  have hden : den.Contains (Complex.normSq z) :=
    RBox.add_contains (RBox.mul_contains hz.1 hz.1 hrr) (RBox.mul_contains hz.2 hz.2 hii) hs
  have hdinv := RBox.inv_contains hden hi
  constructor
  · simpa [Complex.inv_re,div_eq_mul_inv] using RBox.mul_contains hz.1 hdinv hr
  · simpa [Complex.inv_im,div_eq_mul_inv] using RBox.mul_contains (RBox.neg_contains hz.2) hdinv him

def piBounds : RBox := ⟨3141592653589793238460000000000,3141592653589793238470000000000⟩
lemma piBounds_contains : piBounds.Contains Real.pi := by
  have hp := Real.pi_gt_d20
  have hq := Real.pi_lt_d20
  norm_num [piBounds,RBox.Contains,precision]
  constructor <;> linarith

def bBounds : RBox := ⟨866025403784438646760000000000,866025403784438646770000000000⟩
lemma bBounds_contains : bBounds.Contains (Real.sqrt 3/2) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  norm_num [bBounds,RBox.Contains,precision]
  constructor <;> nlinarith

lemma CBox.ofReal_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (⟨a,⟨0,0⟩⟩ : CBox).Contains (x:ℂ) := by
  exact ⟨hx,by simp [RBox.Contains]⟩

end IntegerIntervals
end SharpPlanar

namespace SharpPlanar.IntegerIntervals

lemma floor_mul_le (x : ℤ) {n : ℤ} (hn : 0 < n) : x/n*n ≤ x :=
  Int.ediv_mul_le x (ne_of_gt hn)
lemma le_ceil_mul (x : ℤ) {n : ℤ} (hn : 0 < n) : x ≤ -((-x)/n)*n := by
  have hh := floor_mul_le (-x) hn
  nlinarith only [hh]

def RBox.rat (m n : ℤ) : RBox := ⟨precision*m/n,-((-precision*m)/n)⟩
def CBox.rat (mr nr mi ni : ℤ) : CBox := ⟨RBox.rat mr nr,RBox.rat mi ni⟩
def RBox.add (a b : RBox) : RBox := ⟨a.lo+b.lo,a.hi+b.hi⟩
def CBox.add (a b : CBox) : CBox := ⟨a.re.add b.re,a.im.add b.im⟩
def RBox.mul (a b : RBox) : RBox :=
  ⟨mulLo a b/precision,-((-mulHi a b)/precision)⟩
def CBox.mul (a b : CBox) : CBox :=
  ⟨⟨(mulLo a.re b.re-mulHi a.im b.im)/precision,
      -((-(mulHi a.re b.re-mulLo a.im b.im))/precision)⟩,
   ⟨(mulLo a.re b.im+mulLo a.im b.re)/precision,
      -((-(mulHi a.re b.im+mulHi a.im b.re))/precision)⟩⟩
def RBox.scale (a : RBox) (m n : ℤ) : RBox :=
  ⟨min (m*a.lo) (m*a.hi)/n,-((-max (m*a.lo) (m*a.hi))/n)⟩
def CBox.scale (a : CBox) (m n : ℤ) : CBox := ⟨a.re.scale m n,a.im.scale m n⟩
def RBox.inv (a : RBox) : RBox := ⟨precision^2/a.hi,-((-precision^2)/a.lo)⟩
def CBox.inv (a : CBox) : CBox :=
  let d := (a.re.mul a.re).add (a.im.mul a.im)
  let di := d.inv
  ⟨a.re.mul di,a.im.neg.mul di⟩
def CBox.widen (a : CBox) (k : ℤ) : CBox :=
  ⟨⟨a.re.lo-k,a.re.hi+k⟩,⟨a.im.lo-k,a.im.hi+k⟩⟩
def CBox.horner (a : CBox) (k : ℕ) : ℕ → CBox
  | 0 => CBox.rat 1 (k.factorial:ℤ) 0 1
  | n+1 => (CBox.rat 1 (k.factorial:ℤ) 0 1).add (a.mul (a.horner (k+1) n))
def CBox.squareIter (a : CBox) : ℕ → CBox
  | 0 => a
  | n+1 => let b := a.squareIter n; b.mul b
def CBox.exp (a : CBox) (k : ℕ := 11) : CBox :=
  (((a.scale 1 (2^k)).horner 0 32).widen 1).squareIter k

lemma RBox.rat_check (m n : ℤ) (hn : 0 < n) : (RBox.rat m n).RatCheck m n := by
  exact ⟨hn,floor_mul_le _ hn,by simpa only [RBox.rat, neg_mul] using le_ceil_mul (precision*m) hn⟩
lemma CBox.rat_check (mr nr mi ni : ℤ) (hr : 0 < nr) (hi : 0 < ni) :
    (CBox.rat mr nr mi ni).RatCheck mr nr mi ni :=
  ⟨RBox.rat_check _ _ hr,RBox.rat_check _ _ hi⟩
lemma RBox.add_check (a b : RBox) : a.AddCheck b (a.add b) := ⟨le_rfl,le_rfl⟩
lemma CBox.add_check (a b : CBox) : a.AddCheck b (a.add b) :=
  ⟨RBox.add_check _ _,RBox.add_check _ _⟩
lemma RBox.mul_check (a b : RBox) : a.MulCheck b (a.mul b) :=
  ⟨floor_mul_le _ (by norm_num [precision]),le_ceil_mul _ (by norm_num [precision])⟩
lemma CBox.mul_check (a b : CBox) : a.MulCheck b (a.mul b) :=
  ⟨floor_mul_le _ (by norm_num [precision]),le_ceil_mul _ (by norm_num [precision]),
   floor_mul_le _ (by norm_num [precision]),le_ceil_mul _ (by norm_num [precision])⟩
lemma RBox.scale_check (a : RBox) (m n : ℤ) (hn : 0 < n) : a.ScaleCheck (a.scale m n) m n :=
  ⟨hn,floor_mul_le _ hn,le_ceil_mul _ hn⟩
lemma CBox.scale_check (a : CBox) (m n : ℤ) (hn : 0 < n) : a.ScaleCheck (a.scale m n) m n :=
  ⟨RBox.scale_check _ _ _ hn,RBox.scale_check _ _ _ hn⟩
lemma CBox.widen_check (a : CBox) (k : ℤ) : a.WidenCheck (a.widen k) k := by
  exact ⟨le_rfl,le_rfl,le_rfl,le_rfl⟩

lemma RBox.contains_rat (m n : ℤ) (hn : 0 < n) : (RBox.rat m n).Contains ((m:ℝ)/n) :=
  RBox.rat_contains (RBox.rat_check m n hn)
lemma CBox.contains_rat (mr nr mi ni : ℤ) (hr : 0 < nr) (hi : 0 < ni) :
    (CBox.rat mr nr mi ni).Contains ((mr:ℂ)/nr+(mi:ℂ)/ni*Complex.I) :=
  CBox.rat_contains (CBox.rat_check _ _ _ _ hr hi)
lemma RBox.contains_add {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := RBox.add_contains hx hy (RBox.add_check _ _)
lemma CBox.contains_add {a b : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := CBox.add_contains hx hy (CBox.add_check _ _)
lemma RBox.contains_mul {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := RBox.mul_contains hx hy (RBox.mul_check _ _)
lemma CBox.contains_mul {a b : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := CBox.mul_contains hx hy (CBox.mul_check _ _)
lemma RBox.contains_scale {a : RBox} {x : ℝ} (hx : a.Contains x) (m n : ℤ) (hn : 0 < n) :
    (a.scale m n).Contains (((m:ℝ)/n)*x) := RBox.scale_contains hx (RBox.scale_check _ _ _ hn)
lemma CBox.contains_scale {a : CBox} {z : ℂ} (hz : a.Contains z) (m n : ℤ) (hn : 0 < n) :
    (a.scale m n).Contains (((m:ℂ)/n)*z) := CBox.scale_contains hz (CBox.scale_check _ _ _ hn)
lemma CBox.contains_horner {a : CBox} {z : ℂ} (hz : a.Contains z) (k n : ℕ) :
    (a.horner k n).Contains (expHorner z k n) := by
  induction n generalizing k with
  | zero =>
    simpa [CBox.horner,expHorner] using CBox.contains_rat 1 (k.factorial:ℤ) 0 1
      (by exact_mod_cast Nat.factorial_pos k) (by norm_num)
  | succ n ih =>
    exact horner_step hz (ih (k+1)) (CBox.rat_check _ _ _ _
      (by exact_mod_cast Nat.factorial_pos k) (by norm_num))
      (CBox.mul_check _ _) (CBox.add_check _ _)
lemma CBox.contains_squareIter {a : CBox} {z : ℂ} (hz : a.Contains z) (k : ℕ) :
    (a.squareIter k).Contains (z^(2^k)) := by
  induction k with
  | zero => simpa [CBox.squareIter] using hz
  | succ k ih =>
    rw [pow_succ,show 2^k*2=2^k+2^k from by omega,pow_add]
    exact CBox.contains_mul ih ih
lemma CBox.contains_exp {a : CBox} {z : ℂ} (hz : a.Contains z) (k : ℕ)
    (hn : (a.scale 1 (2^k)).NormCheck 1) : (a.exp k).Contains (Complex.exp z) := by
  have he := exp_from_horner (CBox.contains_scale hz 1 (2^k) (by positivity)) hn
    (CBox.contains_horner (CBox.contains_scale hz 1 (2^k) (by positivity)) 0 32)
    (CBox.widen_check _ 1)
  have hs := CBox.contains_squareIter he k
  rw [← Complex.exp_nat_mul] at hs
  convert hs using 1
  congr 1
  push_cast
  field_simp


lemma CBox.contains_inv {a : CBox} {z : ℂ} (hz : a.Contains z)
    (hi : ((a.re.mul a.re).add (a.im.mul a.im)).InvCheck
      ((a.re.mul a.re).add (a.im.mul a.im)).inv) :
    a.inv.Contains z⁻¹ :=
  CBox.inv_checked hz (RBox.mul_check _ _) (RBox.mul_check _ _) (RBox.add_check _ _)
    hi (RBox.mul_check _ _) (RBox.mul_check _ _)

def CBox.powBin (a : CBox) : ℕ → ℕ → CBox
  | 0, _ => CBox.rat 1 1 0 1
  | k+1, n =>
    let b := a.powBin k (n/2)
    let b2 := b.mul b
    if n%2 = 0 then b2 else b2.mul a

lemma CBox.contains_powBin {a : CBox} {z : ℂ} (hz : a.Contains z) (k n : ℕ)
    (hn : n < 2^k) : (a.powBin k n).Contains (z^n) := by
  induction k generalizing n with
  | zero =>
    have : n=0 := by simpa using hn
    subst n
    simpa [CBox.powBin] using CBox.contains_rat 1 1 0 1 (by norm_num) (by norm_num)
  | succ k ih =>
    have hd : n/2 < 2^k := by rw [pow_succ] at hn; omega
    have he : n%2+2*(n/2)=n := Nat.mod_add_div n 2
    have hb := CBox.contains_mul (ih (n/2) hd) (ih (n/2) hd)
    rw [← pow_add] at hb
    dsimp only [CBox.powBin]
    split_ifs with h
    · convert hb using 1
      congr 1
      omega
    · have hh := CBox.contains_mul hb hz
      rw [← pow_succ] at hh
      convert hh using 1
      congr 1
      omega

lemma RBox.lower_bound {a : RBox} {x : ℝ} (hx : a.Contains x) {m n : ℤ}
    (hn : 0 < n) (h : precision*m < a.lo*n) : (m:ℝ)/n < x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h' : (precision:ℝ)*m < a.lo*n := by exact_mod_cast h
  rw [div_lt_iff₀ hn']
  apply (mul_lt_mul_iff_right₀ precision_pos).mp
  nlinarith only [hx.1,h',hn']
lemma RBox.upper_bound {a : RBox} {x : ℝ} (hx : a.Contains x) {m n : ℤ}
    (hn : 0 < n) (h : a.hi*n < precision*m) : x < (m:ℝ)/n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h' : (a.hi:ℝ)*n < precision*m := by exact_mod_cast h
  rw [lt_div_iff₀ hn']
  apply (mul_lt_mul_iff_right₀ precision_pos).mp
  nlinarith only [hx.2,h',hn']

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerIntervals

-- These are exactly lambda,z from fourier:frequencies, restricted to real t.
noncomputable def pointLambda (t : ℝ) : ℂ :=
  Complex.I / (((Real.sqrt 3/2:ℝ):ℂ) * ((t:ℂ)+Complex.I*(2/5:ℂ)))
noncomputable def pointZ (t : ℝ) : ℂ :=
  -(4/3:ℂ) / ((t:ℂ)+Complex.I*(2/5:ℂ)) - Complex.I*(2/5:ℂ)

structure PointBox where
  t : RBox
  lam : CBox
  z : CBox
  direct : CBox
  quarter : CBox
  deriving DecidableEq

def rcast (a : RBox) : CBox := ⟨a,⟨0,0⟩⟩
def piI : CBox := ⟨⟨0,0⟩,piBounds⟩
def denBox (a : RBox) : CBox := ⟨a,RBox.rat 2 5⟩
def lamDenBox (a : RBox) : CBox := (rcast bBounds).mul (denBox a)
def lamBox (a : RBox) : CBox := (CBox.rat 0 1 1 1).mul (lamDenBox a).inv
def zBox (a : RBox) : CBox := ((denBox a).inv.scale (-4) 3).add (CBox.rat 0 1 (-2) 5)
def directArgBox (a : RBox) : CBox := (piI.mul (rcast a)).neg
def quarterArgBox (a : RBox) : CBox := (piI.mul (zBox a)).scale 1 4

def CBox.GoodInv (a : CBox) : Prop :=
  ((a.re.mul a.re).add (a.im.mul a.im)).InvCheck
    ((a.re.mul a.re).add (a.im.mul a.im)).inv
instance (a : CBox) : Decidable a.GoodInv := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def PointBox.Check (a : RBox) : Prop :=
  (denBox a).GoodInv ∧ (lamDenBox a).GoodInv ∧
  ((directArgBox a).scale 1 8).NormCheck 1 ∧
  ((quarterArgBox a).scale 1 8).NormCheck 1
instance (a : RBox) : Decidable (PointBox.Check a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def PointBox.calc (a : RBox) : PointBox :=
  ⟨a,lamBox a,zBox a,(directArgBox a).exp 3,(quarterArgBox a).exp 3⟩

def PointBox.Contains (a : PointBox) (x : ℝ) : Prop :=
  a.t.Contains x ∧ a.lam.Contains (pointLambda x) ∧ a.z.Contains (pointZ x) ∧
  a.direct.Contains (Complex.exp (-Complex.I*Real.pi*x)) ∧
  a.quarter.Contains (Complex.exp (Complex.I*Real.pi*pointZ x/4))

lemma rcast_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (rcast a).Contains (x:ℂ) := CBox.ofReal_contains hx
lemma piI_contains : piI.Contains (Complex.I*Real.pi) := by
  constructor
  · norm_num [CBox.Contains,RBox.Contains,piI]
  · simpa [piI] using piBounds_contains
lemma denBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (denBox a).Contains ((x:ℂ)+Complex.I*(2/5:ℂ)) := by
  constructor
  · simpa [denBox] using hx
  · simpa [denBox] using RBox.contains_rat 2 5 (by norm_num)
lemma lamDenBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (lamDenBox a).Contains (((Real.sqrt 3/2:ℝ):ℂ)*((x:ℂ)+Complex.I*(2/5:ℂ))) :=
  CBox.contains_mul (rcast_contains bBounds_contains) (denBox_contains hx)
lemma lamBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (lamDenBox a).GoodInv) : (lamBox a).Contains (pointLambda x) := by
  have hI : (CBox.rat 0 1 1 1).Contains Complex.I := by
    simpa using CBox.contains_rat 0 1 1 1 (by norm_num) (by norm_num)
  simpa only [lamBox,pointLambda,div_eq_mul_inv] using
    CBox.contains_mul hI (CBox.contains_inv (lamDenBox_contains hx) hi)
lemma zBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (denBox a).GoodInv) : (zBox a).Contains (pointZ x) := by
  have hc : (CBox.rat 0 1 (-2) 5).Contains (-Complex.I*(2/5:ℂ)) := by
    convert CBox.contains_rat 0 1 (-2) 5 (by norm_num) (by norm_num) using 1; ring
  have hh := CBox.contains_add
    (CBox.contains_scale (CBox.contains_inv (denBox_contains hx) hi) (-4) 3 (by norm_num)) hc
  unfold zBox
  convert hh using 1
  simp only [pointZ,div_eq_mul_inv,sub_eq_add_neg]
  ring
lemma directArgBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (directArgBox a).Contains (-Complex.I*Real.pi*x) := by
  simpa only [directArgBox,neg_mul] using CBox.neg_contains (CBox.contains_mul piI_contains (rcast_contains hx))
lemma quarterArgBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (denBox a).GoodInv) :
    (quarterArgBox a).Contains (Complex.I*Real.pi*pointZ x/4) := by
  have hh := CBox.contains_scale (CBox.contains_mul piI_contains (zBox_contains hx hi)) 1 4 (by norm_num)
  unfold quarterArgBox
  convert hh using 1; ring

lemma PointBox.calc_contains {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hc : PointBox.Check a) : (PointBox.calc a).Contains x := by
  exact ⟨hx,lamBox_contains hx hc.2.1,zBox_contains hx hc.1,
    CBox.contains_exp (directArgBox_contains hx) 3 hc.2.2.1,
    CBox.contains_exp (quarterArgBox_contains hx hc.1) 3 hc.2.2.2⟩

end SharpPlanar.IntegerIntervals

end OAI
