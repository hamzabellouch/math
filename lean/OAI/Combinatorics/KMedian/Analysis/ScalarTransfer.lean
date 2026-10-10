import Mathlib

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def bit (s : Bool) : ℝ := if s then 1 else 0
noncomputable def d (s : Bool) : ℝ := if s then 2/5 else 13/25
noncomputable def hh (s : Bool) : ℝ := 8/5 + (2/5) * d s
noncomputable def uZero (s : Bool) : ℝ := d s / hh s
noncomputable def uOne (s : Bool) : ℝ := (2-bit s)*(1+d s)/(2*hh s)
noncomputable def c (p : ℝ) (s : Bool) : ℝ := 1-bit s*p
noncomputable def N (p k : ℝ) (s : Bool) : ℝ := c p s-(1-bit s)*k
noncomputable def ell (p a x : ℝ) (s : Bool) : ℝ := c p s+1-a+bit s*p*x
noncomputable def T1 (p x : ℝ) : ℝ :=
  1-p-(28/25)*p*(1+x)+(2/5)*p^2*(1-x)*(1+x)
noncomputable def T2 (p x : ℝ) : ℝ :=
  ((1-p)^2-(19/50)*p*(1-x)+p*x)*(1+x)-2*x*(1-p)
noncomputable def Q0 (p a k W : ℝ) (s : Bool) : ℝ :=
  N p k s - d s*a + p*W*(hh s*W-2*d s)
noncomputable def Q1 (p a k x : ℝ) (s : Bool) : ℝ :=
  N p k s-(2-bit s)*p*x-d s*(c p s*p-ell p a x s)-hh s*p*(uOne s)^2
noncomputable def Y (p k x : ℝ) (s : Bool) : ℝ :=
  N p k s-p*((2-bit s)*x+(2-bit s)^2/(32/5))
noncomputable def Yprime (p k x : ℝ) : ℝ :=
  1-k+p*((8/5)*(1-x)^2-2)

theorem mul_abs_bound {a b e K : ℝ} (ha : |a| ≤ e) (hb : |b| ≤ K) :
    |a*b| ≤ e*K := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) ((abs_nonneg a).trans ha)

private theorem add_product_abs_bound {a b c d e K L : ℝ}
    (ha : |a| ≤ e) (hb : |b| ≤ K) (hc : |c| ≤ 2*e) (hd : |d| ≤ L) :
    |a*b+c*d| ≤ (K+2*L)*e := by
  calc
    |a*b+c*d| ≤ |a*b|+|c*d| := abs_add_le _ _
    _ ≤ e*K+(2*e)*L := add_le_add (mul_abs_bound ha hb) (mul_abs_bound hc hd)
    _ = (K+2*L)*e := by ring

theorem T1_error {p q x e : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (he : |p-q| ≤ e) : |T1 p x-T1 q x| ≤ 5*e := by
  have hxprod0 : 0 ≤ (1-x)*(1+x) := mul_nonneg (by linarith) (by linarith)
  have hxprod1 : (1-x)*(1+x) ≤ 1 := by nlinarith [sq_nonneg x]
  have hprod := mul_le_mul (show p+q ≤ 1 by linarith) hxprod1 hxprod0 (by norm_num : (0:ℝ) ≤ 1)
  have hprod0 : 0 ≤ (p+q)*((1-x)*(1+x)) := mul_nonneg (by linarith) hxprod0
  have hc : |-1-(28/25)*(1+x)+(2/5)*(p+q)*((1-x)*(1+x))| ≤ 5 := by
    rw [abs_le]
    constructor <;> nlinarith only [hx0, hx, hprod, hprod0]
  have hid : T1 p x-T1 q x =
      (p-q)*(-1-(28/25)*(1+x)+(2/5)*(p+q)*((1-x)*(1+x))) := by
    unfold T1
    ring
  rw [hid]
  have h := mul_abs_bound he hc
  simpa only [mul_comm e] using h

theorem T2_error {p q x e : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (he : |p-q| ≤ e) : |T2 p x-T2 q x| ≤ 6*e := by
  let z := p+q-2-(19/50)*(1-x)+x
  have hz0 : -3 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 0 := by dsimp [z]; linarith
  have hzx0 : -6 ≤ z*(1+x) := by
    have h := mul_nonneg (show 0 ≤ z+3 by linarith) (show 0 ≤ 1+x by linarith)
    nlinarith
  have hzx1 : z*(1+x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hz1 (by linarith)
  have hc : |z*(1+x)+2*x| ≤ 6 := by rw [abs_le]; constructor <;> linarith
  have hid : T2 p x-T2 q x = (p-q)*(z*(1+x)+2*x) := by
    unfold T2
    dsimp only [z]
    ring
  rw [hid]
  have h := mul_abs_bound he hc
  simpa only [mul_comm e] using h

theorem Q0_error {p q a b k W e : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1)
    (hpq : |p-q| ≤ e) (hab : |a-b| ≤ 2*e) (s : Bool) :
    |Q0 p a k W s-Q0 q b k W s| ≤ 6*e := by
  have hWs : W^2 ≤ 1 := by nlinarith
  have hc : |-bit s+W*(hh s*W-2*d s)| ≤ 4 := by
    rw [abs_le]
    constructor <;> cases s <;> norm_num [bit, hh, d] <;> nlinarith [sq_nonneg W]
  have hd : |-d s| ≤ 1 := by cases s <;> norm_num [d]
  have hid : Q0 p a k W s-Q0 q b k W s =
      (p-q)*(-bit s+W*(hh s*W-2*d s))+(a-b)*(-d s) := by
    unfold Q0 N c
    ring
  rw [hid]
  calc
    _ ≤ (4+2*1)*e := add_product_abs_bound hpq hc hab hd
    _ = 6*e := by ring

theorem Q1_error {p q a b k x e : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hpq : |p-q| ≤ e) (hab : |a-b| ≤ 2*e) (s : Bool) :
    |Q1 p a k x s-Q1 q b k x s| ≤ 8*e := by
  let z := -bit s-(2-bit s)*x-d s*(1+bit s-bit s*x)+
    d s*bit s*(p+q)-hh s*(uOne s)^2
  have hz : |z| ≤ 6 := by
    rw [abs_le]
    constructor <;> cases s <;> norm_num [z, bit, d, hh, uOne] <;> linarith
  have hd : |-d s| ≤ 1 := by cases s <;> norm_num [d]
  have hid : Q1 p a k x s-Q1 q b k x s = (p-q)*z+(a-b)*(-d s) := by
    dsimp only [Q1, N, c, ell]
    dsimp only [z]
    ring
  rw [hid]
  calc
    _ ≤ (6+2*1)*e := add_product_abs_bound hpq hz hab hd
    _ = 8*e := by ring

theorem Y_error {p q k x e : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hpq : |p-q| ≤ e) (s : Bool) : |Y p k x s-Y q k x s| ≤ 3*e := by
  have hz : |-bit s-((2-bit s)*x+(2-bit s)^2/(32/5))| ≤ 3 := by
    rw [abs_le]
    constructor <;> cases s <;> norm_num [bit] <;> linarith
  have hid : Y p k x s-Y q k x s =
      (p-q)*(-bit s-((2-bit s)*x+(2-bit s)^2/(32/5))) := by
    unfold Y N c
    ring
  rw [hid]
  have h := mul_abs_bound hpq hz
  simpa only [mul_comm e] using h

theorem Yprime_error {p q k x e : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hpq : |p-q| ≤ e) : |Yprime p k x-Yprime q k x| ≤ 2*e := by
  have hs : (1-x)^2 ≤ 1 := by nlinarith
  have hz : |(8/5)*(1-x)^2-2| ≤ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (1-x)]
  have hid : Yprime p k x-Yprime q k x = (p-q)*((8/5)*(1-x)^2-2) := by
    unfold Yprime
    ring
  rw [hid]
  have h := mul_abs_bound hpq hz
  simpa only [mul_comm e] using h

end MetricKMedian.ScalarTransfer


end
end

end OAI
