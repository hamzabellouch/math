import Mathlib
import OAI.Probability.SKRatio.FiniteChain.Spin

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace SKRatio.TwoSpin

private def polynomialSum (l : List (ℤ × ℕ × ℕ × ℕ)) (a b t : ℝ) : ℝ :=
  (l.map fun c => (c.1 : ℝ)*a^c.2.1*b^c.2.2.1*t^c.2.2.2).sum

private lemma polynomialSum_bound (l : List (ℤ × ℕ × ℕ × ℕ)) {a b t : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |t| ≤ 1) :
    |polynomialSum l a b t| ≤ (l.map fun c => |(c.1 : ℝ)|).sum := by
  have hm (c : ℤ × ℕ × ℕ × ℕ) :
      |(c.1 : ℝ)*a^c.2.1*b^c.2.2.1*t^c.2.2.2| ≤ |(c.1 : ℝ)| := by
    simp only [abs_mul, abs_pow]
    have ha' : |a|^c.2.1 ≤ 1 := pow_le_one₀ (abs_nonneg _) ha
    have hb' : |b|^c.2.2.1 ≤ 1 := pow_le_one₀ (abs_nonneg _) hb
    have ht' : |t|^c.2.2.2 ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
    calc
      _ ≤ |(c.1 : ℝ)| * 1*1*1 := by gcongr
      _ = _ := by ring
  induction l with
  | nil => simp [polynomialSum]
  | cons c l ih =>
    simp only [polynomialSum, List.map_cons, List.sum_cons] at ih ⊢
    exact (abs_add_le _ _).trans (add_le_add (hm c) ih)

private lemma affine_factor {a t : ℝ} (ha : |a| ≤ 1) (ht : |t| ≤ 1/4) :
    (1/2:ℝ) ≤ 1+a*t := by
  have h : |a*t| ≤ 1/4 := by
    rw [abs_mul]
    calc |a| * |t| ≤ 1*(1/4) := by gcongr
         _ = _ := by ring
  linarith [(abs_le.mp h).1]

private def rationalCoefficient (a b t : ℝ) : ℝ :=
  (1-t)/((1+a*t)*(1+b*t)) +
  (t+2*t^2*((a+t)/(1+a*t))*((b+t)/(1+b*t)))*
    ((1-t^2)*(1+a)*(1+b)*(1+t))/((1+a*t)^2*(1+b*t)^2)

private def leadingCoefficient (a b t : ℝ) : ℝ :=
  1+a*b*t+(1-a^2-b^2+2*a^2*b^2)*t^2

private def remainder0 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-1, 0, 0, 0),
   (-1, 0, 1, 0),
   (2, 0, 2, 0),
   (2, 0, 3, 0),
   (-1, 1, 0, 0),
   (4, 1, 1, 0),
   (2, 1, 2, 0),
   (-3, 1, 3, 0),
   (2, 2, 0, 0),
   (2, 2, 1, 0),
   (-6, 2, 2, 0),
   (-6, 2, 3, 0),
   (2, 3, 0, 0),
   (-3, 3, 1, 0),
   (-6, 3, 2, 0)]

private def remainder1 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(1, 0, 0, 1),
   (2, 0, 1, 1),
   (-2, 0, 2, 1),
   (3, 0, 4, 1),
   (2, 1, 0, 1),
   (-7, 1, 1, 1),
   (-2, 1, 2, 1),
   (6, 1, 3, 1),
   (-1, 1, 4, 1),
   (-2, 2, 0, 1),
   (-2, 2, 1, 1),
   (-3, 2, 2, 1),
   (-9, 2, 3, 1),
   (-6, 2, 4, 1),
   (6, 3, 1, 1),
   (-9, 3, 2, 1),
   (-18, 3, 3, 1),
   (3, 4, 0, 1),
   (-1, 4, 1, 1),
   (-6, 4, 2, 1)]

private def remainder2 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(2, 0, 0, 2),
   (-1, 0, 1, 2),
   (-3, 0, 2, 2),
   (-1, 0, 3, 2),
   (1, 0, 5, 2),
   (-1, 1, 0, 2),
   (-7, 1, 1, 2),
   (-15, 1, 2, 2),
   (9, 1, 4, 2),
   (-3, 2, 0, 2),
   (-15, 2, 1, 2),
   (-4, 2, 2, 2),
   (7, 2, 3, 2),
   (-3, 2, 4, 2),
   (-2, 2, 5, 2),
   (-1, 3, 0, 2),
   (7, 3, 2, 2),
   (-9, 3, 3, 2),
   (-18, 3, 4, 2),
   (9, 4, 1, 2),
   (-3, 4, 2, 2),
   (-18, 4, 3, 2),
   (1, 5, 0, 2),
   (-2, 5, 2, 2)]

private def remainder3 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-2, 0, 0, 3),
   (-4, 0, 1, 3),
   (-2, 0, 2, 3),
   (-4, 1, 0, 3),
   (-7, 1, 1, 3),
   (-3, 1, 2, 3),
   (-3, 1, 3, 3),
   (3, 1, 5, 3),
   (-2, 2, 0, 3),
   (-3, 2, 1, 3),
   (-10, 2, 2, 3),
   (9, 2, 4, 3),
   (-3, 3, 1, 3),
   (5, 3, 3, 3),
   (-3, 3, 4, 3),
   (-6, 3, 5, 3),
   (9, 4, 2, 3),
   (-3, 4, 3, 3),
   (-18, 4, 4, 3),
   (3, 5, 1, 3),
   (-6, 5, 3, 3)]

private def remainder4 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-2, 0, 0, 4),
   (-2, 0, 1, 4),
   (-2, 1, 0, 4),
   (-2, 1, 1, 4),
   (-3, 2, 3, 4),
   (3, 2, 5, 4),
   (-3, 3, 2, 4),
   (3, 3, 4, 4),
   (3, 4, 3, 4),
   (-1, 4, 4, 4),
   (-6, 4, 5, 4),
   (3, 5, 2, 4),
   (-6, 5, 4, 4)]

private def remainder5 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-1, 3, 3, 5),
   (1, 3, 5, 5),
   (1, 5, 3, 5),
   (-2, 5, 5, 5)]

private def remainder (a b t : ℝ) : ℝ :=
  polynomialSum remainder0 a b t +
  polynomialSum remainder1 a b t +
  polynomialSum remainder2 a b t +
  polynomialSum remainder3 a b t +
  polynomialSum remainder4 a b t +
  polynomialSum remainder5 a b t

private lemma remainder_bound {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1) : |remainder a b t| ≤ 428 := by
  have h0 : |polynomialSum remainder0 a b t| ≤ 43 := by
    have h := polynomialSum_bound remainder0 ha hb ht
    norm_num [remainder0] at h ⊢
    exact h
  have h1 : |polynomialSum remainder1 a b t| ≤ 91 := by
    have h := polynomialSum_bound remainder1 ha hb ht
    norm_num [remainder1] at h ⊢
    exact h
  have h2 : |polynomialSum remainder2 a b t| ≤ 142 := by
    have h := polynomialSum_bound remainder2 ha hb ht
    norm_num [remainder2] at h ⊢
    exact h
  have h3 : |polynomialSum remainder3 a b t| ≤ 108 := by
    have h := polynomialSum_bound remainder3 ha hb ht
    norm_num [remainder3] at h ⊢
    exact h
  have h4 : |polynomialSum remainder4 a b t| ≤ 39 := by
    have h := polynomialSum_bound remainder4 ha hb ht
    norm_num [remainder4] at h ⊢
    exact h
  have h5 : |polynomialSum remainder5 a b t| ≤ 5 := by
    have h := polynomialSum_bound remainder5 ha hb ht
    norm_num [remainder5] at h ⊢
    exact h
  have h01 := (abs_add_le _ _).trans (add_le_add h0 h1)
  have h02 := (abs_add_le _ _).trans (add_le_add h01 h2)
  have h03 := (abs_add_le _ _).trans (add_le_add h02 h3)
  have h04 := (abs_add_le _ _).trans (add_le_add h03 h4)
  have h05 := (abs_add_le _ _).trans (add_le_add h04 h5)
  norm_num at h05
  exact h05

private lemma numerator_certificate (a b t : ℝ) :
    (1-t)*(1+a*t)^2*(1+b*t)^2 +
      (t*(1+a*t)*(1+b*t)+2*t^2*(a+t)*(b+t))*
        ((1-t^2)*(1+a)*(1+b)*(1+t)) -
      leadingCoefficient a b t*((1+a*t)^3*(1+b*t)^3) =
      t^3*remainder a b t := by
  simp only [remainder, leadingCoefficient, polynomialSum,
    remainder0,remainder1,remainder2,remainder3,remainder4,remainder5,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Int.cast_ofNat, Int.cast_neg]
  ring

private lemma rational_remainder {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1/4) :
    rationalCoefficient a b t - leadingCoefficient a b t =
      t^3*remainder a b t/((1+a*t)^3*(1+b*t)^3) := by
  have hA : 1+a*t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (affine_factor ha ht))
  have hB : 1+b*t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (affine_factor hb ht))
  have hc := numerator_certificate a b t
  have hA' : 1+t*a ≠ 0 := by simpa [mul_comm] using hA
  have hB' : 1+t*b ≠ 0 := by simpa [mul_comm] using hB
  unfold rationalCoefficient
  field_simp [hA, hB, hA', hB']
  linear_combination hc

private lemma rational_remainder_bound {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1/4) :
    |rationalCoefficient a b t - leadingCoefficient a b t| ≤ 30000*|t|^3 := by
  have hA := affine_factor ha ht
  have hB := affine_factor hb ht
  have hAp : 0 < 1+a*t := lt_of_lt_of_le (by norm_num) hA
  have hBp : 0 < 1+b*t := lt_of_lt_of_le (by norm_num) hB
  have hd : (1/64:ℝ) ≤ (1+a*t)^3*(1+b*t)^3 := by
    calc (1/64:ℝ) = (1/2:ℝ)^3*(1/2:ℝ)^3 := by norm_num
         _ ≤ (1+a*t)^3*(1+b*t)^3 := by gcongr
  have hdp : 0 < (1+a*t)^3*(1+b*t)^3 := mul_pos (pow_pos hAp 3) (pow_pos hBp 3)
  rw [rational_remainder ha hb ht, abs_div, abs_mul, abs_pow,
    abs_of_pos hdp, div_le_iff₀ hdp]
  have hr := remainder_bound ha hb (ht.trans (by norm_num))
  calc
    |t|^3*|remainder a b t| ≤ |t|^3*428 := by gcongr
    _ ≤ 30000*|t|^3*(1/64) := by nlinarith [pow_nonneg (abs_nonneg t) 3]
    _ ≤ 30000*|t|^3*((1+a*t)^3*(1+b*t)^3) := by gcongr

def pairBaseMass (a b : ℝ) (x y : Bool) : ℝ :=
  (1+a*spinValue x)*(1+b*spinValue y)/4

def pairMean (a b : ℝ) (F : Bool→Bool→ℝ) : ℝ :=
  ∑ x,∑ y,pairBaseMass a b x y*F x y

lemma pairMean_explicit (a b : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b F=((1-a)*(1-b)*F false false+(1-a)*(1+b)*F false true+
      (1+a)*(1-b)*F true false+(1+a)*(1+b)*F true true)/4 := by
  simp only [pairMean,Fintype.sum_bool,pairBaseMass,spinValue,Bool.false_eq_true,
    ite_false,ite_true,mul_neg_one,mul_one]
  ring

lemma pairBaseMass_nonneg {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (x y : Bool) :
    0 ≤ pairBaseMass a b x y := by
  have h₁ := abs_le.mp ha
  have h₂ := abs_le.mp hb
  unfold pairBaseMass
  cases x <;> cases y <;> simp only [spinValue,Bool.false_eq_true,ite_false,ite_true,mul_one,mul_neg_one] <;>
    exact div_nonneg (mul_nonneg (by linarith only [h₁.1,h₁.2]) (by linarith only [h₂.1,h₂.2])) (by norm_num)

lemma pairMean_mono {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    {F G : Bool→Bool→ℝ} (h : ∀ x y,F x y ≤ G x y) : pairMean a b F ≤ pairMean a b G := by
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  exact mul_le_mul_of_nonneg_left (h x y) (pairBaseMass_nonneg ha hb x y)

lemma pairMean_add (a b : ℝ) (F G : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>F x y+G x y)=pairMean a b F+pairMean a b G := by
  simp only [pairMean,mul_add,Finset.sum_add_distrib]

lemma pairMean_sub (a b : ℝ) (F G : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>F x y-G x y)=pairMean a b F-pairMean a b G := by
  simp only [pairMean,mul_sub,Finset.sum_sub_distrib]

lemma pairMean_mul (a b c : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>c*F x y)=c*pairMean a b F := by
  simp only [pairMean,Finset.mul_sum,mul_left_comm]

lemma abs_pairMean_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (F : Bool→Bool→ℝ) : |pairMean a b F| ≤ pairMean a b (fun x y=>|F x y|) := by
  unfold pairMean
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro y _
  rw [abs_mul,abs_of_nonneg (pairBaseMass_nonneg ha hb x y)]

lemma pair_gradient_mean (a b p s r : ℝ) :
    pairMean a b (fun x y=>(p+r*(spinValue y-b))*(s+r*(spinValue x-a)))=p*s := by
  rw [pairMean_explicit]
  simp only [spinValue,Bool.false_eq_true,ite_false,ite_true]
  ring

lemma pair_gradient_square (a b p r : ℝ) :
    pairMean a b (fun _ y=>(p+r*(spinValue y-b))^2)=p^2+(1-b^2)*r^2 := by
  rw [pairMean_explicit]
  simp only [spinValue,Bool.false_eq_true,ite_false,ite_true]
  ring

lemma pairMean_swap (a b : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b F=pairMean b a (fun x y=>F y x) := by
  rw [pairMean_explicit,pairMean_explicit]
  ring

lemma pair_second_gradient_square (a b s r : ℝ) :
    pairMean a b (fun x _=>(s+r*(spinValue x-a))^2)=s^2+(1-a^2)*r^2 := by
  rw [pairMean_swap]
  exact pair_gradient_square b a s r

lemma pair_factor_control {u z : ℝ} (hu : |u| ≤ 1/4) (hz : |z| ≤ 1) :
    (1/2:ℝ) ≤ 1+u*z ∧ 1+u*z ≤ 2 ∧ |(1+u*z)-1| ≤ |u| := by
  have hh : |u*z| ≤ |u| := by rw [abs_mul];exact (mul_le_mul_of_nonneg_left hz (abs_nonneg u)).trans_eq (mul_one _)
  have hb := abs_le.mp hh
  constructor
  · linarith
  constructor
  · linarith
  simpa only [add_sub_cancel_left] using hh

lemma pair_square_factor_control {u : ℝ} (hu : |u| ≤ 1/4) :
    (1/2:ℝ) ≤ 1-u^2 ∧ 1-u^2 ≤ 2 ∧ |(1-u^2)-1| ≤ |u| := by
  have hs : u^2 ≤ |u| := by nlinarith [sq_abs u,abs_nonneg u]
  have h0 := sq_nonneg u
  constructor
  · linarith
  constructor
  · linarith
  rw [sub_sub_cancel_left,abs_neg,abs_of_nonneg h0]
  exact hs

lemma abs_mul_le_one_pair {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x*y| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_mul hx hy (abs_nonneg _) (by norm_num)).trans_eq (by ring)

def pairDensity (a b u : ℝ) (x y : Bool) : ℝ :=
  (1+u*spinValue x*spinValue y)/(1+u*a*b)

def pairInterMean (a b u : ℝ) (F : Bool→Bool→ℝ) : ℝ :=
  pairMean a b (fun x y=>pairDensity a b u x y*F x y)

def pairResidual (a u : ℝ) (x y : Bool) : ℝ :=
  (spinValue x-a)*(1-u*spinValue x*spinValue y)/(1+u*a*spinValue y)

def pairVariance (a u : ℝ) (y : Bool) : ℝ :=
  (1-a^2)*(1-u^2)/(1+u*a*spinValue y)^2

def pairGrad₁ (b p r : ℝ) (y : Bool) : ℝ := p+r*(spinValue y-b)

def pairGrad₂ (a s r : ℝ) (x : Bool) : ℝ := s+r*(spinValue x-a)

lemma pairSign_abs (x : Bool) : |spinValue x|=1 := by cases x <;> norm_num [spinValue]

lemma pairSign_sq (x : Bool) : spinValue x^2=1 := by cases x <;> norm_num [spinValue]

lemma pairDenominator_pos {u a b : ℝ} (hu : |u| ≤ 1/4) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 < 1+u*a*b := by
  have hh := (pair_factor_control hu (abs_mul_le_one_pair ha hb)).1
  rw [← mul_assoc] at hh
  linarith only [hh]

lemma pair_variance_nonneg {a u : ℝ} (ha : |a| ≤ 1) (hu : |u| ≤ 1/4) (y : Bool) :
    0 ≤ pairVariance a u y := by
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hh := (pair_square_factor_control hu).1
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr ha2) (by linarith only [hh])) (sq_nonneg _)

lemma pair_density_nonneg {a b u : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hu : |u| ≤ 1/4) (x y : Bool) : 0 ≤ pairDensity a b u x y := by
  exact div_nonneg (pairDenominator_pos hu (pairSign_abs x).le (pairSign_abs y).le).le
    (pairDenominator_pos hu ha hb).le

lemma pair_density_variance_lower {a b u : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) (x y : Bool) :
    (1-a^2)/32 ≤ pairDensity a b u x y*pairVariance a u y := by
  have hn : 1/2 ≤ 1+u*spinValue x*spinValue y := by
    simpa only [mul_assoc] using (pair_factor_control hu (abs_mul_le_one_pair (pairSign_abs x).le (pairSign_abs y).le)).1
  have hs := (pair_square_factor_control hu).1
  have hd₀ := pair_factor_control hu (abs_mul_le_one_pair ha hb)
  have hd₁ := pair_factor_control hu (abs_mul_le_one_pair ha (pairSign_abs y).le)
  have hd02 : 1+u*a*b ≤ 2 := by simpa only [mul_assoc] using hd₀.2.1
  have hd12 : 1+u*a*spinValue y ≤ 2 := by simpa only [mul_assoc] using hd₁.2.1
  have hd10 : 0 ≤ 1+u*a*spinValue y := (pairDenominator_pos hu ha (pairSign_abs y).le).le
  have hd00 := pairDenominator_pos hu ha hb
  have hdd : 0 < (1+u*a*b)*(1+u*a*spinValue y)^2 := mul_pos hd00 (sq_pos_of_pos (pairDenominator_pos hu ha (pairSign_abs y).le))
  have hd : (1+u*a*b)*(1+u*a*spinValue y)^2 ≤ 8 := by
    have hh : (1+u*a*spinValue y)^2 ≤ 4 := by nlinarith only [hd12,hd10]
    nlinarith only [mul_le_mul hd02 hh (sq_nonneg (1+u*a*spinValue y)) (by norm_num : (0:ℝ) ≤ 2)]
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hA := sub_nonneg.mpr ha2
  have hn' : 1/4 ≤ (1+u*spinValue x*spinValue y)*(1-u^2) := by
    nlinarith only [mul_le_mul hn hs (by norm_num : (0:ℝ) ≤ 1/2) (by linarith only [hn] : 0 ≤ 1+u*spinValue x*spinValue y)]
  have he : pairDensity a b u x y*pairVariance a u y=
      ((1-a^2)*((1+u*spinValue x*spinValue y)*(1-u^2)))/
      ((1+u*a*b)*(1+u*a*spinValue y)^2) := by
    unfold pairDensity pairVariance
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  apply (le_div_iff₀ hdd).mpr
  have h₁ := mul_le_mul_of_nonneg_left hd (div_nonneg hA (by norm_num : (0:ℝ) ≤ 32))
  have h₂ := mul_le_mul_of_nonneg_left hn' hA
  nlinarith only [h₁,h₂]

lemma pair_energy_lower {a b u p r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-a^2)*(1-b^2)*p^2/32 ≤
      pairInterMean a b u (fun _x y=>pairVariance a u y*(pairGrad₁ b p r y)^2) := by
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hb2 : b^2 ≤ 1 := by nlinarith only [sq_abs b,abs_nonneg b,hb]
  have hA := sub_nonneg.mpr ha2
  have hB := sub_nonneg.mpr hb2
  have he := pairMean_mono ha hb (fun x y=>mul_le_mul_of_nonneg_right
    (pair_density_variance_lower ha hb hu x y) (sq_nonneg (pairGrad₁ b p r y)))
  simp only [pairMean_mul] at he
  have h₁ : pairMean a b (fun _ y=>(pairGrad₁ b p r y)^2)=p^2+(1-b^2)*r^2 :=
    pair_gradient_square a b p r
  rw [h₁] at he
  have h₂ : pairMean a b (fun x y=>pairDensity a b u x y*pairVariance a u y*(pairGrad₁ b p r y)^2)=
      pairInterMean a b u (fun _x y=>pairVariance a u y*(pairGrad₁ b p r y)^2) := by
    unfold pairInterMean
    congr 1
    funext x y
    ring
  rw [h₂] at he
  have h₃ : (1-a^2)*(1-b^2)*p^2 ≤ (1-a^2)*p^2 := by
    have hh := mul_le_mul_of_nonneg_right (show 1-b^2 ≤ 1 by linarith [sq_nonneg b])
      (mul_nonneg hA (sq_nonneg p))
    nlinarith only [hh]
  have h₄ : 0 ≤ (1-a^2)*(1-b^2)*r^2 := mul_nonneg (mul_nonneg hA hB) (sq_nonneg r)
  nlinarith only [he,h₃,h₄]

lemma pairInterMean_swap (a b u : ℝ) (F : Bool→Bool→ℝ) :
    pairInterMean a b u F=pairInterMean b a u (fun x y=>F y x) := by
  unfold pairInterMean
  rw [pairMean_swap]
  congr 1
  funext x y
  unfold pairDensity
  have he : (1+u*spinValue y*spinValue x)/(1+u*a*b)=
      (1+u*spinValue x*spinValue y)/(1+u*b*a) := by congr 1 <;> ring
  rw [he]

lemma pair_second_energy_lower {a b u s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-a^2)*(1-b^2)*s^2/32 ≤
      pairInterMean a b u (fun x _y=>pairVariance b u x*(pairGrad₂ a s r x)^2) := by
  rw [pairInterMean_swap]
  simpa only [mul_comm (1-a^2) (1-b^2),pairGrad₁,pairGrad₂] using
    (pair_energy_lower (p:=s) (r:=r) hb ha hu)

lemma pairInterMean_add (a b u : ℝ) (F G : Bool→Bool→ℝ) :
    pairInterMean a b u (fun x y=>F x y+G x y)=pairInterMean a b u F+pairInterMean a b u G := by
  unfold pairInterMean
  simp_rw [mul_add]
  exact pairMean_add a b _ _

lemma pairInterMean_nonneg {a b u : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4)
    {F : Bool→Bool→ℝ} (hF : ∀ x y,0 ≤ F x y) : 0 ≤ pairInterMean a b u F := by
  have hh := pairMean_mono ha hb (fun x y=>mul_nonneg (pair_density_nonneg ha hb hu x y) (hF x y))
  have he : pairMean a b (fun _ _=>(0:ℝ))=0 := by simp [pairMean]
  rwa [he] at hh

def pairConditionalMean (a t : ℝ) (y : Bool) : ℝ :=
  (a+t*spinValue y)/(1+t*a*spinValue y)

private def signedCoefficient (a b t : ℝ) (x y : Bool) : ℝ :=
  (spinValue x*spinValue y-t)/((1+t*a*spinValue y)*(1+t*b*spinValue x)) +
  (t+2*t^2*pairConditionalMean a t y*pairConditionalMean b t x)*
    ((1-t^2)*(1+a*spinValue x)*(1+b*spinValue y)*(1+t*spinValue x*spinValue y))/
      ((1+t*a*spinValue y)^2*(1+t*b*spinValue x)^2)

private lemma signedCoefficient_eq (a b t : ℝ) (x y : Bool) :
    signedCoefficient a b t x y = spinValue x*spinValue y *
      rationalCoefficient (a*spinValue x) (b*spinValue y) (t*spinValue x*spinValue y) := by
  unfold signedCoefficient rationalCoefficient pairConditionalMean
  cases x <;> cases y <;> norm_num [spinValue] <;> ring

private lemma leading_signs (a b t : ℝ) (x y : Bool) :
    leadingCoefficient (a*spinValue x) (b*spinValue y) (t*spinValue x*spinValue y) =
      leadingCoefficient a b t := by
  cases x <;> cases y <;> norm_num [spinValue,leadingCoefficient]

private lemma signedCoefficient_remainder {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1/4) (x y : Bool) :
    |signedCoefficient a b t x y-spinValue x*spinValue y*leadingCoefficient a b t| ≤
      30000*|t|^3 := by
  have h := rational_remainder_bound
    (a := a*spinValue x) (b := b*spinValue y) (t := t*spinValue x*spinValue y)
    (by simpa only [abs_mul,pairSign_abs,mul_one] using ha)
    (by simpa only [abs_mul,pairSign_abs,mul_one] using hb)
    (by simpa only [abs_mul,pairSign_abs,mul_one] using ht)
  rw [leading_signs] at h
  simpa only [signedCoefficient_eq,← mul_sub,abs_mul,pairSign_abs,one_mul,mul_one] using h

private lemma pairMean_const (a b c : ℝ) : pairMean a b (fun _ _ => c)=c := by
  rw [pairMean_explicit]
  ring

private lemma uniform_cross_gradient (a b p q r : ℝ) :
    pairMean 0 0 (fun x y => spinValue x*spinValue y*pairGrad₁ b p r y*pairGrad₂ a q r x)=r^2 := by
  rw [pairMean_explicit]
  simp only [pairGrad₁,pairGrad₂,spinValue,Bool.false_eq_true,ite_false,ite_true]
  ring

private lemma abs_pairGrad_product {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (p q r : ℝ) (x y : Bool) :
    |pairGrad₁ b p r y*pairGrad₂ a q r x| ≤ p^2+q^2+8*r^2 := by
  have hya : |spinValue y-b| ≤ 2 := by
    calc _ ≤ |spinValue y|+|b| := abs_sub _ _
         _ ≤ 2 := by rw [pairSign_abs];linarith
  have hxb : |spinValue x-a| ≤ 2 := by
    calc _ ≤ |spinValue x|+|a| := abs_sub _ _
         _ ≤ 2 := by rw [pairSign_abs];linarith
  have hx2 : (spinValue x-a)^2 ≤ 4 := by
    nlinarith only [hxb,abs_nonneg (spinValue x-a),sq_abs (spinValue x-a)]
  have hy2 : (spinValue y-b)^2 ≤ 4 := by
    nlinarith only [hya,abs_nonneg (spinValue y-b),sq_abs (spinValue y-b)]
  have h₁ : (pairGrad₁ b p r y)^2 ≤ 2*p^2+8*r^2 := by
    have h := mul_le_mul_of_nonneg_left hy2 (sq_nonneg r)
    dsimp [pairGrad₁]
    nlinarith only [sq_nonneg (p-r*(spinValue y-b)),h]
  have h₂ : (pairGrad₂ a q r x)^2 ≤ 2*q^2+8*r^2 := by
    have h := mul_le_mul_of_nonneg_left hx2 (sq_nonneg r)
    dsimp [pairGrad₂]
    nlinarith only [sq_nonneg (q-r*(spinValue x-a)),h]
  have h := sq_nonneg (|pairGrad₁ b p r y|-|pairGrad₂ a q r x|)
  rw [abs_mul]
  nlinarith only [h,h₁,h₂,sq_abs (pairGrad₁ b p r y),sq_abs (pairGrad₂ a q r x)]

private lemma leading_lower {a b t : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    1-|t| ≤ leadingCoefficient a b t := by
  have ha2 : a^2 ≤ 1 := by nlinarith [sq_abs a,abs_nonneg a]
  have hb2 : b^2 ≤ 1 := by nlinarith [sq_abs b,abs_nonneg b]
  have hq : 0 ≤ 1-a^2-b^2+2*a^2*b^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2),
      mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  have ht : |a*b*t| ≤ |t| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (abs_mul_le_one_pair ha hb) (abs_nonneg t)).trans_eq (one_mul _)
  have hs := mul_nonneg hq (sq_nonneg t)
  dsimp [leadingCoefficient]
  linarith only [(abs_le.mp ht).1,hs]

private lemma signed_mean_lower {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1/1000) (p q r : ℝ) :
    -30000*|t|^3*(p^2+q^2) ≤
      pairMean 0 0 (fun x y => pairGrad₁ b p r y*pairGrad₂ a q r x*signedCoefficient a b t x y) := by
  have ht4 : |t| ≤ 1/4 := ht.trans (by norm_num)
  have hpoint (x y : Bool) :
      -30000*|t|^3*(p^2+q^2+8*r^2) ≤
        pairGrad₁ b p r y*pairGrad₂ a q r x*
          (signedCoefficient a b t x y-spinValue x*spinValue y*leadingCoefficient a b t) := by
    have h := mul_le_mul (abs_pairGrad_product ha hb p q r x y)
      (signedCoefficient_remainder ha hb ht4 x y) (abs_nonneg _)
      (by positivity : 0 ≤ p^2+q^2+8*r^2)
    have hh := neg_abs_le (pairGrad₁ b p r y*pairGrad₂ a q r x*
      (signedCoefficient a b t x y-spinValue x*spinValue y*leadingCoefficient a b t))
    rw [abs_mul] at hh
    nlinarith only [h,hh]
  have he := pairMean_mono (a := 0) (b := 0) (by norm_num) (by norm_num) hpoint
  rw [pairMean_const] at he
  have hlead : pairMean 0 0 (fun x y => pairGrad₁ b p r y*pairGrad₂ a q r x*
      (spinValue x*spinValue y*leadingCoefficient a b t)) = leadingCoefficient a b t*r^2 := by
    calc
      _ = pairMean 0 0 (fun x y => leadingCoefficient a b t*
        (spinValue x*spinValue y*pairGrad₁ b p r y*pairGrad₂ a q r x)) := by
          congr 1;funext x y;ring
      _ = _ := by rw [pairMean_mul,uniform_cross_gradient]
  simp_rw [mul_sub] at he
  rw [pairMean_sub,hlead] at he
  have ht3 : |t|^3 ≤ 1/1000000000 := by
    calc _ ≤ (1/1000:ℝ)^3 := by gcongr
         _ = _ := by norm_num
  have hco : 0 ≤ leadingCoefficient a b t-240000*|t|^3 := by
    linarith only [leading_lower (t := t) ha hb,ht,ht3]
  nlinarith only [he,mul_nonneg hco (sq_nonneg r)]

private def pairPrefactor (a b t : ℝ) : ℝ :=
  (1-a^2)*(1-b^2)*(1-t^2)/(1+t*a*b)

private lemma residual_factorization (a b t : ℝ) (x y : Bool) :
    pairBaseMass a b x y*pairDensity a b t x y*pairResidual a t x y*pairResidual b t y x =
      pairPrefactor a b t / 4 *
        ((spinValue x*spinValue y-t)/((1+t*a*spinValue y)*(1+t*b*spinValue x))) := by
  unfold pairBaseMass pairDensity pairResidual pairPrefactor
  simp only [div_eq_mul_inv,mul_inv_rev]
  cases x <;> cases y <;> norm_num [spinValue] <;> ring

private lemma variance_factorization (a b t : ℝ) (x y : Bool) :
    pairBaseMass a b x y*pairDensity a b t x y*pairVariance a t y*pairVariance b t x =
      pairPrefactor a b t / 4 *
        ((1-t^2)*(1+a*spinValue x)*(1+b*spinValue y)*(1+t*spinValue x*spinValue y)/
          ((1+t*a*spinValue y)^2*(1+t*b*spinValue x)^2)) := by
  unfold pairBaseMass pairDensity pairVariance pairPrefactor
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

private lemma signed_factorization (a b t p q r : ℝ) :
    pairInterMean a b t (fun x y => pairResidual a t x y*pairGrad₁ b p r y*
      (pairResidual b t y x*pairGrad₂ a q r x)) +
    pairInterMean a b t (fun x y =>
      (t+2*t^2*pairConditionalMean a t y*pairConditionalMean b t x)*
        pairVariance a t y*pairVariance b t x*pairGrad₁ b p r y*pairGrad₂ a q r x) =
    pairPrefactor a b t * pairMean 0 0 (fun x y =>
      pairGrad₁ b p r y*pairGrad₂ a q r x*signedCoefficient a b t x y) := by
  unfold pairInterMean pairMean
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have h₁ := residual_factorization a b t x y
  have h₂ := variance_factorization a b t x y
  calc
    _ = (pairBaseMass a b x y*pairDensity a b t x y*pairResidual a t x y*pairResidual b t y x)*
        (pairGrad₁ b p r y*pairGrad₂ a q r x) +
      (pairBaseMass a b x y*pairDensity a b t x y*pairVariance a t y*pairVariance b t x)*
        ((t+2*t^2*pairConditionalMean a t y*pairConditionalMean b t x)*
          pairGrad₁ b p r y*pairGrad₂ a q r x) := by ring
    _ = _ := by
      rw [h₁,h₂]
      simp only [pairBaseMass,zero_mul,add_zero,one_mul]
      unfold signedCoefficient
      ring

private lemma pairPrefactor_bounds {a b t : ℝ} (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) (ht : |t| ≤ 1/4) :
    0 ≤ pairPrefactor a b t ∧ pairPrefactor a b t ≤ 2*(1-a^2)*(1-b^2) := by
  have ha2 : a^2 ≤ 1 := by nlinarith [sq_abs a,abs_nonneg a]
  have hb2 : b^2 ≤ 1 := by nlinarith [sq_abs b,abs_nonneg b]
  have hAB : 0 ≤ (1-a^2)*(1-b^2) := mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2)
  have hS := (pair_square_factor_control ht).1
  have hZ : (1/2:ℝ) ≤ 1+t*a*b := by
    simpa only [mul_assoc] using (pair_factor_control ht (abs_mul_le_one_pair ha hb)).1
  have hZp : 0 < 1+t*a*b := by linarith
  constructor
  · exact div_nonneg (mul_nonneg hAB (by linarith : 0 ≤ 1-t^2)) hZp.le
  · unfold pairPrefactor
    apply (div_le_iff₀ hZp).mpr
    have h := mul_le_mul_of_nonneg_left hZ hAB
    have hh := mul_nonneg hAB (sq_nonneg t)
    nlinarith only [h,hh]

theorem pair_cubic_signed_bound {a b t p q r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : |t| ≤ 1/1000) :
    -pairInterMean a b t (fun x y =>
      (t+2*t^2*pairConditionalMean a t y*pairConditionalMean b t x)*
        pairVariance a t y*pairVariance b t x*pairGrad₁ b p r y*pairGrad₂ a q r x) -
    1920000*|t|^3*pairInterMean a b t (fun x y =>
      pairVariance a t y*(pairGrad₁ b p r y)^2 +
      pairVariance b t x*(pairGrad₂ a q r x)^2) ≤
    pairInterMean a b t (fun x y => pairResidual a t x y*pairGrad₁ b p r y*
      (pairResidual b t y x*pairGrad₂ a q r x)) := by
  have ht4 : |t| ≤ 1/4 := ht.trans (by norm_num)
  have hp := pairPrefactor_bounds ha hb ht4
  have hQ := mul_le_mul_of_nonneg_left (signed_mean_lower ha hb ht p q r) hp.1
  rw [← signed_factorization] at hQ
  have he₁ := pair_energy_lower (p := p) (r := r) ha hb ht4
  have he₂ := pair_second_energy_lower (s := q) (r := r) ha hb ht4
  have hcost : pairPrefactor a b t*(p^2+q^2) ≤ 64*pairInterMean a b t (fun x y =>
      pairVariance a t y*(pairGrad₁ b p r y)^2+
      pairVariance b t x*(pairGrad₂ a q r x)^2) := by
    rw [pairInterMean_add]
    have h := mul_le_mul_of_nonneg_right hp.2 (add_nonneg (sq_nonneg p) (sq_nonneg q))
    nlinarith only [h,he₁,he₂]
  have h := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 30000*|t|^3 by positivity)
  nlinarith only [hQ,h]

end SKRatio.TwoSpin

end
end

end OAI
