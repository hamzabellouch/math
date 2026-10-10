import Mathlib
import OAI.Probability.SKRatio.Calculus.Interaction

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus

lemma field_replace_self {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) (i : Fin n) (b : Bool) :
    field J (replace x i b) i = field J x i := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : j = i
  · subst j; simp [hdiag]
  · simp [spin, replace, hi]

@[simp] lemma halfDiff_mean_self {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) (i : Fin n) : halfDiff i (fun y => mean J y i) x = 0 := by
  simp only [halfDiff, mean, field_replace_self J hdiag, sub_self, zero_div]

def plusSpin (n : ℕ) : Spin n := fun _ => true

theorem pointwise_gradient_identity {n : ℕ} (J : Interaction n)
    (hdiag : ∀ i, J i i = 0) (f : Observables n) (t : ℝ) :
    (1 / 2 : ℝ) * (deriv (fun s => unweightedGradient (semigroup J s f) (plusSpin n)) t -
      generator J (unweightedGradient (semigroup J t f)) (plusSpin n)) =
    -unweightedGradient (semigroup J t f) (plusSpin n) +
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        halfDiff i (semigroup J t f) (plusSpin n) *
          halfDiff i (fun y => mean J y j) (plusSpin n) *
            (halfDiff j (semigroup J t f) (plusSpin n) -
              2 * halfDiff i (halfDiff j (semigroup J t f)) (plusSpin n))) -
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        gradientWeight J (plusSpin n) j *
          (halfDiff i (halfDiff j (semigroup J t f)) (plusSpin n))^2) := by
  rw [(unweightedGradient_hasDerivAt J f (plusSpin n) t).deriv,
    unweightedGradient_commutator]
  simp only [spin, plusSpin, ↓reduceIte, mul_one]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), halfDiff_mean_self J hdiag,
      mul_zero, zero_mul, sub_zero]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), halfDiff_self]
    simp

open Real Set

lemma hasDerivAt_tanh (y : ℝ) : HasDerivAt tanh (1 - tanh y ^ 2) y := by
  convert! (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (cosh_pos y).ne' using 1
  · ext x
    exact tanh_eq_sinh_div_cosh x
  · rw [tanh_eq_sinh_div_cosh]
    field_simp

lemma tanh_lipschitz_abs (x y : ℝ) : |tanh x-tanh y| ≤ |x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (univ : Set ℝ)) => (hasDerivAt_tanh z).hasDerivWithinAt)
    (C := 1) (fun z _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (tanh_sq_lt_one z).le)]
      linarith [sq_nonneg (tanh z)]) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs,one_mul] using hh

lemma abs_tanh_le_abs (x : ℝ) : |tanh x| ≤ |x| := by
  simpa only [tanh_zero,sub_zero] using tanh_lipschitz_abs x 0

lemma tanh_cubic_error (x : ℝ) : |tanh x-x| ≤ |x|^3/3 := by
  let f : ℝ→ℝ := fun y=>y^3/3-y+tanh y
  have hd (y : ℝ) : HasDerivAt f (y^2-tanh y^2) y := by
    dsimp [f]
    convert! ((((hasDerivAt_id y).pow 3).div_const 3).sub (hasDerivAt_id y)).add (hasDerivAt_tanh y) using 1; simp only [id_eq]; ring
  have hm : Monotone f := monotone_of_deriv_nonneg (fun y=>(hd y).differentiableAt) (fun y=>by
    rw [(hd y).deriv]
    have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (abs_tanh_le_abs y)
    simpa only [sq_abs,sub_nonneg] using hs)
  have hp (y : ℝ) (hy : 0 ≤ y) : |tanh y-y| ≤ |y|^3/3 := by
    have h := hm hy
    have ht : tanh y ≤ y := (le_abs_self _).trans ((abs_tanh_le_abs y).trans_eq (abs_of_nonneg hy))
    rw [abs_of_nonpos (sub_nonpos.mpr ht),abs_of_nonneg hy]
    simp only [f,tanh_zero,zero_pow (by decide : (3:ℕ) ≠ 0),zero_div,sub_zero,zero_add] at h
    linarith only [h]
  rcases le_or_gt 0 x with hx | hx
  · exact hp x hx
  · have h := hp (-x) (by linarith)
    simpa only [tanh_neg,neg_sub_neg,abs_sub_comm,abs_neg] using h

def scalarVariance (h : ℝ) : ℝ := 1 - Real.tanh h ^ 2

lemma scalarVariance_pos (h : ℝ) : 0 < scalarVariance h :=
  sub_pos.mpr (Real.tanh_sq_lt_one h)

lemma scalarVariance_eq (h : ℝ) : scalarVariance h = 1 / Real.cosh h ^ 2 := by
  have hc := Real.cosh_sq_sub_sinh_sq h
  unfold scalarVariance
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith

lemma tanh_difference_eq (x y : ℝ) : Real.tanh y - Real.tanh x =
    Real.sinh (y-x) / (Real.cosh y * Real.cosh x) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_sub]
  field_simp

lemma normalized_tanh_difference (h d : ℝ) :
    (Real.tanh h - Real.tanh (h-d)) / scalarVariance h =
      Real.tanh d / (1 - Real.tanh h * Real.tanh d) := by
  have hc : Real.cosh (h-d) ≠ 0 := (Real.cosh_pos _).ne'
  have hh : Real.cosh h ≠ 0 := (Real.cosh_pos _).ne'
  have hd : Real.cosh d ≠ 0 := (Real.cosh_pos _).ne'
  have hm : Real.cosh h * Real.cosh d - Real.sinh h * Real.sinh d ≠ 0 := by
    simpa only [Real.cosh_sub] using hc
  rw [tanh_difference_eq, show h-(h-d)=d by ring, scalarVariance_eq]
  simp only [Real.tanh_eq_sinh_div_cosh]
  rw [Real.cosh_sub]
  field_simp

def q (z m : ℝ) : ℝ := Real.tanh (2*z) / (2*(1-m*Real.tanh (2*z)))

lemma tanh_difference_variance (h z : ℝ) :
    (Real.tanh h - Real.tanh (h-2*z)) / 2 = scalarVariance h * q z (Real.tanh h) := by
  have H := normalized_tanh_difference h (2*z)
  apply (div_eq_iff (scalarVariance_pos h).ne').mp at H
  rw [H]
  unfold q
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma q_denominator {z m : ℝ} (hz : |z| ≤ 1/10) (hm : |m| ≤ 1) :
    4/5 ≤ 1-m*Real.tanh (2*z) := by
  have hT : |Real.tanh (2*z)| ≤ 2*|z| := by
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using abs_tanh_le_abs (2*z)
  have hmul := mul_le_mul hm hT (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  rw [one_mul, ← abs_mul] at hmul
  linarith [le_abs_self (m*Real.tanh (2*z))]

lemma q_linear_bound {z m : ℝ} (hz : |z| ≤ 1/10) (hm : |m| ≤ 1) :
    |q z m| ≤ (5/4)*|z| := by
  have hden := q_denominator hz hm
  have hpos : 0 < 1-m*Real.tanh (2*z) := by linarith
  have hT : |Real.tanh (2*z)| ≤ 2*|z| := by
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using abs_tanh_le_abs (2*z)
  rw [q, abs_div, abs_of_pos (mul_pos (by norm_num) hpos), div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hden (abs_nonneg z)]

lemma q_expansion {z m : ℝ} (hz : |z| ≤ 1/10) (hm : |m| ≤ 1) :
    q z m = Real.tanh (2*z)/2 + m*Real.tanh (2*z)^2/2 +
      m^2*Real.tanh (2*z)^3/(2*(1-m*Real.tanh (2*z))) := by
  have hden := q_denominator hz hm
  have hne : 1-m*Real.tanh (2*z) ≠ 0 := by linarith
  have hD : 2*(1-m*Real.tanh (2*z)) ≠ 0 := mul_ne_zero (by norm_num) hne
  apply mul_right_cancel₀ hD
  simp only [q, add_mul, div_mul_cancel₀ _ hD]
  ring

lemma q_cubic_bound {z m : ℝ} (hz : |z| ≤ 1/10) (hm : |m| ≤ 1) :
    |q z m - z - 2*m*z^2| ≤ 7*|z|^3 := by
  let T := Real.tanh (2*z)
  have hT : |T| ≤ 2*|z| := by
    simpa only [T, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using abs_tanh_le_abs (2*z)
  have hc : |T-2*z| ≤ (8/3)*|z|^3 := by
    calc
      _ ≤ |2*z|^3/3 := tanh_cubic_error _
      _ = _ := by rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; ring
  have hden : 4/5 ≤ 1-m*T := q_denominator hz hm
  have hpos : 0 < 1-m*T := by linarith
  have h1 : |T/2-z| ≤ (4/3)*|z|^3 := by
    rw [show T/2-z = (T-2*z)/2 by ring, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith only [hc]
  have hsum : |T+2*z| ≤ 4*|z| := by
    calc
      _ ≤ |T| + |2*z| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; linarith only [hT]
  have h2 : |m*T^2/2-2*m*z^2| ≤ (16/3)*|z|^4 := by
    rw [show m*T^2/2-2*m*z^2 = m/2*((T-2*z)*(T+2*z)) by ring,
      abs_mul, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul]
    calc
      _ ≤ (1/2)*(((8/3)*|z|^3)*(4*|z|)) :=
        mul_le_mul (by linarith only [hm]) (mul_le_mul hc hsum (abs_nonneg _) (by positivity))
          (by positivity) (by norm_num)
      _ = _ := by ring
  have h3 : |m^2*T^3/(2*(1-m*T))| ≤ 5*|z|^3 := by
    rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos (by positivity : 0 < 2*(1-m*T)),
      div_le_iff₀ (by positivity)]
    have hm2 : |m|^2 ≤ 1 := by nlinarith only [hm, abs_nonneg m]
    have hT3 : |T|^3 ≤ 8*|z|^3 := by
      calc
        _ ≤ (2*|z|)^3 := pow_le_pow_left₀ (abs_nonneg _) hT 3
        _ = _ := by ring
    have hprod := mul_le_mul hm2 hT3 (by positivity : 0 ≤ |T|^3) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [hprod, mul_le_mul_of_nonneg_right hden (pow_nonneg (abs_nonneg z) 3)]
  have hrem : q z m - z - 2*m*z^2 = (T/2-z) + (m*T^2/2-2*m*z^2) +
      m^2*T^3/(2*(1-m*T)) := by
    rw [q_expansion hz hm]
    dsimp [T]; ring
  rw [hrem]
  calc
    _ ≤ (|T/2-z| + |m*T^2/2-2*m*z^2|) + |m^2*T^3/(2*(1-m*T))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (4/3)*|z|^3 + (16/3)*|z|^4 + 5*|z|^3 :=
      add_le_add (add_le_add h1 h2) h3
    _ ≤ 7*|z|^3 := by
      have h := mul_le_mul_of_nonneg_right hz (pow_nonneg (abs_nonneg z) 3)
      nlinarith only [h, pow_nonneg (abs_nonneg z) 3]

lemma q_quadratic_bound {z m : ℝ} (hz : |z| ≤ 1/10) (hm : |m| ≤ 1) :
    |q z m - z| ≤ (27/10)*z^2 := by
  have hc := q_cubic_bound hz hm
  have hmz : |2*m*z^2| ≤ 2*|z|^2 := by
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_pow]
    nlinarith only [mul_le_mul_of_nonneg_right hm (sq_nonneg |z|)]
  calc
    _ = |(q z m-z-2*m*z^2)+2*m*z^2| := by congr 1; ring
    _ ≤ |q z m-z-2*m*z^2|+|2*m*z^2| := abs_add_le _ _
    _ ≤ 7*|z|^3+2*|z|^2 := add_le_add hc hmz
    _ ≤ (27/10)*z^2 := by
      have h := mul_le_mul_of_nonneg_right hz (sq_nonneg |z|)
      nlinarith only [h, sq_abs z]

lemma field_flip_coordinate {n : ℕ} (J : Interaction n) (x : Spin n) (i j : Fin n) :
    field J (flip i x) j = field J x j - 2 * J j i * spin x i := by
  simp only [field, spin_flip, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

def conditionalVariance {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  1 - mean J x i ^ 2

lemma conditionalVariance_pos {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    0 < conditionalVariance J x i := scalarVariance_pos _

lemma conditionalVariance_le_one {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    conditionalVariance J x i ≤ 1 := by
  unfold conditionalVariance
  linarith [sq_nonneg (mean J x i)]

lemma mean_abs_le_one {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    |mean J x i| ≤ 1 := (abs_lt.mpr ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).le

lemma gradientWeight_pos {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    0 < gradientWeight J x i := by
  cases hi : x i
  · have h := Real.neg_one_lt_tanh (field J x i)
    simp only [gradientWeight, spin, hi, Bool.false_eq_true, ↓reduceIte, neg_mul,
      one_mul, sub_neg_eq_add, mean]
    linarith
  · simpa only [gradientWeight, spin, hi, ↓reduceIte, one_mul, mean] using
      sub_pos.mpr (Real.tanh_lt_one (field J x i))

@[simp] lemma mean_weight_plus {n : ℕ} (J : Interaction n) (i : Fin n) :
    gradientWeight J (plusSpin n) i = 1 - mean J (plusSpin n) i := by
  simp [gradientWeight, spin, plusSpin]

lemma halfDiff_mean_plus {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (i j : Fin n) :
    halfDiff i (fun y => mean J y j) (plusSpin n) =
      conditionalVariance J (plusSpin n) j * q (J i j) (mean J (plusSpin n) j) := by
  have hplus : replace (plusSpin n) i true = plusSpin n := replace_self _ _
  have hminus : replace (plusSpin n) i false = flip i (plusSpin n) := rfl
  simp only [halfDiff, hplus, hminus, mean, field_flip_coordinate, spin, plusSpin,
    ↓reduceIte, mul_one, ← hsymm i j]
  exact tanh_difference_variance _ _

lemma variance_over_weight {m : ℝ} (hm : -1 ≤ m) (hm' : m < 1) :
    (1 - m^2)^2 / (1-m) ≤ 32/27 := by
  have hpos : 0 < 1-m := sub_pos.mpr hm'
  have hid : (1-m^2)^2 / (1-m) = (1-m)*(1+m)^2 := by
    apply (div_eq_iff hpos.ne').mpr
    ring
  rw [hid]
  have hp : 0 ≤ m + 5/3 := by linarith only [hm]
  nlinarith only [mul_nonneg (sq_nonneg (m-1/3)) hp]

lemma pair_denominator_control {vi vj wi wj pi pj : ℝ}
    (hwi : 0 < wi) (hwj : 0 < wj) :
    (vj * |pi| + vi * |pj|)^2 / (wi + wj) ≤
      (vj^2 / wj) * pi^2 + (vi^2 / wi) * pj^2 := by
  have H := Finset.sq_sum_div_le_sum_sq_div (R := ℝ) Finset.univ
    ![vj * |pi|, vi * |pj|] (g := ![wj, wi]) (by
      intro i _
      fin_cases i
      · exact hwj
      · exact hwi)
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_pow, sq_abs, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, add_comm] using H

lemma scalar_pair_denominator_control {mi mj pi pj : ℝ}
    (hmi : -1 ≤ mi) (hmi' : mi < 1) (hmj : -1 ≤ mj) (hmj' : mj < 1) :
    ((1-mj^2)*|pi| + (1-mi^2)*|pj|)^2 / ((1-mi) + (1-mj)) ≤
      (32/27)*(pi^2 + pj^2) := by
  calc
    _ ≤ ((1-mj^2)^2/(1-mj))*pi^2 + ((1-mi^2)^2/(1-mi))*pj^2 :=
      pair_denominator_control (sub_pos.mpr hmi') (sub_pos.mpr hmj')
    _ ≤ (32/27)*pi^2 + (32/27)*pj^2 :=
      add_le_add (mul_le_mul_of_nonneg_right (variance_over_weight hmj hmj') (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (variance_over_weight hmi hmi') (sq_nonneg _))
    _ = _ := by ring

lemma complete_pair_square (A r w : ℝ) (hw : 0 < w) :
    -2*A*r - w*r^2 ≤ A^2/w := by
  rw [le_div_iff₀ hw]
  nlinarith only [sq_nonneg (A+w*r)]

lemma weighted_pair_abs_le {vi vj qi qj pi pj B : ℝ}
    (hvi : 0 ≤ vi) (hvj : 0 ≤ vj) (hqi : |qi| ≤ B) (hqj : |qj| ≤ B) :
    |vj*qj*pi + vi*qi*pj| ≤ B * (vj*|pi| + vi*|pj|) := by
  calc
    _ ≤ |vj*qj*pi| + |vi*qi*pj| := abs_add_le _ _
    _ = vj*|qj| *|pi| + vi*|qi| *|pj| := by
      simp only [abs_mul, abs_of_nonneg hvi, abs_of_nonneg hvj]
    _ ≤ vj*B*|pi| + vi*B*|pj| := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqj hvj) (abs_nonneg pi))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqi hvi) (abs_nonneg pj))
    _ = _ := by ring

lemma pair_q_error {z mi mj vi vj pi pj : ℝ}
    (hz : |z| ≤ 1/10) (hmi : |mi| ≤ 1) (hmj : |mj| ≤ 1)
    (hvi : 0 ≤ vi) (hvj : 0 ≤ vj) :
    |(vj*q z mj*pi + vi*q z mi*pj)^2 - (z*(vj*pi+vi*pj))^2| ≤
      7*|z|^3*(vj*|pi|+vi*|pj|)^2 := by
  let A := vj*q z mj*pi + vi*q z mi*pj
  let B := z*(vj*pi+vi*pj)
  let S := vj*|pi|+vi*|pj|
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hdiff : |A-B| ≤ (27/10)*z^2*S := by
    have hid : A-B = vj*(q z mj-z)*pi + vi*(q z mi-z)*pj := by dsimp [A, B]; ring
    rw [hid]
    exact weighted_pair_abs_le hvi hvj (q_quadratic_bound hz hmi) (q_quadratic_bound hz hmj)
  have hA : |A| ≤ (5/4)*|z| *S :=
    weighted_pair_abs_le hvi hvj (q_linear_bound hz hmi) (q_linear_bound hz hmj)
  have hB : |B| ≤ |z| *S := by
    have hid : B = vj*z*pi + vi*z*pj := by dsimp [B]; ring
    rw [hid]
    exact weighted_pair_abs_le hvi hvj le_rfl le_rfl
  have hsum : |A+B| ≤ (9/4)*|z| *S := by
    calc
      _ ≤ |A| + |B| := abs_add_le _ _
      _ ≤ (5/4)*|z| *S + |z| *S := add_le_add hA hB
      _ = _ := by ring
  change |A^2-B^2| ≤ 7*|z|^3*S^2
  rw [show A^2-B^2 = (A-B)*(A+B) by ring, abs_mul]
  calc
    _ ≤ ((27/10)*z^2*S)*((9/4)*|z| *S) :=
      mul_le_mul hdiff hsum (abs_nonneg _) (by positivity)
    _ = (243/40)*|z|^3*S^2 := by rw [← sq_abs z]; ring
    _ ≤ 7*|z|^3*S^2 := by nlinarith only [mul_nonneg (pow_nonneg (abs_nonneg z) 3) (sq_nonneg S)]

lemma pair_square_replacement {z mi mj pi pj : ℝ}
    (hz : |z| ≤ 1/10) (hmi : -1 ≤ mi) (hmi' : mi < 1)
    (hmj : -1 ≤ mj) (hmj' : mj < 1) :
    ((1-mj^2)*q z mj*pi + (1-mi^2)*q z mi*pj)^2 / ((1-mi)+(1-mj)) ≤
      z^2*((1-mj^2)*pi+(1-mi^2)*pj)^2 / ((1-mi)+(1-mj)) +
      (224/27)*|z|^3*(pi^2+pj^2) := by
  have hmiabs : |mi| ≤ 1 := abs_le.mpr ⟨hmi, hmi'.le⟩
  have hmjabs : |mj| ≤ 1 := abs_le.mpr ⟨hmj, hmj'.le⟩
  have hvi : 0 ≤ 1-mi^2 := by nlinarith only [sq_le_sq₀ (abs_nonneg mi) (by norm_num : (0:ℝ) ≤ 1) |>.2 hmiabs, sq_abs mi]
  have hvj : 0 ≤ 1-mj^2 := by nlinarith only [sq_le_sq₀ (abs_nonneg mj) (by norm_num : (0:ℝ) ≤ 1) |>.2 hmjabs, sq_abs mj]
  have herr := pair_q_error hz hmiabs hmjabs hvi hvj (pi := pi) (pj := pj)
  have hd : 0 < (1-mi)+(1-mj) := add_pos (sub_pos.mpr hmi') (sub_pos.mpr hmj')
  have hraw : ((1-mj^2)*q z mj*pi + (1-mi^2)*q z mi*pj)^2 ≤
      z^2*((1-mj^2)*pi+(1-mi^2)*pj)^2 + 7*|z|^3*((1-mj^2)*|pi|+(1-mi^2)*|pj|)^2 := by
    have h := (le_abs_self _).trans herr
    rw [mul_pow] at h
    linarith only [h]
  calc
    _ ≤ (z^2*((1-mj^2)*pi+(1-mi^2)*pj)^2 + 7*|z|^3*((1-mj^2)*|pi|+(1-mi^2)*|pj|)^2) /
        ((1-mi)+(1-mj)) := div_le_div_of_nonneg_right hraw hd.le
    _ = z^2*((1-mj^2)*pi+(1-mi^2)*pj)^2 / ((1-mi)+(1-mj)) +
        (7*|z|^3)*(((1-mj^2)*|pi|+(1-mi^2)*|pj|)^2/((1-mi)+(1-mj))) := by ring
    _ ≤ z^2*((1-mj^2)*pi+(1-mi^2)*pj)^2 / ((1-mi)+(1-mj)) +
        (7*|z|^3)*((32/27)*(pi^2+pj^2)) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (scalar_pair_denominator_control hmi hmi' hmj hmj') (by positivity))
    _ = _ := by ring

def pairSum {n : ℕ} (F : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), F i j

lemma sum_transpose_triangle {n : ℕ} (F : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => j < i), F i j) =
      pairSum (fun i j => F j i) := by
  simp only [pairSum, Finset.sum_filter]
  rw [Finset.sum_comm]

lemma sum_offdiag_pairs {n : ℕ} (F : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, F i j) = pairSum (fun i j => F i j + F j i) := by
  have hsplit (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i, F i j) =
        (∑ j ∈ Finset.univ.filter (fun j => i < j), F i j) +
        ∑ j ∈ Finset.univ.filter (fun j => j < i), F i j := by
    have heq : Finset.univ.erase i = (Finset.univ.filter (fun j => i < j)) ∪
        (Finset.univ.filter (fun j => j < i)) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
        Finset.mem_filter, true_and]
      omega
    have hdis : Disjoint (Finset.univ.filter (fun j => i < j))
        (Finset.univ.filter (fun j => j < i)) := by
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hj hj'; exact (lt_asymm hj hj')
    rw [heq, Finset.sum_union hdis]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, sum_transpose_triangle]
  simp only [pairSum, Finset.sum_add_distrib]

lemma pairSum_add {n : ℕ} (F G : Fin n → Fin n → ℝ) :
    pairSum (fun i j => F i j + G i j) = pairSum F + pairSum G := by
  simp only [pairSum, Finset.sum_add_distrib]

end SKRatio.Calculus
end
end

end OAI
