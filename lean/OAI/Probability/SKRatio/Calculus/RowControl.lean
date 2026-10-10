import Mathlib
import OAI.Probability.SKRatio.Calculus.PlusSpin

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
open Real Set

lemma pairSum_sub {n : ℕ} (F G : Fin n → Fin n → ℝ) :
    pairSum (fun i j => F i j - G i j) = pairSum F - pairSum G := by
  simp only [pairSum, Finset.sum_sub_distrib]

lemma pairSum_mul {n : ℕ} (a : ℝ) (F : Fin n → Fin n → ℝ) :
    pairSum (fun i j => a * F i j) = a * pairSum F := by
  simp only [pairSum, Finset.mul_sum]

lemma pairSum_le {n : ℕ} {F G : Fin n → Fin n → ℝ}
    (h : ∀ i j, i < j → F i j ≤ G i j) : pairSum F ≤ pairSum G := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j hj
  exact h i j (Finset.mem_filter.mp hj).2

def rowControl {n : ℕ} (J : Interaction n) (k : ℕ) : ℝ :=
  (Finset.univ.sup (fun i => ∑ j, ‖J i j‖₊ ^ k) : NNReal)

lemma rowControl_nonneg {n : ℕ} (J : Interaction n) (k : ℕ) : 0 ≤ rowControl J k :=
  NNReal.coe_nonneg _

lemma row_le_rowControl {n : ℕ} (J : Interaction n) (k : ℕ) (i : Fin n) :
    (∑ j, |J i j|^k) ≤ rowControl J k := by
  have h := Finset.le_sup (f := fun i => ∑ j, ‖J i j‖₊^k) (Finset.mem_univ i)
  simpa only [rowControl, NNReal.coe_sum, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs] using
    (NNReal.coe_le_coe.mpr h)

abbrev R2 {n : ℕ} (J : Interaction n) : ℝ := rowControl J 2
abbrev R3 {n : ℕ} (J : Interaction n) : ℝ := rowControl J 3

lemma pair_row_bound {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (p : Fin n → ℝ) (k : ℕ) :
    pairSum (fun i j => |J i j|^k * (p i^2+p j^2)) ≤ rowControl J k * ∑ i, p i^2 := by
  have hid : pairSum (fun i j => |J i j|^k * (p i^2+p j^2)) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, |J i j|^k * p i^2 := by
    rw [sum_offdiag_pairs]
    unfold pairSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    rw [← hsymm i j]
    ring
  rw [hid, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun _ _ _ => pow_nonneg (abs_nonneg _) k)).trans (row_le_rowControl J k i)

lemma offdiag_abs_row_bound {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (p : Fin n → ℝ) (k : ℕ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, |J i j|^k * |p i| * |p j|) ≤
      rowControl J k * ∑ i, p i^2 := by
  rw [sum_offdiag_pairs]
  refine le_trans (pairSum_le (fun i j _ => ?_)) (pair_row_bound J hsymm p k)
  rw [← hsymm i j]
  have h : 2*|p i| * |p j| ≤ p i^2+p j^2 := by
    nlinarith only [sq_nonneg (|p i|-|p j|), sq_abs (p i), sq_abs (p j)]
  have hm := mul_le_mul_of_nonneg_left h (pow_nonneg (abs_nonneg (J i j)) k)
  nlinarith only [hm]

lemma eliminate_second_differences {n : ℕ} (p w : Fin n → ℝ)
    (a r : Fin n → Fin n → ℝ) (hw : ∀ i, 0 < w i) (hr : ∀ i j, r i j = r j i) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i*a i j*(p j-2*r i j)) -
      (∑ i, ∑ j ∈ Finset.univ.erase i, w j*(r i j)^2) ≤
    (∑ i, ∑ j ∈ Finset.univ.erase i, p i*a i j*p j) +
      pairSum (fun i j => (a i j*p i+a j i*p j)^2/(w i+w j)) := by
  rw [sum_offdiag_pairs, sum_offdiag_pairs, sum_offdiag_pairs, ← pairSum_sub, ← pairSum_add]
  apply pairSum_le
  intro i j _
  rw [← hr i j]
  have h := complete_pair_square (a i j*p i+a j i*p j) (r i j) (w i+w j)
    (add_pos (hw i) (hw j))
  linarith only [h]

def gradientForm {n : ℕ} (J : Interaction n) (p : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i,
    J i j * p i * conditionalVariance J (plusSpin n) j * p j) +
  2 * (∑ i, ∑ j ∈ Finset.univ.erase i,
    J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j) +
  pairSum (fun i j =>
    J i j^2 * (conditionalVariance J (plusSpin n) j * p i +
      conditionalVariance J (plusSpin n) i * p j)^2 /
        (gradientWeight J (plusSpin n) i + gradientWeight J (plusSpin n) j))

lemma field_difference_error {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (i j : Fin n) :
    |halfDiff i (fun y => mean J y j) (plusSpin n) -
      J i j * conditionalVariance J (plusSpin n) j -
      2*(J i j)^2 * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j| ≤
    7*|J i j|^3 := by
  let v := conditionalVariance J (plusSpin n) j
  let m := mean J (plusSpin n) j
  have hv : 0 ≤ v := (conditionalVariance_pos J (plusSpin n) j).le
  have hv1 : v ≤ 1 := conditionalVariance_le_one J (plusSpin n) j
  rw [halfDiff_mean_plus J hsymm]
  change |v*q (J i j) m - J i j*v - 2*(J i j)^2*m*v| ≤ _
  rw [show v*q (J i j) m - J i j*v - 2*(J i j)^2*m*v =
      v*(q (J i j) m - J i j - 2*m*(J i j)^2) by ring, abs_mul, abs_of_nonneg hv]
  calc
    _ ≤ v*(7*|J i j|^3) := mul_le_mul_of_nonneg_left
      (q_cubic_bound (hsmall i j) (mean_abs_le_one J (plusSpin n) j)) hv
    _ ≤ 7*|J i j|^3 := by nlinarith only [mul_le_mul_of_nonneg_right hv1 (by positivity : 0 ≤ 7*|J i j|^3)]

lemma linear_field_replacement {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (p : Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      p i * halfDiff i (fun y => mean J y j) (plusSpin n) * p j) ≤
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      J i j * p i * conditionalVariance J (plusSpin n) j * p j) +
    2 * (∑ i, ∑ j ∈ Finset.univ.erase i,
      J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j) +
    7*R3 J*(∑ i, p i^2) := by
  have hpoint (i j : Fin n) : p i * halfDiff i (fun y => mean J y j) (plusSpin n) * p j ≤
      J i j * p i * conditionalVariance J (plusSpin n) j * p j +
      2 * (J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j) +
      7*|J i j|^3 * |p i| * |p j| := by
    let e := halfDiff i (fun y => mean J y j) (plusSpin n) -
      J i j * conditionalVariance J (plusSpin n) j -
      2*(J i j)^2 * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j
    have he : |e| ≤ 7*|J i j|^3 := field_difference_error J hsymm hsmall i j
    have hprod : p i*e*p j ≤ 7*|J i j|^3 * |p i| * |p j| := by
      calc
        _ ≤ |p i*e*p j| := le_abs_self _
        _ = |e| * |p i| * |p j| := by simp only [abs_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right he (abs_nonneg _)) (abs_nonneg _)
    dsimp only [e] at hprod
    linarith only [hprod]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ.erase i) => hpoint i j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc] at hsum
  have hrow := mul_le_mul_of_nonneg_left (offdiag_abs_row_bound J hsymm p 3)
    (by norm_num : (0:ℝ) ≤ 7)
  simp only [← Finset.mul_sum, mul_assoc] at hrow ⊢
  linarith only [hsum, hrow]

lemma completed_squares_replacement {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (p : Fin n → ℝ) :
    pairSum (fun i j =>
      (halfDiff i (fun y => mean J y j) (plusSpin n)*p i +
        halfDiff j (fun y => mean J y i) (plusSpin n)*p j)^2 /
          (gradientWeight J (plusSpin n) i+gradientWeight J (plusSpin n) j)) ≤
    pairSum (fun i j =>
      J i j^2 * (conditionalVariance J (plusSpin n) j * p i +
        conditionalVariance J (plusSpin n) i * p j)^2 /
          (gradientWeight J (plusSpin n) i + gradientWeight J (plusSpin n) j)) +
      (224/27)*R3 J*(∑ i, p i^2) := by
  calc
    _ ≤ pairSum (fun i j =>
      J i j^2 * (conditionalVariance J (plusSpin n) j * p i +
        conditionalVariance J (plusSpin n) i * p j)^2 /
          (gradientWeight J (plusSpin n) i + gradientWeight J (plusSpin n) j) +
        (224/27)*|J i j|^3*(p i^2+p j^2)) := by
      apply pairSum_le
      intro i j _
      rw [halfDiff_mean_plus J hsymm, halfDiff_mean_plus J hsymm, ← hsymm i j]
      simp only [mean_weight_plus, conditionalVariance]
      exact pair_square_replacement (hsmall i j)
        (Real.neg_one_lt_tanh _).le (Real.tanh_lt_one _)
        (Real.neg_one_lt_tanh _).le (Real.tanh_lt_one _)
    _ = _ + (224/27) * pairSum (fun i j => |J i j|^3*(p i^2+p j^2)) := by
      rw [pairSum_add]
      congr 1
      simp only [mul_assoc, pairSum_mul]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (pair_row_bound J hsymm p 3)
        (by norm_num : (0:ℝ) ≤ 224/27)
      simp only [mul_assoc]
      exact add_le_add le_rfl h

theorem pointwise_gradient_bound_plus {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (f : Observables n) (t : ℝ) :
    (1/2:ℝ) * (deriv (fun s => unweightedGradient (semigroup J s f) (plusSpin n)) t -
      generator J (unweightedGradient (semigroup J t f)) (plusSpin n)) ≤
    -unweightedGradient (semigroup J t f) (plusSpin n) +
      gradientForm J (fun i => halfDiff i (semigroup J t f) (plusSpin n)) +
      16*R3 J*unweightedGradient (semigroup J t f) (plusSpin n) := by
  rw [pointwise_gradient_identity J hdiag]
  let p := fun i => halfDiff i (semigroup J t f) (plusSpin n)
  let a := fun i j => halfDiff i (fun y => mean J y j) (plusSpin n)
  let r := fun i j => halfDiff i (halfDiff j (semigroup J t f)) (plusSpin n)
  have hc := eliminate_second_differences p (gradientWeight J (plusSpin n)) a r
    (gradientWeight_pos J (plusSpin n)) (fun i j => halfDiff_comm i j _ _)
  have hl := linear_field_replacement J hsymm hsmall p
  have hs := completed_squares_replacement J hsymm hsmall p
  have hU : 0 ≤ unweightedGradient (semigroup J t f) (plusSpin n) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hR := rowControl_nonneg J 3
  have hbudget := mul_nonneg hR hU
  dsimp only [p, a, r] at hc hl hs
  unfold gradientForm unweightedGradient at *
  linarith only [hc, hl, hs, hbudget]

def signProduct {n : ℕ} (x y : Spin n) : Spin n :=
  fun i => if x i then y i else !(y i)

@[simp] lemma signProduct_plus {n : ℕ} (x : Spin n) : signProduct x (plusSpin n) = x := by
  funext i
  cases hi : x i <;> simp [signProduct, plusSpin, hi]

@[simp] lemma plus_signProduct {n : ℕ} (x : Spin n) : signProduct (plusSpin n) x = x := by
  funext i
  simp [signProduct, plusSpin]

lemma signProduct_involutive {n : ℕ} (x : Spin n) : Function.Involutive (signProduct x) := by
  intro y
  funext i
  cases h : x i <;> simp [signProduct, h]

lemma spin_signProduct {n : ℕ} (x y : Spin n) (i : Fin n) :
    spin (signProduct x y) i = spin x i * spin y i := by
  cases hx : x i <;> cases hy : y i <;> simp [signProduct, spin, hx, hy]

@[simp] lemma abs_spin {n : ℕ} (x : Spin n) (i : Fin n) : |spin x i| = 1 := by
  cases hx : x i <;> simp [spin, hx]

lemma signProduct_replace {n : ℕ} (x y : Spin n) (i : Fin n) (b : Bool) :
    signProduct x (replace y i b) = replace (signProduct x y) i (if x i then b else !b) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [replace, signProduct]
  · simp [replace, signProduct, hj]

def signConjugate {n : ℕ} (x : Spin n) (J : Interaction n) : Interaction n :=
  fun i j => spin x i * J i j * spin x j

def signPullback {n : ℕ} (x : Spin n) (f : Observables n) : Observables n :=
  fun y => f (signProduct x y)

lemma halfDiff_signPullback {n : ℕ} (x y : Spin n) (f : Observables n) (i : Fin n) :
    halfDiff i (signPullback x f) y = spin x i * halfDiff i f (signProduct x y) := by
  simp only [halfDiff, signPullback, signProduct_replace]
  cases hi : x i <;> simp only [hi, ↓reduceIte, Bool.not_true, Bool.not_false, spin,
    Bool.false_eq_true, neg_mul, one_mul]
  · ring

lemma field_signConjugate {n : ℕ} (J : Interaction n) (x y : Spin n) (i : Fin n) :
    field (signConjugate x J) y i = spin x i * field J (signProduct x y) i := by
  simp only [field, signConjugate, spin_signProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma mean_signConjugate {n : ℕ} (J : Interaction n) (x y : Spin n) (i : Fin n) :
    mean (signConjugate x J) y i = spin x i * mean J (signProduct x y) i := by
  simp only [mean, field_signConjugate]
  cases hi : x i <;> simp only [spin, hi, Bool.false_eq_true, ↓reduceIte,
    neg_mul, one_mul, Real.tanh_neg]

lemma generator_signConjugate {n : ℕ} (J : Interaction n) (x : Spin n) (f : Observables n) :
    generator (signConjugate x J) (signPullback x f) = signPullback x (generator J f) := by
  funext y
  simp only [generator, halfDiff_signPullback, mean_signConjugate, signPullback]
  apply Finset.sum_congr rfl
  intro i _
  rw [spin_signProduct]
  linear_combination mean J (signProduct x y) i * halfDiff i f (signProduct x y) * spin_sq x i

lemma unweightedGradient_signPullback {n : ℕ} (x : Spin n) (f : Observables n) :
    unweightedGradient (signPullback x f) = signPullback x (unweightedGradient f) := by
  funext y
  simp only [unweightedGradient, halfDiff_signPullback, mul_pow, spin_sq, one_mul, signPullback]

lemma gradient_drift_signPullback {n : ℕ} (J : Interaction n) (x y : Spin n) (f : Observables n) :
    (∑ i, 2 * halfDiff i (signPullback x f) y *
      halfDiff i (generator (signConjugate x J) (signPullback x f)) y) =
    ∑ i, 2 * halfDiff i f (signProduct x y) * halfDiff i (generator J f) (signProduct x y) := by
  rw [generator_signConjugate]
  simp only [halfDiff_signPullback]
  apply Finset.sum_congr rfl
  intro i _
  linear_combination 2 * halfDiff i f (signProduct x y) * halfDiff i (generator J f) (signProduct x y) * spin_sq x i

lemma signConjugate_symm {n : ℕ} (J : Interaction n) (hsymm : ∀ i j, J i j = J j i)
    (x : Spin n) : ∀ i j, signConjugate x J i j = signConjugate x J j i := by
  intro i j
  simp only [signConjugate, ← hsymm i j]
  ring

lemma signConjugate_diag {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) : ∀ i, signConjugate x J i i = 0 := by
  intro i; simp [signConjugate, hdiag]

@[simp] lemma abs_signConjugate {n : ℕ} (J : Interaction n) (x : Spin n) (i j : Fin n) :
    |signConjugate x J i j| = |J i j| := by
  simp [signConjugate, abs_mul]

lemma rowControl_signConjugate {n : ℕ} (J : Interaction n) (x : Spin n) (k : ℕ) :
    rowControl (signConjugate x J) k = rowControl J k := by
  have hn (i j : Fin n) : ‖signConjugate x J i j‖₊ = ‖J i j‖₊ := by
    apply NNReal.coe_injective
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_signConjugate]
  simp only [rowControl, hn]

lemma instantaneous_gradient_bound_plus {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (f : Observables n) :
    (1/2:ℝ) * ((∑ i, 2 * halfDiff i f (plusSpin n) *
      halfDiff i (generator J f) (plusSpin n)) - generator J (unweightedGradient f) (plusSpin n)) ≤
    -unweightedGradient f (plusSpin n) + gradientForm J (fun i => halfDiff i f (plusSpin n)) +
      16*R3 J*unweightedGradient f (plusSpin n) := by
  have h := pointwise_gradient_bound_plus J hsymm hdiag hsmall f 0
  rw [(unweightedGradient_hasDerivAt J f (plusSpin n) 0).deriv] at h
  simpa only [semigroup_zero, one_apply_eq_self] using h

theorem pointwise_gradient_local_bound {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (f : Observables n) (t : ℝ) (x : Spin n) :
    (1/2:ℝ) * (deriv (fun s => unweightedGradient (semigroup J s f) x) t -
      generator J (unweightedGradient (semigroup J t f)) x) ≤
    -unweightedGradient (semigroup J t f) x +
      gradientForm (signConjugate x J) (fun i => spin x i * halfDiff i (semigroup J t f) x) +
      16*R3 J*unweightedGradient (semigroup J t f) x := by
  have h := instantaneous_gradient_bound_plus (signConjugate x J) (signConjugate_symm J hsymm x)
    (signConjugate_diag J hdiag x) (by simpa only [abs_signConjugate] using hsmall)
    (signPullback x (semigroup J t f))
  rw [gradient_drift_signPullback, unweightedGradient_signPullback,
    generator_signConjugate] at h
  simp only [halfDiff_signPullback, signPullback, signProduct_plus, R3,
    rowControl_signConjugate] at h
  rw [(unweightedGradient_hasDerivAt J f x t).deriv]
  exact h

def euclideanOpNorm {n : ℕ} (J : Interaction n) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J‖

lemma euclideanOpNorm_nonneg {n : ℕ} (J : Interaction n) : 0 ≤ euclideanOpNorm J :=
  norm_nonneg _

lemma euclideanNorm_variance_le {n : ℕ} (J : Interaction n) (x : Spin n)
    (p : Fin n → ℝ) :
    ‖WithLp.toLp 2 (fun i => conditionalVariance J x i * p i)‖ ≤
      ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin n))‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  have hv := (conditionalVariance_pos J x i).le
  have hv1 := conditionalVariance_le_one J x i
  have hv2 : (conditionalVariance J x i)^2 ≤ 1 := by nlinarith only [hv, hv1]
  nlinarith only [mul_le_mul_of_nonneg_right hv2 (sq_nonneg (p i))]

lemma gradientForm_linear_bound {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (p : Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      J i j * p i * conditionalVariance J (plusSpin n) j * p j) ≤
    euclideanOpNorm J * ∑ i, p i^2 := by
  let P : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 p
  let Q : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun j => conditionalVariance J (plusSpin n) j * p j)
  have hid : (∑ i, ∑ j ∈ Finset.univ.erase i,
      J i j * p i * conditionalVariance J (plusSpin n) j * p j) =
      inner ℝ P (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J Q) := by
    rw [Matrix.inner_toEuclideanCLM (J : Matrix (Fin n) (Fin n) ℝ) P Q]
    simp only [dotProduct, Matrix.mulVec, P, Q, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [hdiag, zero_mul, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hid]
  calc
    _ ≤ ‖P‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J Q‖ := real_inner_le_norm _ _
    _ ≤ ‖P‖ * (euclideanOpNorm J * ‖Q‖) :=
      mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J).le_opNorm _) (norm_nonneg _)
    _ ≤ ‖P‖ * (euclideanOpNorm J * ‖P‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (euclideanNorm_variance_le J (plusSpin n) p)
          (euclideanOpNorm_nonneg J)) (norm_nonneg _)
    _ = euclideanOpNorm J * ∑ i, p i^2 := by
      rw [show ‖P‖ * (euclideanOpNorm J * ‖P‖) = euclideanOpNorm J * ‖P‖^2 by ring,
        EuclideanSpace.real_norm_sq_eq]

lemma abs_mean_variance_bound {m : ℝ} (hm : |m| ≤ 1) :
    |m*(1-m^2)| ≤ 2/(3*Real.sqrt 3) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hmv : 0 ≤ 1-m^2 := by nlinarith only [sq_abs m, abs_nonneg m, hm]
  rw [abs_mul, abs_of_nonneg hmv, le_div_iff₀ (by positivity : 0 < 3*Real.sqrt 3)]
  have h : 0 ≤ (Real.sqrt 3 * |m| - 1)^2 * (Real.sqrt 3 * |m| + 2) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hc : (Real.sqrt 3 * |m|)^3 = 3*m^2*(Real.sqrt 3*|m|) := by
    rw [pow_succ, mul_pow, hs2, sq_abs]
  nlinarith only [h, hc]

lemma mean_variance_bound {n : ℕ} (J : Interaction n) (x : Spin n) (j : Fin n) :
    |mean J x j * conditionalVariance J x j| ≤ 2/(3*Real.sqrt 3) :=
  abs_mean_variance_bound (mean_abs_le_one J x j)

lemma gradientForm_quadratic_bound {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (p : Fin n → ℝ) :
    2*(∑ i, ∑ j ∈ Finset.univ.erase i,
      J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j) ≤
    (4/(3*Real.sqrt 3))* R2 J * ∑ i, p i^2 := by
  have hpoint (i j : Fin n) :
      J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j ≤
      (2/(3*Real.sqrt 3)) * (|J i j|^2*|p i| *|p j|) := by
    calc
      _ ≤ |J i j^2 * p i * mean J (plusSpin n) j * conditionalVariance J (plusSpin n) j * p j| :=
        le_abs_self _
      _ = |mean J (plusSpin n) j*conditionalVariance J (plusSpin n) j| *
          (|J i j|^2*|p i| *|p j|) := by simp only [abs_mul, abs_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mean_variance_bound J (plusSpin n) j) (by positivity)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ.erase i) => hpoint i j))
  simp only [← Finset.mul_sum] at hsum
  have hrow := mul_le_mul_of_nonneg_left (offdiag_abs_row_bound J hsymm p 2)
    (by positivity : 0 ≤ 2/(3*Real.sqrt 3))
  calc
    _ ≤ 2*((2/(3*Real.sqrt 3))* (R2 J * ∑ i, p i^2)) :=
      mul_le_mul_of_nonneg_left (hsum.trans hrow) (by norm_num)
    _ = _ := by ring

end SKRatio.Calculus
end
end

end OAI
