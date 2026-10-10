import OAI.Probability.FreeIsing.Cavity.LogOdds
import OAI.Probability.FreeIsing.Posterior.FinitePosterior
import OAI.Probability.FreeIsing.Spins.Kernel

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.LeafGibbs

def expectation {A : Type*} [Fintype A] (E f : A → ℝ) : ℝ :=
  (∑ a, f a * Real.exp (E a)) / ∑ a, Real.exp (E a)

theorem expectation_eq_mean_zero {A : Type*} [Fintype A] (E f : A → ℝ) :
    expectation E f = FinitePosterior.mean E (fun _ => 0) f 0 := by
  simp only [expectation, FinitePosterior.mean, FinitePosterior.partition,
    FinitePosterior.weight, zero_mul, add_zero]

def covariance {A : Type*} [Fintype A] (E f g : A → ℝ) : ℝ :=
  expectation E (fun a => f a * g a) - expectation E f * expectation E g

def energy {A : Type*} (E : A → ℝ) (parent : A → IsingSpin)
    (beta y : ℝ) (s : A × IsingSpin) : ℝ :=
  E s.1 + y * spinSign s.2 + beta * spinSign s.2 * spinSign (parent s.1)

lemma expectation_add {A : Type*} [Fintype A] (E f g : A → ℝ) :
    expectation E (fun a => f a + g a) = expectation E f + expectation E g := by
  simp only [expectation, add_mul, Finset.sum_add_distrib, add_div]

lemma expectation_const_mul {A : Type*} [Fintype A] (E f : A → ℝ) (c : ℝ) :
    expectation E (fun a => c * f a) = c * expectation E f := by
  simp only [expectation, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

lemma expectation_mul_const {A : Type*} [Fintype A] (E f : A → ℝ) (c : ℝ) :
    expectation E (fun a => f a * c) = expectation E f * c := by
  simpa only [mul_comm] using expectation_const_mul E f c

lemma expectation_const {A : Type*} [Fintype A] [Nonempty A] (E : A → ℝ) (c : ℝ) :
    expectation E (fun _ => c) = c := by
  have hpos : 0 < ∑ a, Real.exp (E a) :=
    Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [expectation, ← Finset.mul_sum]
  exact mul_div_cancel_right₀ c hpos.ne'

lemma spin_exponential_mean (z : ℝ) :
    (∑ l : IsingSpin, spinSign l * Real.exp (z * spinSign l)) =
      Real.tanh z * ∑ l : IsingSpin, Real.exp (z * spinSign l) := by
  simp only [sum_isingSpin, spinSign_neg, spinSign_pos, mul_neg_one,
    mul_one, neg_one_mul, one_mul]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hpos : Real.exp z + Real.exp (-z) ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
  field_simp
  ring

lemma tanh_leaf_affine (beta y : ℝ) (s : IsingSpin) :
    Real.tanh (y + beta * spinSign s) =
      (Real.tanh (y + beta) + Real.tanh (y - beta)) / 2 +
        (Real.tanh beta * responseAttenuation (Real.tanh beta) y) * spinSign s := by
  have hs : Real.tanh beta * responseAttenuation (Real.tanh beta) y =
      (Real.tanh (y + beta) - Real.tanh (y - beta)) / 2 := by
    simpa only [responseAttenuation, mul_div_assoc] using (tanh_field_difference_eq beta y).symm
  rw [hs]
  cases s <;> simp only [spinSign_neg, spinSign_pos, mul_neg_one, mul_one, ← sub_eq_add_neg] <;> ring

theorem expectation_mul_leaf_eq {A : Type*} [Fintype A]
    (E f : A → ℝ) (parent : A → IsingSpin) (beta y : ℝ) :
    expectation (energy E parent beta y) (fun s => f s.1 * spinSign s.2) =
    expectation (energy E parent beta y)
      (fun s => f s.1 * Real.tanh (y + beta * spinSign (parent s.1))) := by
  unfold expectation
  congr 1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  have he (l : IsingSpin) : energy E parent beta y (a, l) =
      E a + (y + beta * spinSign (parent a)) * spinSign l := by
    unfold energy
    ring
  simp_rw [he]
  simp only [Real.exp_add]
  calc
    _ = (f a * Real.exp (E a)) *
        ∑ l : IsingSpin, spinSign l *
          Real.exp ((y + beta * spinSign (parent a)) * spinSign l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = _ := by
      rw [spin_exponential_mean, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring

theorem expectation_mul_leaf_affine {A : Type*} [Fintype A]
    (E f : A → ℝ) (parent : A → IsingSpin) (beta y : ℝ) :
    expectation (energy E parent beta y) (fun s => f s.1 * spinSign s.2) =
      ((Real.tanh (y + beta) + Real.tanh (y - beta)) / 2) *
        expectation (energy E parent beta y) (fun s => f s.1) +
      (Real.tanh beta * responseAttenuation (Real.tanh beta) y) *
        expectation (energy E parent beta y) (fun s => f s.1 * spinSign (parent s.1)) := by
  rw [expectation_mul_leaf_eq]
  simp_rw [tanh_leaf_affine]
  have he : (fun s : A × IsingSpin => f s.1 *
      ((Real.tanh (y + beta) + Real.tanh (y - beta)) / 2 +
        (Real.tanh beta * responseAttenuation (Real.tanh beta) y) * spinSign (parent s.1))) =
      (fun s => ((Real.tanh (y + beta) + Real.tanh (y - beta)) / 2) * f s.1 +
        (Real.tanh beta * responseAttenuation (Real.tanh beta) y) *
          (f s.1 * spinSign (parent s.1))) := by
    funext s
    ring
  rw [he, expectation_add, expectation_const_mul, expectation_const_mul]

theorem covariance_leaf_eq_mul_parent {A : Type*} [Fintype A] [Nonempty A]
    (E f : A → ℝ) (parent : A → IsingSpin) (beta y : ℝ) :
    covariance (energy E parent beta y) (fun s => f s.1) (fun s => spinSign s.2) =
      (Real.tanh beta * responseAttenuation (Real.tanh beta) y) *
        covariance (energy E parent beta y) (fun s => f s.1)
          (fun s => spinSign (parent s.1)) := by
  let : Nonempty IsingSpin := ⟨.neg⟩
  have hmean := expectation_mul_leaf_affine E (fun _ => 1) parent beta y
  simp only [one_mul, expectation_const, mul_one] at hmean
  unfold covariance
  rw [expectation_mul_leaf_affine, hmean]
  ring

lemma spin_variance_bounds {A : Type*} [Fintype A] [Nonempty A]
    (E : A → ℝ) (spin : A → IsingSpin) :
    0 ≤ 1 - expectation E (fun a => spinSign (spin a)) ^ 2 ∧
      1 - expectation E (fun a => spinSign (spin a)) ^ 2 ≤ 1 := by
  constructor
  · have h := FinitePosterior.variance_nonneg E (fun _ => 0)
      (fun a => spinSign (spin a)) 0
    simpa only [spinSign_sq, FinitePosterior.mean_const, ← expectation_eq_mean_zero] using h
  · nlinarith [sq_nonneg (expectation E (fun a => spinSign (spin a)))]

theorem covariance_parent_leaf {A : Type*} [Fintype A] [Nonempty A]
    (E : A → ℝ) (parent : A → IsingSpin) (beta y : ℝ) :
    covariance (energy E parent beta y) (fun s => spinSign (parent s.1))
      (fun s => spinSign s.2) =
      (Real.tanh beta * responseAttenuation (Real.tanh beta) y) *
        (1 - expectation (energy E parent beta y) (fun s => spinSign (parent s.1)) ^ 2) := by
  let : Nonempty IsingSpin := ⟨.neg⟩
  rw [covariance_leaf_eq_mul_parent E (fun a => spinSign (parent a)) parent beta y]
  simp only [covariance, spinSign_mul_self, expectation_const, pow_two]

theorem covariance_parent_leaf_bounds {A : Type*} [Fintype A] [Nonempty A]
    (E : A → ℝ) (parent : A → IsingSpin) {beta : ℝ} (hbeta : 0 ≤ beta) (y : ℝ) :
    0 ≤ covariance (energy E parent beta y) (fun s => spinSign (parent s.1))
      (fun s => spinSign s.2) ∧
    covariance (energy E parent beta y) (fun s => spinSign (parent s.1))
      (fun s => spinSign s.2) ≤ Real.tanh beta := by
  let : Nonempty IsingSpin := ⟨.neg⟩
  have ht : 0 ≤ Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos beta).le
  have ha := responseAttenuation_pos (Real.tanh_sq_lt_one beta).le y
  have ha1 := responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le y
  have hv := spin_variance_bounds (energy E parent beta y) (fun s => parent s.1)
  rw [covariance_parent_leaf]
  constructor
  · exact mul_nonneg (mul_nonneg ht ha.le) hv.1
  · calc
      _ ≤ Real.tanh beta * responseAttenuation (Real.tanh beta) y :=
        mul_le_of_le_one_right (mul_nonneg ht ha.le) hv.2
      _ ≤ Real.tanh beta := mul_le_of_le_one_right ht ha1

end Problem367.LeafGibbs

end

end OAI
