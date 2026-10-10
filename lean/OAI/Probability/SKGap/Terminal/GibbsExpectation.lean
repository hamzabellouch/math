import Mathlib
import OAI.Probability.SKGap.Localization.Character

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff
open Filter Topology
noncomputable def gibbsExpectation {n : ℕ} (J : Interaction n) (f : Observables n) : ℝ :=
  ∑ x, gibbs J x * f x
noncomputable def gibbsVariance {n : ℕ} (J : Interaction n) (f : Observables n) : ℝ :=
  gibbsExpectation J (fun x => (f x - gibbsExpectation J f) ^ 2)
noncomputable def siteVariance {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  1 - mean J x i ^ 2
noncomputable def dirichlet {n : ℕ} (J : Interaction n) (f g : Observables n) : ℝ :=
  gibbsExpectation J (fun x => ∑ i, siteVariance J x i * halfDiff i f x * halfDiff i g x)
def HasGap {n : ℕ} (J : Interaction n) (γ : ℝ) : Prop :=
  ∀ f : Observables n, γ * gibbsVariance J f ≤ dirichlet J f f

def QuenchedGap (β : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ Tendsto (fun n => (disorderLaw β n)
    {g | HasGap (sampledInteraction g) γ}) atTop (nhds 1)

def flip {n : ℕ} (x : Spin n) (i : Fin n) : Spin n := replace x i (!x i)

@[simp] lemma flip_flip {n : ℕ} (x : Spin n) (i : Fin n) : flip (flip x i) i = x := by
  simp [flip]

@[simp] lemma spin_flip_self {n : ℕ} (x : Spin n) (i : Fin n) :
    spin (flip x i) i = -spin x i := by
  cases h : x i <;> simp [flip, spin, h]

lemma spin_flip {n : ℕ} (x : Spin n) (i j : Fin n) :
    spin (flip x i) j = spin x j - if j = i then 2 * spin x i else 0 := by
  by_cases h : j = i
  · subst j; simp; ring
  · simp [flip, spin_replace_of_ne x h, h]

lemma field_flip {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) (i : Fin n) : field J (flip x i) i = field J x i := by
  simp only [field, spin_flip, mul_sub, Finset.sum_sub_distrib]
  simp [mul_ite, hdiag]

@[simp] lemma mean_flip {n : ℕ} (J : Interaction n) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) (i : Fin n) : mean J (flip x i) i = mean J x i := by
  simp only [mean, field_flip J hdiag]

lemma energy_flip {n : ℕ} (J : Interaction n) (hJ : ∀ i j, J i j = J j i)
    (hdiag : ∀ i, J i i = 0) (x : Spin n) (i : Fin n) :
    energy J (flip x i) = energy J x - 2 * spin x i * field J x i := by
  have hr : ∑ j, spin x j * J j i = field J x i := by
    simp only [field, hJ, mul_comm]
  unfold energy
  simp only [spin_flip, sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, hdiag]
  simp only [← Finset.sum_mul, hr]
  simp only [mul_assoc, ← Finset.mul_sum, field]
  ring

noncomputable def flipRate {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  (1 - spin x i * mean J x i) / 2

lemma generator_flip {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    generator J f x = ∑ i, flipRate J x i * (f (flip x i) - f x) := by
  apply Finset.sum_congr rfl
  intro i _
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, flipRate, flip, Bool.not_false,
      halfDiff]
    rw [hx]; ring
  · simp only [spin, hi, ↓reduceIte, flipRate, flip, Bool.not_true, halfDiff]
    rw [hx]; ring

lemma exp_two_mul_one_sub_tanh (a : ℝ) :
    Real.exp (2 * a) * (1 - Real.tanh a) = 1 + Real.tanh a := by
  rw [Real.tanh_eq, show 2 * a = a + a by ring, Real.exp_add, Real.exp_neg]
  have he := Real.exp_pos a
  field_simp
  nlinarith

lemma exp_neg_two_mul_one_add_tanh (a : ℝ) :
    Real.exp (-2 * a) * (1 + Real.tanh a) = 1 - Real.tanh a := by
  simpa only [mul_neg, neg_mul, Real.tanh_neg, sub_neg_eq_add, sub_eq_add_neg, neg_neg] using
    exp_two_mul_one_sub_tanh (-a)

lemma gibbs_detailed_balance {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) (i : Fin n) :
    gibbs J (flip x i) * flipRate J (flip x i) i = gibbs J x * flipRate J x i := by
  simp only [gibbs, energy_flip J hJ hdiag, flipRate, spin_flip_self,
    Real.exp_sub, mean, field_flip J hdiag]
  cases hi : x i
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, neg_neg, neg_mul, mul_one,
      one_mul, mul_neg, Real.exp_neg]
    have h := exp_two_mul_one_sub_tanh (field J x i)
    field_simp [ne_of_gt (partition_pos J)]
    nlinarith only [h]
  · simp only [spin, hi, ↓reduceIte, mul_one, one_mul, neg_mul, sub_neg_eq_add]
    have h := exp_two_mul_one_sub_tanh (field J x i)
    field_simp [ne_of_gt (partition_pos J)]
    nlinarith only [h]

def flipEquiv (n : ℕ) (i : Fin n) : Spin n ≃ Spin n where
  toFun x := flip x i
  invFun x := flip x i
  left_inv x := flip_flip x i
  right_inv x := flip_flip x i

lemma sum_flip {n : ℕ} (i : Fin n) (f : Observables n) :
    ∑ x, f (flip x i) = ∑ x, f x := (flipEquiv n i).sum_comp f

@[simp] lemma halfDiff_flip {n : ℕ} (i : Fin n) (f : Observables n) (x : Spin n) :
    halfDiff i f (flip x i) = halfDiff i f x := by simp [flip]

lemma flip_sub {n : ℕ} (i : Fin n) (f : Observables n) (x : Spin n) :
    f (flip x i) - f x = -2 * spin x i * halfDiff i f x := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [flip, hi, Bool.not_false, spin, Bool.false_eq_true, ↓reduceIte, halfDiff]
    rw [hx]; ring
  · simp only [flip, hi, Bool.not_true, spin, ↓reduceIte, halfDiff]
    rw [hx]; ring

lemma gibbs_flip_integral {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (i : Fin n) (f : Observables n) :
    ∑ x, gibbs J x * flipRate J x i * f (flip x i) =
      ∑ x, gibbs J x * flipRate J x i * f x := by
  calc
    _ = ∑ x, gibbs J (flip x i) * flipRate J (flip x i) i * f (flip x i) := by
      simp_rw [gibbs_detailed_balance J hJ hdiag]
    _ = _ := sum_flip i (fun x => gibbs J x * flipRate J x i * f x)

lemma gibbs_generator_zero {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (f : Observables n) : gibbsExpectation J (generator J f) = 0 := by
  simp only [gibbsExpectation, generator_flip, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp only [← mul_assoc, gibbs_flip_integral J hJ hdiag, sub_self]

lemma gibbs_coordinate_mean {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (i : Fin n) (h : Observables n) (hinv : ∀ x, h (flip x i) = h x) :
    (∑ x, gibbs J x * spin x i * h x) = ∑ x, gibbs J x * mean J x i * h x := by
  have he := gibbs_flip_integral J hJ hdiag i (fun x => spin x i * h x)
  simp only [spin_flip_self, hinv] at he
  have hz : ∑ x, gibbs J x * flipRate J x i * spin x i * h x = 0 := by
    simp only [mul_neg, neg_mul, ← mul_assoc, Finset.sum_neg_distrib] at he
    linarith
  have hp (x : Spin n) : gibbs J x * flipRate J x i * spin x i * h x =
      (gibbs J x * spin x i * h x - gibbs J x * mean J x i * h x) / 2 := by
    unfold flipRate
    have hs := spin_sq x i
    nlinarith only [congrArg (fun a : ℝ => gibbs J x * mean J x i * h x * a) hs]
  simp_rw [hp] at hz
  rw [← Finset.sum_div, Finset.sum_sub_distrib] at hz
  linarith

lemma gibbs_edge_dirichlet {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (i : Fin n) (f g : Observables n) :
    (∑ x, gibbs J x * f x * (flipRate J x i * (g x - g (flip x i)))) =
      ∑ x, gibbs J x * siteVariance J x i * halfDiff i f x * halfDiff i g x := by
  let c (x : Spin n) := gibbs J x * flipRate J x i
  have hc (x : Spin n) : c (flip x i) = c x := gibbs_detailed_balance J hJ hdiag x i
  have he := sum_flip i (fun x => c x * f x * (g x - g (flip x i)))
  simp only [hc, flip_flip] at he
  have hpair : (∑ x, c x * f x * (g x - g (flip x i))) =
      (∑ x, c x * (f (flip x i) - f x) * (g (flip x i) - g x)) / 2 := by
    have hp (x : Spin n) : c x * (f (flip x i) - f x) * (g (flip x i) - g x) =
        c x * f (flip x i) * (g (flip x i) - g x) + c x * f x * (g x - g (flip x i)) := by ring
    simp_rw [hp]
    rw [Finset.sum_add_distrib, he]
    ring
  have hdf (x : Spin n) : c x * (f (flip x i) - f x) * (g (flip x i) - g x) =
      4 * c x * halfDiff i f x * halfDiff i g x := by
    rw [flip_sub, flip_sub]
    have hs := spin_sq x i
    nlinarith only [congrArg (fun a : ℝ => c x * halfDiff i f x * halfDiff i g x * a) hs]
  have hmean := gibbs_coordinate_mean J hJ hdiag i
    (fun x => mean J x i * halfDiff i f x * halfDiff i g x)
    (by intro x; rw [mean_flip J hdiag, halfDiff_flip, halfDiff_flip])
  have hp (x : Spin n) : (4 * c x * halfDiff i f x * halfDiff i g x) / 2 =
      gibbs J x * siteVariance J x i * halfDiff i f x * halfDiff i g x +
      gibbs J x * mean J x i * (mean J x i * halfDiff i f x * halfDiff i g x) -
      gibbs J x * spin x i * (mean J x i * halfDiff i f x * halfDiff i g x) := by
    dsimp [c, siteVariance, flipRate]
    ring
  calc
    _ = (∑ x, c x * f x * (g x - g (flip x i))) := by
      apply Finset.sum_congr rfl; intro x _; dsimp [c]; ring
    _ = _ := hpair
    _ = _ := by
      simp_rw [hdf]
      rw [Finset.sum_div]
      simp_rw [hp]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hmean]
      ring

theorem gibbs_dirichlet {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (f g : Observables n) :
    gibbsExpectation J (fun x => f x * -generator J g x) = dirichlet J f g := by
  simp only [gibbsExpectation, generator_flip, dirichlet, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x i =>
    gibbs J x * (siteVariance J x i * halfDiff i f x * halfDiff i g x))]
  apply Finset.sum_congr rfl
  intro i _
  convert gibbs_edge_dirichlet J hJ hdiag i f g using 1 <;>
    apply Finset.sum_congr rfl <;> intro x _ <;> ring

end SKGapCutoff

end

end OAI
