import Mathlib
import OAI.Probability.SKGap.Localization.Character

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff

lemma one_add_pow_le_exp (q : ℝ) (hq : 0 ≤ q) (n : ℕ) :
    (1 + q) ^ n ≤ Real.exp ((n : ℝ) * q) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp q]) _

lemma kernel_apply {n : ℕ} (A : Observables n →L[ℝ] Observables n)
    (f : Observables n) (x : Spin n) :
    ∑ y : Spin n, A (fun z => if z = y then 1 else 0) x * f y = A f x := by
  have hf : (∑ y : Spin n, f y • (fun z => if z = y then (1 : ℝ) else 0)) = f := by
    funext z
    simp
  calc
    _ = A (∑ y : Spin n, f y • (fun z => if z = y then (1 : ℝ) else 0)) x := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = A f x := by rw [hf]

lemma generator_mul {n : ℕ} (J : Interaction n) (f g : Observables n) (x : Spin n) :
    generator J (fun y => f y * g y) x =
      f x * generator J g x + g x * generator J f x +
        2 * ∑ i, (1 - mean J x i * spin x i) * halfDiff i f x * halfDiff i g x := by
  simp only [generator, halfDiff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hx := spin_sq x i
  linear_combination 2 * halfDiff i f x * halfDiff i g x * hx

noncomputable def magnetization {n : ℕ} (x : Spin n) : ℝ := ∑ i, spin x i

def plusSpin (n : ℕ) : Spin n := fun _ => true

@[simp] lemma magnetization_plus (n : ℕ) : magnetization (plusSpin n) = (n : ℝ) := by
  simp [magnetization, spin, plusSpin]

@[simp] lemma character_singleton {n : ℕ} (i : Fin n) (x : Spin n) :
    character {i} x = spin x i := by simp [character]

@[simp] lemma halfDiff_magnetization {n : ℕ} (i : Fin n) (x : Spin n) :
    halfDiff i magnetization x = 1 := by
  change halfDiff i (fun y => ∑ j, spin y j) x = _
  simp only [halfDiff_sum, halfDiff_spin, Fintype.sum_ite_eq]

lemma generator_zero_magnetization {n : ℕ} :
    generatorCLM (0 : Interaction n) magnetization = (-1 : ℝ) • magnetization := by
  funext x
  change generator (0 : Interaction n) magnetization x = -1 * magnetization x
  simp [generator, magnetization]

noncomputable def centeredMagnetizationSq {n : ℕ} (x : Spin n) : ℝ :=
  magnetization x ^ 2 - (n : ℝ)

lemma generator_zero_centeredMagnetizationSq {n : ℕ} :
    generatorCLM (0 : Interaction n) centeredMagnetizationSq =
      (-2 : ℝ) • centeredMagnetizationSq := by
  funext x
  have hg := generator_mul (0 : Interaction n) magnetization magnetization x
  have hl : generator (0 : Interaction n) magnetization x = -magnetization x := by
    have h := congrFun (generator_zero_magnetization (n := n)) x
    change generator (0 : Interaction n) magnetization x = -1 * magnetization x at h
    simpa only [neg_one_mul] using h
  simp only [mean_zero, zero_mul, sub_zero, halfDiff_magnetization, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hl] at hg
  change generator (0 : Interaction n) centeredMagnetizationSq x =
    -2 * centeredMagnetizationSq x
  have heq : generator (0 : Interaction n) centeredMagnetizationSq x =
      generator (0 : Interaction n) (fun y => magnetization y * magnetization y) x := by
    change generator (0 : Interaction n) (fun y => magnetization y ^ 2 - (n : ℝ)) x = _
    simp only [generator, halfDiff_sub, halfDiff_const, sub_zero, pow_two]
  rw [heq, hg]
  unfold centeredMagnetizationSq
  ring

lemma semigroup_zero_magnetization {n : ℕ} (t : ℝ) :
    semigroup (0 : Interaction n) t magnetization = Real.exp (-t) • magnetization := by
  apply exp_apply_of_eigenvector
  rw [smul_apply, generator_zero_magnetization, smul_smul]
  simp

lemma semigroup_zero_centeredMagnetizationSq {n : ℕ} (t : ℝ) :
    semigroup (0 : Interaction n) t centeredMagnetizationSq =
      Real.exp (-2 * t) • centeredMagnetizationSq := by
  apply exp_apply_of_eigenvector
  rw [smul_apply, generator_zero_centeredMagnetizationSq, smul_smul]
  congr 1
  ring

lemma pow_apply_of_eigenvector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (f : E) (a : ℝ) (ha : A f = a • f) (k : ℕ) :
    (A ^ k) f = a ^ k • f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, ha, smul_smul, pow_succ]

lemma attempt_pow_zero_magnetization {n : ℕ} (k : ℕ) :
    (attemptLM (0 : Interaction n) ^ k) magnetization =
      (1 - (n : ℝ)⁻¹) ^ k • magnetization := by
  apply pow_apply_of_eigenvector
  change magnetization + (n : ℝ)⁻¹ • generatorCLM (0 : Interaction n) magnetization = _
  rw [generator_zero_magnetization, smul_smul]
  module

lemma attempt_pow_zero_centeredMagnetizationSq {n : ℕ} (k : ℕ) :
    (attemptLM (0 : Interaction n) ^ k) centeredMagnetizationSq =
      (1 - 2 / (n : ℝ)) ^ k • centeredMagnetizationSq := by
  apply pow_apply_of_eigenvector
  change centeredMagnetizationSq +
    (n : ℝ)⁻¹ • generatorCLM (0 : Interaction n) centeredMagnetizationSq = _
  rw [generator_zero_centeredMagnetizationSq, smul_smul]
  module

lemma uniform_magnetization_second_moment (n : ℕ) :
    ∑ x : Spin n, gibbs (0 : Interaction n) x * magnetization x ^ 2 = (n : ℝ) := by
  have hinner (i j : Fin n) : (∑ x : Spin n, spin x i * spin x j) =
      if i = j then (2 : ℝ) ^ n else 0 := by
    simpa only [character_singleton, Finset.singleton_inj] using character_inner {i} {j}
  simp only [gibbs_zero, ← Finset.mul_sum]
  have hsum : (∑ x : Spin n, magnetization x ^ 2) = (n : ℝ) * (2 : ℝ) ^ n := by
    simp only [magnetization, pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Spin n))), hinner,
      Fintype.sum_ite_eq]
    simp
  rw [hsum]
  field_simp

lemma totalVariation_nonneg {n : ℕ} (p q : Spin n → ℝ) : 0 ≤ totalVariation p q :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

lemma totalVariation_le_one {n : ℕ} (p q : Spin n → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (hp1 : ∑ x, p x = 1)
    (hq1 : ∑ x, q x = 1) : totalVariation p q ≤ 1 := by
  have hs : ∑ x, |p x - q x| ≤ ∑ x, (p x + q x) := by
    apply Finset.sum_le_sum
    intro x _
    exact abs_le.mpr ⟨by linarith [hp x, hq x], by linarith [hp x, hq x]⟩
  rw [Finset.sum_add_distrib, hp1, hq1] at hs
  unfold totalVariation
  linarith

lemma event_difference_le_totalVariation {n : ℕ} (p q : Spin n → ℝ)
    (hpq : ∑ x, p x = ∑ x, q x) (A : Spin n → Prop) [DecidablePred A] :
    (∑ x, if A x then p x else 0) - (∑ x, if A x then q x else 0) ≤
      totalVariation p q := by
  have h (x : Spin n) :
      2 * ((if A x then p x else 0) - (if A x then q x else 0)) ≤
        |p x - q x| + (p x - q x) := by
    split_ifs <;> linarith [le_abs_self (p x - q x), neg_le_abs (p x - q x)]
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Spin n))) => h x)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, hpq,
    sub_self, add_zero] at hs
  unfold totalVariation
  linarith

lemma totalVariation_lower_from_quadratic_test {n : ℕ} (p q f : Spin n → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1)
    (m V : ℝ) (hm : 0 < m)
    (hpV : ∑ x, p x * (f x - m) ^ 2 ≤ V)
    (hqV : ∑ x, q x * f x ^ 2 ≤ V) :
    m ^ 2 * (1 - totalVariation p q) ≤ 8 * V := by
  let A : Spin n → Prop := fun x => m / 2 ≤ f x
  have hP (x : Spin n) :
      (m ^ 2 / 4) * (p x - if A x then p x else 0) ≤ p x * (f x - m) ^ 2 := by
    by_cases hx : A x
    · simp only [hx, ↓reduceIte, sub_self, mul_zero]
      exact mul_nonneg (hp x) (sq_nonneg _)
    · have hfx : f x < m / 2 := lt_of_not_ge hx
      simp only [hx, ↓reduceIte, sub_zero]
      have hs : m ^ 2 / 4 ≤ (f x - m) ^ 2 := by nlinarith [sq_nonneg (f x - m / 2)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs (hp x)
  have hQ (x : Spin n) :
      (m ^ 2 / 4) * (if A x then q x else 0) ≤ q x * f x ^ 2 := by
    by_cases hx : A x
    · have hfx : m / 2 ≤ f x := hx
      simp only [hx, ↓reduceIte]
      have hs : m ^ 2 / 4 ≤ f x ^ 2 := by nlinarith [sq_nonneg (f x - m / 2)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs (hq x)
    · simp only [hx, ↓reduceIte, mul_zero]
      exact mul_nonneg (hq x) (sq_nonneg _)
  have hpbd := (Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Spin n))) => hP x)).trans hpV
  have hqbd := (Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Spin n))) => hQ x)).trans hqV
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, hp1] at hpbd
  simp only [← Finset.mul_sum] at hqbd
  have hd := event_difference_le_totalVariation p q (hp1.trans hq1.symm) A
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ m ^ 2 / 4 by positivity)
  nlinarith

lemma quadratic_centered_identity {n : ℕ} (p f : Spin n → ℝ) (m b a : ℝ)
    (hp : ∑ y, p y = 1) (hm : ∑ y, p y * f y = m)
    (hs : ∑ y, p y * (f y ^ 2 - b) = a) :
    ∑ y, p y * (f y - m) ^ 2 = b + a - m ^ 2 := by
  have he (y : Spin n) : p y * (f y - m) ^ 2 =
      p y * (f y ^ 2 - b) - 2 * m * (p y * f y) + (b + m ^ 2) * p y := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hs, hm, hp]
  ring

lemma continuous_zero_variance {n : ℕ} (t : ℝ) :
    ∑ y, continuousKernel (0 : Interaction n) t (plusSpin n) y *
      (magnetization y - (n : ℝ) * Real.exp (-t)) ^ 2 ≤ (n : ℝ) := by
  have hm : ∑ y, continuousKernel (0 : Interaction n) t (plusSpin n) y *
      magnetization y = (n : ℝ) * Real.exp (-t) := by
    change (∑ y, semigroup (0 : Interaction n) t (fun z => if z = y then 1 else 0)
      (plusSpin n) * magnetization y) = _
    rw [kernel_apply, semigroup_zero_magnetization]
    simp [mul_comm]
  have hs : ∑ y, continuousKernel (0 : Interaction n) t (plusSpin n) y *
      (magnetization y ^ 2 - (n : ℝ)) =
        Real.exp (-2 * t) * ((n : ℝ) ^ 2 - n) := by
    change (∑ y, semigroup (0 : Interaction n) t (fun z => if z = y then 1 else 0)
      (plusSpin n) * centeredMagnetizationSq y) = _
    rw [kernel_apply, semigroup_zero_centeredMagnetizationSq]
    simp [centeredMagnetizationSq]
  rw [quadratic_centered_identity _ _ _ _ _ (continuousKernel_sum _ _ _) hm hs]
  have he : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [he]
  nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (Real.exp (-t)))]

lemma discrete_zero_variance {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    ∑ y, discreteKernel (0 : Interaction n) k (plusSpin n) y *
      (magnetization y - (n : ℝ) * (1 - (n : ℝ)⁻¹) ^ k) ^ 2 ≤ (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hi : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hi1 : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hn0).mpr (by linarith)
  have hi2 : 2 / (n : ℝ) ≤ 1 := (div_le_iff₀ hn0).mpr (by linarith)
  have hm : ∑ y, discreteKernel (0 : Interaction n) k (plusSpin n) y *
      magnetization y = (n : ℝ) * (1 - (n : ℝ)⁻¹) ^ k := by
    change (∑ y, (attemptLM (0 : Interaction n) ^ k)
      (fun z => if z = y then 1 else 0) (plusSpin n) * magnetization y) = _
    rw [kernel_apply, attempt_pow_zero_magnetization]
    simp [mul_comm]
  have hs : ∑ y, discreteKernel (0 : Interaction n) k (plusSpin n) y *
      (magnetization y ^ 2 - (n : ℝ)) =
        (1 - 2 / (n : ℝ)) ^ k * ((n : ℝ) ^ 2 - n) := by
    change (∑ y, (attemptLM (0 : Interaction n) ^ k)
      (fun z => if z = y then 1 else 0) (plusSpin n) * centeredMagnetizationSq y) = _
    rw [kernel_apply, attempt_pow_zero_centeredMagnetizationSq]
    simp [centeredMagnetizationSq]
  rw [quadratic_centered_identity _ _ _ _ _ (discreteKernel_sum _ _ _) hm hs]
  have hbase : 1 - 2 / (n : ℝ) ≤ (1 - (n : ℝ)⁻¹) ^ 2 := by
    rw [div_eq_mul_inv]; nlinarith [sq_nonneg (n : ℝ)⁻¹]
  have hpow : (1 - 2 / (n : ℝ)) ^ k ≤ ((1 - (n : ℝ)⁻¹) ^ k) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by linarith) hbase k
  have hn2 : 0 ≤ (n : ℝ) ^ 2 - n := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hpow hn2
  have hs0 := sq_nonneg ((1 - (n : ℝ)⁻¹) ^ k)
  nlinarith [mul_nonneg (Nat.cast_nonneg n) hs0]

lemma continuous_zero_lower {n : ℕ} (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    1 - 8 * Real.exp (2 * t) / (n : ℝ) ≤
      totalVariation (continuousKernel (0 : Interaction n) t (plusSpin n)) (gibbs 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : 0 < (n : ℝ) * Real.exp (-t) := mul_pos hn' (Real.exp_pos _)
  have h := totalVariation_lower_from_quadratic_test
    (continuousKernel (0 : Interaction n) t (plusSpin n)) (gibbs 0) magnetization
    (continuousKernel_nonneg _ _ ht _) (fun y => le_of_lt (gibbs_pos _ y))
    (continuousKernel_sum _ _ _) (gibbs_sum _) _ _ hm (continuous_zero_variance t)
    (le_of_eq (uniform_magnetization_second_moment n))
  have he : Real.exp (-t) ^ 2 * Real.exp (2 * t) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 1; congr 1; ring
  have hmul := mul_le_mul_of_nonneg_right h (le_of_lt (Real.exp_pos (2 * t)))
  have heq : ((n : ℝ) * Real.exp (-t)) ^ 2 * Real.exp (2 * t) = (n : ℝ) ^ 2 := by
    rw [mul_pow, mul_assoc, he, mul_one]
  have hmul' : (n : ℝ) ^ 2 * (1 - totalVariation
      (continuousKernel (0 : Interaction n) t (plusSpin n)) (gibbs 0)) ≤
      8 * n * Real.exp (2 * t) := by
    calc
      _ = ((n : ℝ) * Real.exp (-t)) ^ 2 * (1 - totalVariation
          (continuousKernel (0 : Interaction n) t (plusSpin n)) (gibbs 0)) *
          Real.exp (2 * t) := by rw [mul_right_comm, heq]
      _ ≤ _ := hmul
  have hscaled : (n : ℝ) * ((1 - totalVariation
      (continuousKernel (0 : Interaction n) t (plusSpin n)) (gibbs 0)) * n) ≤
      (n : ℝ) * (8 * Real.exp (2 * t)) := by nlinarith only [hmul']
  have hsmall := (mul_le_mul_iff_right₀ hn').mp hscaled
  have hdiv := (le_div_iff₀ hn').mpr hsmall
  linarith

lemma exp_neg_inv_le_one_sub_inv (a : ℝ) (ha : 1 < a) :
    Real.exp (-1 / (a - 1)) ≤ 1 - a⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hsub : 0 < a - 1 := by linarith
  have h := Real.add_one_le_exp (1 / (a - 1))
  have heq : 1 / (a - 1) + 1 = a / (a - 1) := by field_simp; ring
  rw [heq] at h
  have hi := one_div_le_one_div_of_le (div_pos ha0 hsub) h
  rw [one_div, ← Real.exp_neg] at hi
  calc
    _ = Real.exp (-(1 / (a - 1))) := by congr 1; ring
    _ ≤ 1 / (a / (a - 1)) := hi
    _ = 1 - a⁻¹ := by field_simp

lemma discrete_zero_lower {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    1 - 8 * Real.exp (2 * (k : ℝ) / ((n : ℝ) - 1)) / (n : ℝ) ≤
      totalVariation (discreteKernel (0 : Interaction n) k (plusSpin n)) (gibbs 0) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hb := exp_neg_inv_le_one_sub_inv (n : ℝ) hn'
  have hpow : Real.exp (-(k : ℝ) / ((n : ℝ) - 1)) ≤ (1 - (n : ℝ)⁻¹) ^ k := by
    calc
      _ = Real.exp (-1 / ((n : ℝ) - 1)) ^ k := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hb k
  have hp : 0 < (1 - (n : ℝ)⁻¹) ^ k := lt_of_lt_of_le (Real.exp_pos _) hpow
  have h := totalVariation_lower_from_quadratic_test
    (discreteKernel (0 : Interaction n) k (plusSpin n)) (gibbs 0) magnetization
    (discreteKernel_nonneg _ _ _) (fun y => le_of_lt (gibbs_pos _ y))
    (discreteKernel_sum _ _ _) (gibbs_sum _) _ _ (mul_pos hn0 hp)
    (discrete_zero_variance hn k) (le_of_eq (uniform_magnetization_second_moment n))
  have he : Real.exp (-(k : ℝ) / ((n : ℝ) - 1)) ^ 2 *
      Real.exp (2 * (k : ℝ) / ((n : ℝ) - 1)) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 1; congr 1; ring
  have hbE : 1 ≤ ((1 - (n : ℝ)⁻¹) ^ k) ^ 2 *
      Real.exp (2 * (k : ℝ) / ((n : ℝ) - 1)) := by
    calc
      1 = Real.exp (-(k : ℝ) / ((n : ℝ) - 1)) ^ 2 *
          Real.exp (2 * (k : ℝ) / ((n : ℝ) - 1)) := he.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hpow 2) (le_of_lt (Real.exp_pos _))
  have hTV := totalVariation_le_one
    (discreteKernel (0 : Interaction n) k (plusSpin n)) (gibbs 0)
    (discreteKernel_nonneg _ _ _) (fun y => le_of_lt (gibbs_pos _ y))
    (discreteKernel_sum _ _ _) (gibbs_sum _)
  have hl := mul_le_mul_of_nonneg_right hbE
    (mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hTV))
  have hr := mul_le_mul_of_nonneg_right h
    (le_of_lt (Real.exp_pos (2 * (k : ℝ) / ((n : ℝ) - 1))))
  have hs : (n : ℝ) * ((1 - totalVariation
      (discreteKernel (0 : Interaction n) k (plusSpin n)) (gibbs 0)) * n) ≤
      (n : ℝ) * (8 * Real.exp (2 * (k : ℝ) / ((n : ℝ) - 1))) := by
    nlinarith only [hl, hr]
  have hsmall := (mul_le_mul_iff_right₀ hn0).mp hs
  have hdiv := (le_div_iff₀ hn0).mpr hsmall
  linarith

lemma worstContinuous_nonneg {n : ℕ} (J : Interaction n) (t : ℝ) :
    0 ≤ worstContinuous J t := by
  unfold worstContinuous
  exact (totalVariation_nonneg _ _).trans
    (Finset.le_sup' (fun x => totalVariation (continuousKernel J t x) (gibbs J))
      (Finset.mem_univ (plusSpin n)))

lemma worstDiscrete_nonneg {n : ℕ} (J : Interaction n) (k : ℕ) :
    0 ≤ worstDiscrete J k := by
  unfold worstDiscrete
  exact (totalVariation_nonneg _ _).trans
    (Finset.le_sup' (fun x => totalVariation (discreteKernel J k x) (gibbs J))
      (Finset.mem_univ (plusSpin n)))

lemma worstContinuous_le_one {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t) :
    worstContinuous J t ≤ 1 := by
  apply Finset.sup'_le
  intro x _
  exact totalVariation_le_one _ _ (continuousKernel_nonneg _ _ ht _)
    (fun y => le_of_lt (gibbs_pos _ y)) (continuousKernel_sum _ _ _) (gibbs_sum _)

lemma worstDiscrete_le_one {n : ℕ} (J : Interaction n) (k : ℕ) :
    worstDiscrete J k ≤ 1 := by
  apply Finset.sup'_le
  intro x _
  exact totalVariation_le_one _ _ (discreteKernel_nonneg _ _ _)
    (fun y => le_of_lt (gibbs_pos _ y)) (discreteKernel_sum _ _ _) (gibbs_sum _)

lemma worstContinuous_zero_lower {n : ℕ} (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    1 - 8 * Real.exp (2 * t) / (n : ℝ) ≤ worstContinuous (0 : Interaction n) t := by
  unfold worstContinuous
  exact (continuous_zero_lower hn t ht).trans
    (Finset.le_sup' (fun x => totalVariation (continuousKernel 0 t x) (gibbs 0))
      (Finset.mem_univ _))

lemma worstDiscrete_zero_lower {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    1 - 8 * Real.exp (2 * (k : ℝ) / ((n : ℝ) - 1)) / (n : ℝ) ≤
      worstDiscrete (0 : Interaction n) k := by
  unfold worstDiscrete
  exact (discrete_zero_lower hn k).trans
    (Finset.le_sup' (fun x => totalVariation (discreteKernel 0 k x) (gibbs 0))
      (Finset.mem_univ _))

lemma worstContinuous_zero_upper {n : ℕ} (t : ℝ) :
    worstContinuous (0 : Interaction n) t ≤
      Real.sqrt (Real.exp ((n : ℝ) * Real.exp (-2 * t)) - 1) / 2 := by
  apply Finset.sup'_le
  intro x _
  have h := (continuous_zero_tv_sq_le t x).trans
    (sub_le_sub_right (one_add_pow_le_exp _ (le_of_lt (Real.exp_pos _)) n) 1)
  have hnonneg : 0 ≤ Real.exp ((n : ℝ) * Real.exp (-2 * t)) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (Nat.cast_nonneg n)
      (le_of_lt (Real.exp_pos _))))
  have hs := Real.sq_sqrt hnonneg
  have hs0 := Real.sqrt_nonneg (Real.exp ((n : ℝ) * Real.exp (-2 * t)) - 1)
  nlinarith [totalVariation_nonneg (continuousKernel (0 : Interaction n) t x) (gibbs 0)]

lemma worstDiscrete_zero_upper {n : ℕ} (hn : 0 < n) (k : ℕ) :
    worstDiscrete (0 : Interaction n) k ≤
      Real.sqrt (Real.exp ((n : ℝ) * Real.exp (-2 * (k : ℝ) / n)) - 1) / 2 := by
  apply Finset.sup'_le
  intro x _
  have h := (discrete_zero_tv_sq_le hn k x).trans
    (sub_le_sub_right (one_add_pow_le_exp _ (le_of_lt (Real.exp_pos _)) n) 1)
  have hnonneg : 0 ≤ Real.exp ((n : ℝ) * Real.exp (-2 * (k : ℝ) / n)) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (Nat.cast_nonneg n)
      (le_of_lt (Real.exp_pos _))))
  have hs := Real.sq_sqrt hnonneg
  have hs0 := Real.sqrt_nonneg (Real.exp ((n : ℝ) * Real.exp (-2 * (k : ℝ) / n)) - 1)
  nlinarith [totalVariation_nonneg (discreteKernel (0 : Interaction n) k x) (gibbs 0)]

open Filter Topology

end SKGapCutoff
end

end OAI
