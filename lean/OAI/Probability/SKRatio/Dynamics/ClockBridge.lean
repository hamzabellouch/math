import Mathlib
import OAI.Probability.SKRatio.Calculus.GibbsMeanCLM
import OAI.Probability.SKRatio.Dynamics.SumPoissonMass

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter ProbabilityTheory SKRatioClock
namespace SKRatio.Calculus

lemma kernel_apply {n : ℕ} (K : Observables n →L[ℝ] Observables n)
    (f : Observables n) (x : Spin n) :
    (∑ y, K (fun z => if z = y then 1 else 0) x*f y) = K f x := by
  conv_rhs => rw [observable_basis f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

def attemptKernel {n : ℕ} (J : Interaction n) : Matrix (Spin n) (Spin n) ℝ :=
  fun x y => attemptLM J (fun z => if z = y then 1 else 0) x

lemma attemptKernel_nonneg {n : ℕ} (J : Interaction n) (x y : Spin n) :
    0 ≤ attemptKernel J x y := by
  classical
  exact attempt_nonneg J _ (fun z => by split_ifs <;> norm_num) x

lemma attemptKernel_eq_transition {n : ℕ} (g : Disorder n) :
    attemptKernel (coupling g) = transition g := by
  classical
  funext x y
  simp [attemptKernel, attempt_eq_transition, Matrix.mulVec, dotProduct]

noncomputable def residualAttempt {n : ℕ} (J : Interaction n) (q : ℝ) :
    Observables n →L[ℝ] Observables n :=
  q⁻¹ • (attemptLM J-(1-q) • 1)

lemma residualAttempt_apply {n : ℕ} (J : Interaction n) (q : ℝ)
    (f : Observables n) (x : Spin n) :
    residualAttempt J q f x = (attemptLM J f x-(1-q)*f x)/q := by
  simp [residualAttempt,div_eq_mul_inv,mul_comm]

lemma attempt_eq_lazy_residual {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0) :
    attemptLM J = q • residualAttempt J q+(1-q) • 1 := by
  simp only [residualAttempt,smul_smul,mul_inv_cancel₀ hq,one_smul,sub_add_cancel]

lemma residualAttempt_const {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (c : ℝ) : residualAttempt J q (fun _ => c) = fun _ => c := by
  ext x
  rw [residualAttempt_apply,attempt_const]
  field_simp
  ring

lemma residualAttempt_pow_const {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (k : ℕ) (c : ℝ) : (residualAttempt J q ^ k) (fun _ => c) = fun _ => c := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ',mul_apply_eq_comp,ih,residualAttempt_const J hq]

lemma residualAttempt_nonneg {n : ℕ} (J : Interaction n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ attemptKernel J x x)
    (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ residualAttempt J q f x := by
  rw [← kernel_apply (residualAttempt J q) f x]
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg _ (hf y)
  rw [residualAttempt_apply]
  apply div_nonneg _ hq.le
  by_cases hxy : x=y
  · subst y
    simpa [attemptKernel] using sub_nonneg.mpr (hhold x)
  · simpa only [hxy,↓reduceIte,mul_zero,sub_zero,attemptKernel] using
      attemptKernel_nonneg J x y

lemma residualAttempt_pow_nonneg {n : ℕ} (J : Interaction n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ attemptKernel J x x)
    (k : ℕ) (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ (residualAttempt J q ^ k) f x := by
  induction k generalizing x with
  | zero => exact hf x
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp]
    exact residualAttempt_nonneg J hq hhold _ (fun x => ih x) x

lemma residualAttempt_pow_abs_le {n : ℕ} (J : Interaction n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ attemptKernel J x x)
    (k : ℕ) (f : Observables n) (hf : ∀ x, |f x| ≤ 1) (x : Spin n) :
    |(residualAttempt J q ^ k) f x| ≤ 1 := by
  have hup := residualAttempt_pow_nonneg J hq hhold k (fun y => 1-f y)
    (fun y => by have := (abs_le.mp (hf y)).2; linarith) x
  have hlo := residualAttempt_pow_nonneg J hq hhold k (fun y => f y+1)
    (fun y => by have := (abs_le.mp (hf y)).1; linarith) x
  change 0 ≤ (residualAttempt J q ^ k) ((fun _ => 1)-f) x at hup
  change 0 ≤ (residualAttempt J q ^ k) (f+(fun _ => 1)) x at hlo
  rw [map_sub,residualAttempt_pow_const J hq.ne'] at hup
  rw [map_add,residualAttempt_pow_const J hq.ne'] at hlo
  simp only [Pi.add_apply,Pi.sub_apply] at hlo hup
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma residual_semigroup_uniformization {n : ℕ} (hn : 0 < n)
    (J : Interaction n) {q : ℝ} (hq : q ≠ 0) (t : ℝ) :
    semigroup J t = Real.exp (-(q*n*t)) •
      NormedSpace.exp ((q*n*t) • residualAttempt J q) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : t • generatorCLM J =
      (-(q*n*t)) • (1 : Observables n →L[ℝ] Observables n) +
        (q*n*t) • residualAttempt J q := by
    unfold residualAttempt attemptLM
    simp only [smul_smul,smul_sub,smul_add]
    have hc : q*n*t*q⁻¹ = (n:ℝ)*t := by field_simp
    have hc' : q*n*t*(q⁻¹*(n:ℝ)⁻¹) = t := by field_simp
    have hc'' : q*n*t*(q⁻¹*(1-q)) = (n:ℝ)*t*(1-q) := by field_simp
    rw [hc,hc',hc'']
    module
  let : NormedAlgebra ℚ (Observables n →L[ℝ] Observables n) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  unfold semigroup
  rw [heq,NormedSpace.exp_add_of_commute
    (((Commute.one_left (residualAttempt J q)).smul_left _).smul_right _),
    exp_smul_identity,smul_mul_assoc,one_mul]

lemma residual_poisson_hasSum {n : ℕ} (hn : 0 < n)
    (J : Interaction n) {q : ℝ} (hq : q ≠ 0) (t : ℝ)
    (f : Observables n) (x : Spin n) :
    HasSum (fun j => Clock.poissonMass (q*n*t) j*(residualAttempt J q ^ j) f x)
      (semigroup J t f x) := by
  have hs := (Pi.hasSum.mp (exp_apply_hasSum ((q*n*t) • residualAttempt J q) f) x).mul_left
    (Real.exp (-(q*n*t)))
  convert! hs using 1
  · funext j
    simp only [smul_pow,_root_.smul_apply,Pi.smul_apply,smul_eq_mul,Clock.poissonMass]
    ring
  · rw [residual_semigroup_uniformization hn J hq]
    rfl

lemma natCastCLM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (f : E) : (k : E →L[ℝ] E) f = (k:ℝ) • f := by
  induction k with
  | zero => simp
  | succ k ih => simp [Nat.cast_succ,ih,add_smul]

lemma residual_binomial_sum {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (M : ℕ) (f : Observables n) (x : Spin n) :
    (∑ j ∈ Finset.range (M+1), Clock.binomialMass q M j*
      (residualAttempt J q ^ j) f x) = (attemptLM J ^ M) f x := by
  rw [attempt_eq_lazy_residual J hq]
  rw [(((Commute.one_right (residualAttempt J q)).smul_left q).smul_right (1-q)).add_pow]
  simp only [_root_.sum_apply,smul_pow,one_pow,smul_mul_assoc,mul_smul_comm,mul_one,
    Clock.binomialMass,mul_apply_eq_comp,_root_.smul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [natCastCLM_apply,map_smul,Pi.smul_apply,smul_eq_mul]
  ring

lemma residual_binomial_hasSum {n : ℕ} (J : Interaction n) {q : ℝ} (hq : q ≠ 0)
    (M : ℕ) (f : Observables n) (x : Spin n) :
    HasSum (fun j => Clock.binomialMass q M j*(residualAttempt J q ^ j) f x)
      ((attemptLM J ^ M) f x) := by
  rw [← residual_binomial_sum J hq M f x]
  apply hasSum_sum_of_ne_finset_zero
  intro j hj
  have hj' : M < j := by simp only [Finset.mem_range,not_lt] at hj; omega
  simp [Clock.binomialMass,Nat.choose_eq_zero_of_lt hj']

lemma gibbsMean_abs_le_one {n : ℕ} (g : Disorder n) (f : Observables n)
    (hf : ∀ x, |f x| ≤ 1) : |FiniteLaw.mean (mass g 0) f| ≤ 1 := by
  unfold FiniteLaw.mean
  calc
    _ ≤ ∑ x, |mass g 0 x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, mass g 0 x := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul,abs_of_nonneg (mass_nonneg g 0 x)]
      exact mul_le_of_le_one_right (mass_nonneg g 0 x) (hf x)
    _ = _ := sum_mass g 0

lemma residual_test_bound {n : ℕ} (g : Disorder n) {q : ℝ} (hq : 0 < q)
    (hhold : ∀ x, 1-q ≤ transition g x x)
    (f : Observables n) (hf : ∀ x, |f x| ≤ 1) (x : Spin n) (j : ℕ) :
    |(residualAttempt (coupling g) q ^ j) f x-FiniteLaw.mean (mass g 0) f| ≤ 2 := by
  have h := abs_sub ((residualAttempt (coupling g) q ^ j) f x)
    (FiniteLaw.mean (mass g 0) f)
  have hhold' : ∀ x, 1-q ≤ attemptKernel (coupling g) x x := by
    rwa [attemptKernel_eq_transition]
  linarith [residualAttempt_pow_abs_le (coupling g) hq hhold' j f hf x,
    gibbsMean_abs_le_one g f hf]

lemma residual_poisson_test {n : ℕ} (hn : 0 < n)
    (g : Disorder n) {q : ℝ} (hq : q ≠ 0) (m : ℝ)
    (f : Observables n) (x : Spin n) :
    (∑' j, Clock.poissonMass m j*((residualAttempt (coupling g) q ^ j) f x-
      FiniteLaw.mean (mass g 0) f)) =
      semigroup (coupling g) (m/(q*n)) f x-FiniteLaw.mean (mass g 0) f := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : q*n*(m/(q*n)) = m := by field_simp
  have hs := residual_poisson_hasSum hn (coupling g) hq (m/(q*n)) f x
  rw [he] at hs
  have hh := hs.sub ((Clock.hasSum_poissonMass m).mul_right (FiniteLaw.mean (mass g 0) f))
  simpa only [one_mul,← mul_sub] using hh.tsum_eq

lemma residual_binomial_test {n : ℕ} (g : Disorder n) {q : ℝ} (hq : q ≠ 0)
    (M : ℕ) (f : Observables n) (x : Spin n) :
    (∑' j, Clock.binomialMass q M j*((residualAttempt (coupling g) q ^ j) f x-
      FiniteLaw.mean (mass g 0) f)) =
      ((transition g ^ M) *ᵥ f) x-FiniteLaw.mean (mass g 0) f := by
  have hs := residual_binomial_hasSum (coupling g) hq M f x
  have hh := hs.sub ((Clock.hasSum_binomialMass q M).mul_right (FiniteLaw.mean (mass g 0) f))
  simpa only [one_mul,← mul_sub, attempt_pow_eq_transition_pow] using hh.tsum_eq

lemma totalVariation_test_bound {n : ℕ} (p r f : Spin n → ℝ)
    (hf : ∀ y, |f y| ≤ 1) :
    |FiniteLaw.mean p f-FiniteLaw.mean r f| ≤ 2*totalVariation p r := by
  unfold FiniteLaw.mean
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ y, |(p y-r y)*f y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, |p y-r y| := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hf y)
    _ = _ := by dsimp [totalVariation]; ring

lemma continuous_test_bound {n : ℕ} (g : Disorder n) (t : ℝ)
    (f : Observables n) (hf : ∀ y, |f y| ≤ 1) (x : Spin n) :
    |semigroup (coupling g) t f x-FiniteLaw.mean (mass g 0) f| ≤
      2*continuousDistance g t := by
  rw [semigroup_eq_kernel]
  apply (totalVariation_test_bound (continuousKernel (coupling g) t x) (mass g 0) f hf).trans
  exact mul_le_mul_of_nonneg_left (tv_le_continuousDistance g t x) (by norm_num)

lemma field_square_sum_le {n : ℕ} (J : Interaction n) (x : Spin n)
    {K : ℝ} (_hK : 0 ≤ K)
    (hJ : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ K) :
    ∑ i, field J x i^2 ≤ K^2*(n:ℝ) := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J
  let v : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 _).symm (spin x)
  have hv : ‖v‖^2 = (n:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [v, spin_sq]
  have hh : ‖A v‖ ≤ K*‖v‖ := (A.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  rw [mul_pow, hv, EuclideanSpace.real_norm_sq_eq] at hs
  exact hs

lemma one_sub_tanh_half (a : ℝ) :
    (1-Real.tanh a)/2 = 1/(1+Real.exp (2*a)) := by
  have hh := exp_two_mul_one_sub_tanh a
  have he := Real.exp_pos (2*a)
  apply (eq_div_iff (by positivity : (1+Real.exp (2*a)) ≠ 0)).mpr
  nlinarith

lemma one_add_tanh_half (a : ℝ) :
    (1+Real.tanh a)/2 = 1/(1+Real.exp (-2*a)) := by
  simpa only [Real.tanh_neg, sub_neg_eq_add, mul_neg, neg_mul] using one_sub_tanh_half (-a)

lemma siteRefresh_diagonal_lower {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    1/(1+Real.exp (2*|field J x i|)) ≤
      siteRefresh J i (fun z => if z=x then 1 else 0) x := by
  have htrue : replace x i true = x ↔ x i = true := by
    constructor
    · intro h; simpa using (congrFun h i).symm
    · intro h; simpa only [h] using replace_self x i
  have hfalse : replace x i false = x ↔ x i = false := by
    constructor
    · intro h; simpa using (congrFun h i).symm
    · intro h; simpa only [h] using replace_self x i
  simp only [siteRefresh, htrue, hfalse, mean]
  cases x i <;> simp only [ Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, mul_zero, mul_one, zero_add, add_zero]
  · rw [one_sub_tanh_half]
    apply one_div_le_one_div_of_le (by positivity)
    apply add_le_add le_rfl
    apply Real.exp_le_exp.mpr
    linarith [le_abs_self (field J x i)]
  · rw [one_add_tanh_half]
    apply one_div_le_one_div_of_le (by positivity)
    apply add_le_add le_rfl
    apply Real.exp_le_exp.mpr
    linarith [neg_le_abs (field J x i)]

lemma logistic_quadratic_lower {a L : ℝ} (hL : 0 < L) :
    (1-a^2/L^2)/(1+Real.exp (2*L)) ≤ 1/(1+Real.exp (2*|a|)) := by
  by_cases ha : |a| ≤ L
  · calc
      _ ≤ 1/(1+Real.exp (2*L)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : 0 ≤ a^2/L^2 := by positivity
        linarith
      _ ≤ _ := by
        apply one_div_le_one_div_of_le (by positivity)
        apply add_le_add le_rfl
        apply Real.exp_le_exp.mpr
        linarith
  · have ha2 : L^2 ≤ a^2 := by nlinarith [sq_abs a, abs_nonneg a, le_of_not_ge ha]
    have hratio : 1 ≤ a^2/L^2 := (one_le_div (sq_pos_of_pos hL)).mpr ha2
    exact (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)).trans (by positivity)

lemma attempted_holding_lower {n : ℕ} (hn : 0 < n) (J : Interaction n)
    {K : ℝ} (hK : 0 < K)
    (hJ : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ K) (x : Spin n) :
    1/(2*(1+Real.exp (2*(Real.sqrt 2*K)))) ≤ attemptKernel J x x := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hL : 0 < Real.sqrt 2*K := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hK
  have hL2 : (Real.sqrt 2*K)^2 = 2*K^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hsum := field_square_sum_le J x hK.le hJ
  have hs : (∑ i, (1-field J x i^2/(Real.sqrt 2*K)^2)/(1+Real.exp (2*(Real.sqrt 2*K)))) ≤
      ∑ i, siteRefresh J i (fun z => if z=x then 1 else 0) x := by
    apply Finset.sum_le_sum
    intro i _
    exact (logistic_quadratic_lower hL).trans (siteRefresh_diagonal_lower J x i)
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hL2] at hs
  have hf : (∑ i, field J x i^2)/(2*K^2) ≤ (n:ℝ)/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*K^2)).mpr
    nlinarith
  change _ ≤ attemptLM J (fun z => if z=x then 1 else 0) x
  rw [attempt_apply_of_pos hn]
  apply (le_div_iff₀ hnR).mpr
  calc
    _ = ((n:ℝ)/2)/(1+Real.exp (2*(Real.sqrt 2*K))) := by field_simp
    _ ≤ ((n:ℝ)-(∑ i, field J x i^2)/(2*K^2))/(1+Real.exp (2*(Real.sqrt 2*K))) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ _ := hs

end SKRatio.Calculus

end
end

end OAI
