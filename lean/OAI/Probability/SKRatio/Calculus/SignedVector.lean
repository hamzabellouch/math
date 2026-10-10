import Mathlib
import OAI.Probability.SKRatio.FiniteChain.Mean
import OAI.Probability.SKRatio.Calculus.RowControl

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
open Real Set

lemma gradientForm_pairs_bound {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (p : Fin n → ℝ) :
    pairSum (fun i j =>
      J i j^2 * (conditionalVariance J (plusSpin n) j * p i +
        conditionalVariance J (plusSpin n) i * p j)^2 /
        (gradientWeight J (plusSpin n) i + gradientWeight J (plusSpin n) j)) ≤
    (32/27)*R2 J * ∑ i, p i^2 := by
  have hpoint (i j : Fin n) :
      (conditionalVariance J (plusSpin n) j * p i +
        conditionalVariance J (plusSpin n) i * p j)^2 /
        (gradientWeight J (plusSpin n) i + gradientWeight J (plusSpin n) j) ≤
      (32/27)*(p i^2+p j^2) := by
    have habs : |conditionalVariance J (plusSpin n) j * p i +
        conditionalVariance J (plusSpin n) i * p j| ≤
        conditionalVariance J (plusSpin n) j * |p i| +
        conditionalVariance J (plusSpin n) i * |p j| := by
      simpa only [abs_mul, abs_of_pos (conditionalVariance_pos J (plusSpin n) j),
        abs_of_pos (conditionalVariance_pos J (plusSpin n) i)] using abs_add_le
          (conditionalVariance J (plusSpin n) j * p i) (conditionalVariance J (plusSpin n) i * p j)
    have hsquare := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hsquare
    refine (div_le_div_of_nonneg_right hsquare
      (add_pos (gradientWeight_pos J (plusSpin n) i) (gradientWeight_pos J (plusSpin n) j)).le).trans ?_
    simpa only [conditionalVariance, mean_weight_plus, mean] using
      (scalar_pair_denominator_control
        (Real.neg_one_lt_tanh (field J (plusSpin n) i)).le
        (Real.tanh_lt_one (field J (plusSpin n) i))
        (Real.neg_one_lt_tanh (field J (plusSpin n) j)).le
        (Real.tanh_lt_one (field J (plusSpin n) j)) (pi := p i) (pj := p j))
  have hp := pairSum_le (fun i j (_ : i < j) =>
    mul_le_mul_of_nonneg_left (hpoint i j) (sq_nonneg (J i j)))
  simp only [← mul_assoc] at hp
  have hr := mul_le_mul_of_nonneg_left (pair_row_bound J hsymm p 2)
    (by norm_num : (0:ℝ) ≤ 32/27)
  have hid : pairSum (fun i j => J i j^2 * (32/27) * (p i^2+p j^2)) =
      (32/27)*pairSum (fun i j => |J i j|^2 * (p i^2+p j^2)) := by
    rw [← pairSum_mul]
    unfold pairSum
    simp only [sq_abs]
    congr 1
    ext i
    congr 1
    ext j
    ring
  rw [hid] at hp
  simpa only [mul_div_assoc, mul_assoc] using hp.trans hr

theorem rough_gradient_bound {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (p : Fin n → ℝ) :
    gradientForm J p ≤ (euclideanOpNorm J +
      (4/(3*Real.sqrt 3)+32/27)*R2 J) * ∑ i, p i^2 := by
  have h₁ := gradientForm_linear_bound J hdiag p
  have h₂ := gradientForm_quadratic_bound J hsymm p
  have h₃ := gradientForm_pairs_bound J hsymm p
  unfold gradientForm
  linarith only [h₁, h₂, h₃]

def signedVector {n : ℕ} (x : Spin n) (p : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => spin x i * p.ofLp i)

@[simp] lemma norm_signedVector {n : ℕ} (x : Spin n) (p : EuclideanSpace ℝ (Fin n)) :
    ‖signedVector x p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, signedVector, mul_pow, spin_sq, one_mul]

lemma signConjugate_action {n : ℕ} (J : Interaction n) (x : Spin n)
    (p : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (signConjugate x J) p =
      signedVector x (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J (signedVector x p)) := by
  apply WithLp.ofLp_injective
  funext i
  change (∑ j, signConjugate x J i j * p.ofLp j) =
    spin x i * (∑ j, J i j * (spin x j * p.ofLp j))
  simp only [signConjugate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma euclideanOpNorm_signConjugate_le {n : ℕ} (J : Interaction n) (x : Spin n) :
    euclideanOpNorm (signConjugate x J) ≤ euclideanOpNorm J := by
  apply ContinuousLinearMap.opNorm_le_bound _ (euclideanOpNorm_nonneg J)
  intro p
  rw [signConjugate_action, norm_signedVector]
  simpa only [norm_signedVector, euclideanOpNorm] using
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) J).le_opNorm (signedVector x p)

@[simp] lemma signConjugate_twice {n : ℕ} (J : Interaction n) (x : Spin n) :
    signConjugate x (signConjugate x J) = J := by
  funext i j
  simp only [signConjugate]
  calc
    _ = (spin x i)^2 * (spin x j)^2 * J i j := by ring
    _ = J i j := by simp only [spin_sq, one_mul]

@[simp] lemma euclideanOpNorm_signConjugate {n : ℕ} (J : Interaction n) (x : Spin n) :
    euclideanOpNorm (signConjugate x J) = euclideanOpNorm J := by
  exact le_antisymm (euclideanOpNorm_signConjugate_le J x)
    (by simpa only [signConjugate_twice] using euclideanOpNorm_signConjugate_le (signConjugate x J) x)

theorem gradient_global_bound {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hsmall : ∀ i j, |J i j| ≤ 1/10) (f : Observables n) (t : ℝ) (x : Spin n) :
    deriv (fun s => unweightedGradient (semigroup J s f) x) t -
        generator J (unweightedGradient (semigroup J t f)) x ≤
      2*(-1+euclideanOpNorm J+(4/(3*Real.sqrt 3)+32/27)*R2 J+16*R3 J) *
        unweightedGradient (semigroup J t f) x := by
  have hlocal := pointwise_gradient_local_bound J hsymm hdiag hsmall f t x
  have hform := rough_gradient_bound (signConjugate x J) (signConjugate_symm J hsymm x)
    (signConjugate_diag J hdiag x) (fun i => spin x i * halfDiff i (semigroup J t f) x)
  simp only [euclideanOpNorm_signConjugate, R2, rowControl_signConjugate, mul_pow, spin_sq, one_mul] at hform
  change gradientForm _ _ ≤ _ * unweightedGradient (semigroup J t f) x at hform
  linarith only [hlocal, hform]

lemma rough_coefficient_lt_two : 4/(3*Real.sqrt 3)+32/27 < (2:ℝ) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hslo : (18/11:ℝ) < Real.sqrt 3 := by nlinarith only [hs2, hs]
  have h : 4/(3*Real.sqrt 3) < (22/27:ℝ) :=
    (div_lt_iff₀ (by positivity : 0 < 3*Real.sqrt 3)).mpr (by linarith only [hslo])
  linarith only [h]

theorem gradient_dissipation_small_norm {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (hsmall : ∀ i j, |J i j| ≤ 1/10)
    (hop : euclideanOpNorm J ≤ 7/10+1/10000)
    (hr2 : R2 J ≤ 49/400+1/10000) (hr3 : R3 J ≤ 1/10000)
    (f : Observables n) (t : ℝ) (x : Spin n) :
    deriv (fun s => unweightedGradient (semigroup J s f) x) t -
        generator J (unweightedGradient (semigroup J t f)) x ≤
      -(1/10:ℝ) * unweightedGradient (semigroup J t f) x := by
  have h := gradient_global_bound J hsymm hdiag hsmall f t x
  have hc : 2*(-1+euclideanOpNorm J+(4/(3*Real.sqrt 3)+32/27)*R2 J+16*R3 J) ≤ -(1/10:ℝ) := by
    have hm := mul_le_mul_of_nonneg_right rough_coefficient_lt_two.le (rowControl_nonneg J 2)
    linarith only [hm, hop, hr2, hr3]
  exact h.trans (mul_le_mul_of_nonneg_right hc
    (Finset.sum_nonneg (fun i _ => sq_nonneg (halfDiff i (semigroup J t f) x))))

noncomputable def attemptLM {n : ℕ} (J : Interaction n) :
    Observables n →L[ℝ] Observables n :=
  1 + (n : ℝ)⁻¹ • generatorCLM J

noncomputable def continuousKernel {n : ℕ} (J : Interaction n) (t : ℝ) :
    Matrix (Spin n) (Spin n) ℝ := fun x y =>
      semigroup J t (fun z => if z = y then 1 else 0) x

noncomputable def siteRefresh {n : ℕ} (J : Interaction n) (i : Fin n)
    (f : Observables n) (x : Spin n) : ℝ :=
  ((1 + mean J x i) / 2) * f (replace x i true) +
  ((1 - mean J x i) / 2) * f (replace x i false)

theorem generator_siteRefresh {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) : generator J f x = ∑ i, (siteRefresh J i f x - f x) := by
  apply Finset.sum_congr rfl
  intro i _
  have hx : replace x i (x i) = x := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [halfDiff, spin, hi, Bool.false_eq_true, ↓reduceIte, siteRefresh]
    rw [hx]
    ring
  · simp only [halfDiff, spin, hi, ↓reduceIte, siteRefresh]
    rw [hx]
    ring

theorem attempt_apply_of_pos {n : ℕ} (hn : 0 < n) (J : Interaction n)
    (f : Observables n) (x : Spin n) :
    attemptLM J f x = (∑ i, siteRefresh J i f x) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  change f x + (n : ℝ)⁻¹ * generator J f x = _
  rw [generator_siteRefresh, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

@[simp] theorem generator_const {n : ℕ} (J : Interaction n) (a : ℝ) (x : Spin n) :
    generator J (fun _ => a) x = 0 := by
  simp [generator]

@[simp] theorem siteRefresh_const {n : ℕ} (J : Interaction n) (i : Fin n)
    (a : ℝ) (x : Spin n) : siteRefresh J i (fun _ => a) x = a := by
  unfold siteRefresh
  ring

@[simp] theorem attempt_const {n : ℕ} (J : Interaction n) (a : ℝ) :
    attemptLM J (fun _ => a) = fun _ => a := by
  funext x
  change a + (n : ℝ)⁻¹ * generator J (fun _ => a) x = a
  simp

@[simp] theorem attempt_pow_const {n : ℕ} (J : Interaction n) (k : ℕ) (a : ℝ) :
    (attemptLM J ^ k) (fun _ => a) = fun _ => a := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ', mul_apply_eq_comp, ih, attempt_const]

theorem siteRefresh_nonneg {n : ℕ} (J : Interaction n) (i : Fin n)
    (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ siteRefresh J i f x := by
  have hm1 : -1 ≤ mean J x i := le_of_lt (Real.neg_one_lt_tanh _)
  have hm2 : mean J x i ≤ 1 := le_of_lt (Real.tanh_lt_one _)
  exact add_nonneg (mul_nonneg (by linarith) (hf _))
    (mul_nonneg (by linarith) (hf _))

theorem attempt_nonneg {n : ℕ} (J : Interaction n) (f : Observables n)
    (hf : ∀ x, 0 ≤ f x) (x : Spin n) : 0 ≤ attemptLM J f x := by
  by_cases hn : n = 0
  · subst n
    simpa [attemptLM] using hf x
  · rw [attempt_apply_of_pos (Nat.pos_of_ne_zero hn)]
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => siteRefresh_nonneg J _ f hf x))
      (Nat.cast_nonneg n)

theorem attempt_pow_nonneg {n : ℕ} (J : Interaction n) (k : ℕ) (f : Observables n)
    (hf : ∀ x, 0 ≤ f x) (x : Spin n) : 0 ≤ (attemptLM J ^ k) f x := by
  induction k generalizing x with
  | zero => simpa using hf x
  | succ k ih =>
    simp only [pow_succ', mul_apply_eq_comp]
    exact attempt_nonneg J _ ih x

theorem exp_apply_hasSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) (f : E) :
    HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ • ((A ^ k) f))
      (NormedSpace.exp A f) := by
  simpa only [NormedSpace.expSeries_apply_eq, ContinuousLinearMap.apply_apply,
    smul_apply] using
    (ContinuousLinearMap.apply ℝ E f).hasSum
      (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) A)

theorem exp_apply_of_apply_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (f : E)
    (h : A f = 0) : NormedSpace.exp A f = f := by
  have hp (k : ℕ) : (A ^ (k + 1)) f = 0 := by
    induction k with
    | zero => simpa using h
    | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, map_zero]
  have hs : HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ • ((A ^ k) f)) f := by
    convert hasSum_ite_eq 0 f using 1
    funext k
    cases k with
    | zero => simp
    | succ k => simp [hp]
  exact (exp_apply_hasSum A f).unique hs

@[simp] theorem semigroup_const {n : ℕ} (J : Interaction n) (t a : ℝ) :
    semigroup J t (fun _ => a) = fun _ => a := by
  apply exp_apply_of_apply_eq_zero
  funext x
  change t * generator J (fun _ => a) x = 0
  simp

theorem exp_smul_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a : ℝ) :
    NormedSpace.exp (a • (1 : E →L[ℝ] E)) = Real.exp a • (1 : E →L[ℝ] E) := by
  simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
    (NormedSpace.algebraMap_exp_comm (𝔸 := E →L[ℝ] E) a).symm

theorem semigroup_uniformization {n : ℕ} (hn : 0 < n) (J : Interaction n) (t : ℝ) :
    semigroup J t = Real.exp (-(n : ℝ) * t) •
      NormedSpace.exp (((n : ℝ) * t) • attemptLM J) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have heq : t • generatorCLM J =
      (-(n : ℝ) * t) • (1 : Observables n →L[ℝ] Observables n) +
        ((n : ℝ) * t) • attemptLM J := by
    unfold attemptLM
    simp only [smul_add, smul_smul]
    have hc : ((n : ℝ) * t) * (n : ℝ)⁻¹ = t := by field_simp
    rw [hc]
    module
  let : NormedAlgebra ℚ (Observables n →L[ℝ] Observables n) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  unfold semigroup
  rw [heq, NormedSpace.exp_add_of_commute
    (((Commute.one_left (attemptLM J)).smul_left _).smul_right _),
    exp_smul_identity, smul_mul_assoc, one_mul]

theorem semigroup_nonneg {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ semigroup J t f x := by
  by_cases hn : n = 0
  · subst n
    have hL : generatorCLM J = 0 := by
      ext f x
      simp [generatorCLM, generatorLM, generator]
    simp only [semigroup, hL, smul_zero, NormedSpace.exp_zero,
      one_apply_eq_self]
    exact hf x
  · rw [semigroup_uniformization (Nat.pos_of_ne_zero hn)]
    simp only [smul_apply, Pi.smul_apply, smul_eq_mul]
    apply mul_nonneg (le_of_lt (Real.exp_pos _))
    have hs := Pi.hasSum.mp (exp_apply_hasSum (((n : ℝ) * t) • attemptLM J) f) x
    apply HasSum.nonneg _ hs
    intro k
    simp only [smul_pow, smul_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (mul_nonneg (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) ht) _)
        (attempt_pow_nonneg J k f hf x))

theorem continuousKernel_nonneg {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    (x y : Spin n) : 0 ≤ continuousKernel J t x y := by
  exact semigroup_nonneg J t ht _ (fun _ => by split_ifs <;> norm_num) x

theorem continuousKernel_sum {n : ℕ} (J : Interaction n) (t : ℝ) (x : Spin n) :
    ∑ y, continuousKernel J t x y = 1 := by
  have eq_one : (∑ y : Spin n, fun z => if z = y then (1 : ℝ) else 0) =
      fun _ : Spin n => (1 : ℝ) := by
    funext z
    simp
  unfold continuousKernel
  rw [← Finset.sum_apply, ← map_sum, eq_one, semigroup_const]

theorem attempt_eq_transition {n : ℕ} (g : Disorder n) (f : Observables n) :
    attemptLM (coupling g) f = transition g *ᵥ f := by
  funext x
  by_cases hn : n = 0
  · subst n
    simp [attemptLM, transition]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  change f x + (n : ℝ)⁻¹ * generator (coupling g) f x = _
  rw [generator_eq_transition]
  simp only [← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  change f x + ((transition g *ᵥ f) x - f x) = (transition g *ᵥ f) x
  ring

theorem attempt_pow_eq_transition_pow {n : ℕ} (g : Disorder n) (k : ℕ)
    (f : Observables n) : (attemptLM (coupling g)^k) f = transition g^k *ᵥ f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, ih, attempt_eq_transition,
      Matrix.mulVec_mulVec]

theorem semigroup_add {n : ℕ} (J : Interaction n) (s t : ℝ) :
    semigroup J (s+t) = semigroup J s * semigroup J t := by
  let : NormedAlgebra ℚ (Observables n →L[ℝ] Observables n) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  unfold semigroup
  rw [add_smul, NormedSpace.exp_add_of_commute
    (((Commute.refl (generatorCLM J)).smul_left _).smul_right _)]

theorem semigroup_mono {n : ℕ} (J : Interaction n) {t : ℝ} (ht : 0 ≤ t)
    (f h : Observables n) (hfh : ∀ x, f x ≤ h x) (x : Spin n) :
    semigroup J t f x ≤ semigroup J t h x := by
  have hn := semigroup_nonneg J t ht (h-f) (fun x => sub_nonneg.mpr (hfh x)) x
  simpa only [map_sub, Pi.sub_apply, sub_nonneg] using hn

theorem semigroup_abs_le {n : ℕ} (J : Interaction n) {t : ℝ} (ht : 0 ≤ t)
    (f : Observables n) {B : ℝ} (hf : ∀ x, |f x| ≤ B) (x : Spin n) :
    |semigroup J t f x| ≤ B := by
  have hu := semigroup_mono J ht f (fun _ => B) (fun x => (abs_le.mp (hf x)).2) x
  have hl := semigroup_mono J ht (fun _ => -B) f (fun x => (abs_le.mp (hf x)).1) x
  simp only [semigroup_const] at hu hl
  exact abs_le.mpr ⟨hl,hu⟩

theorem observable_basis {n : ℕ} (f : Observables n) :
    f = ∑ y : Spin n, f y • (fun z => if z = y then (1:ℝ) else 0) := by
  funext x
  simp

theorem semigroup_eq_kernel {n : ℕ} (J : Interaction n) (t : ℝ)
    (f : Observables n) (x : Spin n) :
    semigroup J t f x = FiniteLaw.mean (continuousKernel J t x) f := by
  conv_lhs => rw [observable_basis f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    FiniteLaw.mean, continuousKernel]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem kernel_eq_mulVec {n : ℕ} (J : Interaction n) (t : ℝ)
    (f : Observables n) : semigroup J t f = continuousKernel J t *ᵥ f := by
  funext x
  exact semigroup_eq_kernel J t f x

theorem continuousKernel_add {n : ℕ} (J : Interaction n) (s t : ℝ) :
    continuousKernel J (s+t) =
      (continuousKernel J s : Matrix (Spin n) (Spin n) ℝ) * continuousKernel J t := by
  funext x y
  unfold continuousKernel
  rw [semigroup_add, mul_apply_eq_comp, semigroup_eq_kernel]
  rfl

theorem continuousKernel_poisson_hasSum {n : ℕ} (hn : 0 < n) (g : Disorder n)
    (t : ℝ) (x y : Spin n) :
    HasSum (fun k : ℕ => Real.exp (-(n:ℝ)*t) * ((n:ℝ)*t)^k /
      (k.factorial:ℝ) * (transition g^k) x y)
      (continuousKernel (coupling g) t x y) := by
  have hs := (Pi.hasSum.mp (exp_apply_hasSum (((n:ℝ)*t) • attemptLM (coupling g))
    (fun z => if z = y then (1:ℝ) else 0)) x).mul_left (Real.exp (-(n:ℝ)*t))
  simp only [smul_pow, smul_apply, Pi.smul_apply, smul_eq_mul,
    attempt_pow_eq_transition_pow, Matrix.mulVec, dotProduct,
    mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq'] at hs
  rw [continuousKernel, semigroup_uniformization hn]
  have heq : (fun k : ℕ => Real.exp (-(n:ℝ)*t) * ((n:ℝ)*t)^k /
      (k.factorial:ℝ) * (transition g^k) x y) =
      (fun k : ℕ => Real.exp (-(n:ℝ)*t) * ((k.factorial:ℝ)⁻¹ *
        (((n:ℝ)*t)^k * (transition g^k) x y))) := by
    funext k
    ring
  rw [heq]
  exact hs

end SKRatio.Calculus
end
end

end OAI
