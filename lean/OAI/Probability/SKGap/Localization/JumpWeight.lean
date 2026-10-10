import Mathlib
import OAI.Probability.SKGap.Localization.JumpEnergy

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
namespace SKGapCutoff

noncomputable def jumpWeight {n : ℕ} (J : Interaction n) (x : Spin n) (j : Fin n) : ℝ :=
  1 - mean J x j * spin x j

lemma jumpWeight_pos {n : ℕ} (J : Interaction n) (x : Spin n) (j : Fin n) :
    0 < jumpWeight J x j := by
  have ht := Real.abs_tanh_lt_one (field J x j)
  have hm : |mean J x j| < 1 := ht
  unfold jumpWeight spin
  cases x j <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_neg, mul_one] <;>
    linarith [(abs_lt.mp hm).1, (abs_lt.mp hm).2]

noncomputable def influence {n : ℕ} (J : Interaction n) (x : Spin n) : Interaction n :=
  fun i j => halfDiff i (fun y => mean J y j) x

noncomputable def vectorSquare {n : ℕ} (p : VectorFields n) (x : Spin n) : ℝ :=
  ∑ i, p x i ^ 2

noncomputable def vectorDissipation {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (x : Spin n) : ℝ :=
  ∑ i, ∑ j, jumpWeight J x j * (halfDiff j (fun y => p y i) x) ^ 2

lemma vectorSquare_nonneg {n : ℕ} (p : VectorFields n) (x : Spin n) :
    0 ≤ vectorSquare p x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma vectorDissipation_nonneg {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (x : Spin n) : 0 ≤ vectorDissipation J p x := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (jumpWeight_pos J x j).le (sq_nonneg _)))

lemma generator_vectorSquare {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (x : Spin n) :
    generator J (vectorSquare p) x = ∑ i, generator J (fun y => p y i ^ 2) x := by
  have hv : vectorSquare p = ∑ i, fun y => p y i ^ 2 := by
    funext y
    simp only [vectorSquare, Finset.sum_apply]
  rw [hv]
  change generatorLM J (∑ i, fun y => p y i ^ 2) x = _
  rw [map_sum, Finset.sum_apply]
  rfl

lemma gradient_square_identity {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (x : Spin n) :
    (∑ i, 2 * p x i * gradientGenerator J p x i) - generator J (vectorSquare p) x =
      -2 * vectorSquare p x +
        2 * ∑ i, p x i * (∑ j, influence J x i j * p x j) -
        4 * ∑ i, (p x i * spin x i) * (∑ j, influence J x i j * halfDiff j (fun y => p y i) x) -
        2 * vectorDissipation J p x := by
  rw [generator_vectorSquare, ← Finset.sum_sub_distrib]
  have hloc (i : Fin n) :
      2 * p x i * gradientGenerator J p x i - generator J (fun y => p y i ^ 2) x =
      -2 * p x i ^ 2 + 2 * (p x i * (∑ j, influence J x i j * p x j)) -
        4 * ((p x i * spin x i) * (∑ j, influence J x i j * halfDiff j (fun y => p y i) x)) -
        2 * (∑ j, jumpWeight J x j * (halfDiff j (fun y => p y i) x) ^ 2) := by
    rw [generator_square]
    dsimp only [gradientGenerator, influence, jumpEnergy, jumpWeight]
    ring
  simp_rw [hloc]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    vectorSquare, vectorDissipation]

lemma weighted_cross_young (q a d w : ℝ) (hw : 0 < w) :
    -4 * q * a * d ≤ 4 * (a ^ 2 / w) * q ^ 2 + w * d ^ 2 := by
  apply (mul_le_mul_iff_left₀ hw).mp
  have he : (4 * (a ^ 2 / w) * q ^ 2 + w * d ^ 2) * w =
      4 * (q*a)^2 + (w*d)^2 := by field_simp
  rw [he]
  nlinarith [sq_nonneg (2*q*a+w*d)]

lemma gradient_first_order_bound {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (x : Spin n) (R : ℝ)
    (hR : ∀ i, ∑ j, influence J x i j ^ 2 / jumpWeight J x j ≤ R) :
    -4 * (∑ i, (p x i * spin x i) *
      (∑ j, influence J x i j * halfDiff j (fun y => p y i) x)) ≤
      4 * R * vectorSquare p x + vectorDissipation J p x := by
  have hrow (i : Fin n) :
      -4 * ((p x i * spin x i) *
        (∑ j, influence J x i j * halfDiff j (fun y => p y i) x)) ≤
      4 * R * p x i ^ 2 +
        ∑ j, jumpWeight J x j * (halfDiff j (fun y => p y i) x) ^ 2 := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => weighted_cross_young
      (p x i * spin x i) (influence J x i j)
      (halfDiff j (fun y => p y i) x) (jumpWeight J x j) (jumpWeight_pos J x j))
    simp only [mul_pow, spin_sq, mul_one, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum] at hs
    calc
      _ ≤ 4 * (∑ j, influence J x i j ^ 2 / jumpWeight J x j) * p x i ^ 2 +
        ∑ j, jumpWeight J x j * (halfDiff j (fun y => p y i) x) ^ 2 := by
          have he : -4 * ((p x i * spin x i) *
              (∑ j, influence J x i j * halfDiff j (fun y => p y i) x)) =
              ∑ j, -4 * (p x i * spin x i) * influence J x i j *
                halfDiff j (fun y => p y i) x := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          rw [he]
          exact hs
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_right (hR i) (sq_nonneg (p x i))
        nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    vectorSquare, vectorDissipation] using hs

lemma gradient_square_le {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (x : Spin n) (A R : ℝ)
    (hA : ∑ i, p x i * (∑ j, influence J x i j * p x j) ≤ A * vectorSquare p x)
    (hR : ∀ i, ∑ j, influence J x i j ^ 2 / jumpWeight J x j ≤ R) :
    (∑ i, 2 * p x i * gradientGenerator J p x i) - generator J (vectorSquare p) x ≤
      (2*A+4*R-2) * vectorSquare p x - vectorDissipation J p x := by
  rw [gradient_square_identity]
  have h := gradient_first_order_bound J p x R hR
  linarith

lemma gradientSemigroup_apply_hasDerivAt {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gradientSemigroup J s p)
      (gradientGenerator J (gradientSemigroup J t p)) t := by
  simpa only [gradientSemigroup, mul_apply_eq_comp, map_zero, add_zero, gradientGeneratorCLM,
    gradientGeneratorLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk] using
    (hasDerivAt_exp_smul_const' (gradientGeneratorCLM J) t).clm_apply
      (hasDerivAt_const t p)

lemma backward_gradient_hasDerivAt {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (t s : ℝ) :
    HasDerivAt (fun r : ℝ => gradientSemigroup J (t-r) p)
      (-gradientGenerator J (gradientSemigroup J (t-s) p)) s := by
  have h := (gradientSemigroup_apply_hasDerivAt J p (t-s)).scomp s
    ((hasDerivAt_id s).const_sub t)
  simpa only [id_eq, neg_smul, one_smul, Function.comp_def] using h

lemma backward_vectorSquare_hasDerivAt {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (t s : ℝ) :
    HasDerivAt (fun r : ℝ => vectorSquare (gradientSemigroup J (t-r) p))
      (fun x => -(∑ i, 2 * gradientSemigroup J (t-s) p x i *
        gradientGenerator J (gradientSemigroup J (t-s) p) x i)) s := by
  apply hasDerivAt_pi.mpr
  intro x
  have hi (i : Fin n) := (hasDerivAt_pi.mp
    (hasDerivAt_pi.mp (backward_gradient_hasDerivAt J p t s) x) i).pow 2
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  simpa only [vectorSquare, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.neg_apply, mul_neg,
    Finset.sum_neg_distrib] using hs

noncomputable def roughDefect {n : ℕ} (J : Interaction n) (C : ℝ)
    (p : VectorFields n) (x : Spin n) : ℝ :=
  C * vectorSquare p x + generator J (vectorSquare p) x -
    ∑ i, 2 * p x i * gradientGenerator J p x i

lemma roughDefect_nonneg {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (x : Spin n) (A R : ℝ)
    (hA : ∑ i, p x i * (∑ j, influence J x i j * p x j) ≤ A * vectorSquare p x)
    (hR : ∀ i, ∑ j, influence J x i j ^ 2 / jumpWeight J x j ≤ R) :
    0 ≤ roughDefect J (2*A+4*R-2) p x := by
  have hs := gradient_square_le J p x A R hA hR
  have hd := vectorDissipation_nonneg J p x
  unfold roughDefect
  linarith

lemma interpolated_vectorSquare_hasDerivAt {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (t C s : ℝ) (x : Spin n) :
    HasDerivAt (fun r : ℝ => Real.exp (C*r) * semigroup J r
      (vectorSquare (gradientSemigroup J (t-r) p)) x)
      (Real.exp (C*s) * semigroup J s
        (roughDefect J C (gradientSemigroup J (t-s) p)) x) s := by
  have hv := (semigroup_hasDerivAt J s).clm_apply
    (backward_vectorSquare_hasDerivAt J p t s)
  have he := (hasDerivAt_id s).const_mul C |>.exp
  have hh := he.mul (hasDerivAt_pi.mp hv x)
  apply hh.congr_deriv
  simp only [mul_one, mul_apply_eq_comp]
  let q := gradientSemigroup J (t-s) p
  change Real.exp (C*s) * C * semigroup J s (vectorSquare q) x +
    Real.exp (C*s) * (semigroup J s (generator J (vectorSquare q)) +
      semigroup J s (fun y => -(∑ i, 2*q y i*gradientGenerator J q y i))) x = _
  have hd : roughDefect J C q = C • vectorSquare q + generator J (vectorSquare q) +
      (fun y => -(∑ i, 2*q y i*gradientGenerator J q y i)) := by
    funext y
    simp only [roughDefect, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
  rw [hd, map_add, map_add, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma rough_vector_propagation {n : ℕ} (J : Interaction n) (A R : ℝ)
    (hA : ∀ x (q : Fin n → ℝ),
      ∑ i, q i * (∑ j, influence J x i j * q j) ≤ A * ∑ i, q i ^ 2)
    (hR : ∀ x i, ∑ j, influence J x i j ^ 2 / jumpWeight J x j ≤ R)
    (p : VectorFields n) (t : ℝ) (ht : 0 ≤ t) (x : Spin n) :
    vectorSquare (gradientSemigroup J t p) x ≤
      Real.exp ((2*A+4*R-2)*t) * semigroup J t (vectorSquare p) x := by
  let C := 2*A+4*R-2
  let F (s : ℝ) := Real.exp (C*s) * semigroup J s
    (vectorSquare (gradientSemigroup J (t-s) p)) x
  let F' (s : ℝ) := Real.exp (C*s) * semigroup J s
    (roughDefect J C (gradientSemigroup J (t-s) p)) x
  have hd (s : ℝ) : HasDerivAt F (F' s) s :=
    interpolated_vectorSquare_hasDerivAt J p t C s x
  have hc : Continuous F := (show Differentiable ℝ F from
    fun s => (hd s).differentiableAt).continuous
  have hpos (s : ℝ) (hs : 0 ≤ s) : 0 ≤ F' s := by
    apply mul_nonneg (Real.exp_pos _).le
    apply semigroup_nonneg J s hs
    intro y
    exact roughDefect_nonneg J _ y A R (hA y _) (hR y)
  have hm : MonotoneOn F (Set.Icc 0 t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) hc.continuousOn
      (fun s _ => (hd s).hasDerivWithinAt)
      (fun s hs => hpos s ((interior_subset hs).1))
  have hv := hm (show (0 : ℝ) ∈ Set.Icc 0 t from ⟨le_rfl, ht⟩)
    (show t ∈ Set.Icc (0 : ℝ) t from ⟨ht, le_rfl⟩) ht
  simpa only [F, mul_zero, Real.exp_zero, semigroup_zero, sub_zero, sub_self,
    gradientSemigroup, zero_smul, NormedSpace.exp_zero, one_apply_eq_self, one_mul, C] using hv

lemma gradientSemigroup_continuous {n : ℕ} (J : Interaction n) (p : VectorFields n) :
    Continuous (fun t : ℝ => gradientSemigroup J t p) :=
  (show Differentiable ℝ (fun t : ℝ => gradientSemigroup J t p) from
    fun t => (gradientSemigroup_apply_hasDerivAt J p t).differentiableAt).continuous

lemma vectorDissipation_continuous {n : ℕ} (J : Interaction n) :
    Continuous (vectorDissipation J) := by
  unfold vectorDissipation halfDiff
  fun_prop

lemma roughDefect_continuous {n : ℕ} (J : Interaction n) (C : ℝ) :
    Continuous (roughDefect J C) := by
  unfold roughDefect vectorSquare gradientGenerator generator halfDiff
  fun_prop

lemma interpolated_vector_continuous {n : ℕ} (J : Interaction n)
    (p : VectorFields n) (G : VectorFields n → Observables n)
    (hG : Continuous G) (C t : ℝ) (x : Spin n) :
    Continuous (fun s : ℝ => Real.exp (C*s) *
      semigroup J s (G (gradientSemigroup J (t-s) p)) x) := by
  have hq : Continuous (fun s : ℝ => gradientSemigroup J (t-s) p) :=
    (gradientSemigroup_continuous J p).comp (continuous_const.sub continuous_id)
  exact (continuous_const.mul continuous_id).rexp.mul
    ((continuous_apply x).comp ((semigroup_continuous J).clm_apply (hG.comp hq)))

lemma rough_vector_dissipation {n : ℕ} (J : Interaction n) (A R : ℝ)
    (hA : ∀ x (q : Fin n → ℝ),
      ∑ i, q i * (∑ j, influence J x i j * q j) ≤ A * ∑ i, q i ^ 2)
    (hR : ∀ x i, ∑ j, influence J x i j ^ 2 / jumpWeight J x j ≤ R)
    (p : VectorFields n) (t : ℝ) (ht : 0 ≤ t) (x : Spin n) :
    (∫ s in (0 : ℝ)..t, Real.exp ((2*A+4*R-2)*s) *
      semigroup J s (vectorDissipation J (gradientSemigroup J (t-s) p)) x) ≤
      Real.exp ((2*A+4*R-2)*t) * semigroup J t (vectorSquare p) x -
        vectorSquare (gradientSemigroup J t p) x := by
  let C := 2*A+4*R-2
  have h1 := interpolated_vector_continuous J p (vectorDissipation J)
    (vectorDissipation_continuous J) C t x
  have h2 := interpolated_vector_continuous J p (roughDefect J C)
    (roughDefect_continuous J C) C t x
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => interpolated_vectorSquare_hasDerivAt J p t C s x)
    (h2.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
  have hi : (∫ s in (0 : ℝ)..t, Real.exp (C*s) *
      semigroup J s (vectorDissipation J (gradientSemigroup J (t-s) p)) x) ≤
      ∫ s in (0 : ℝ)..t, Real.exp (C*s) *
        semigroup J s (roughDefect J C (gradientSemigroup J (t-s) p)) x := by
    apply intervalIntegral.integral_mono_on ht (h1.intervalIntegrable 0 t) (h2.intervalIntegrable 0 t)
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply semigroup_mono J s hs.1
    intro y
    have hg := gradient_square_le J (gradientSemigroup J (t-s) p) y A R (hA y _) (hR y)
    dsimp only [roughDefect, C]
    linarith
  rw [he] at hi
  simpa only [C, sub_self, sub_zero, mul_zero, Real.exp_zero, semigroup_zero,
    gradientSemigroup, zero_smul, NormedSpace.exp_zero, one_apply_eq_self, one_mul] using hi

end SKGapCutoff

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

end

end OAI
