import Mathlib
import OAI.Probability.SKGap.Terminal.GibbsExpectation

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
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
namespace SKGapCutoff.Static

noncomputable def conditionalMean {n : ℕ} (P : Spin n → ℝ) (x : Spin n)
    (i : Fin n) : ℝ :=
  spin x i * ((P x - P (flip x i)) / (P x + P (flip x i)))

noncomputable def lawDirichlet {n : ℕ} (P : Spin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  (∑ i, ∑ x, (P x * P (flip x i) / (P x + P (flip x i))) *
    (f x - f (flip x i)) ^ 2) / 2

noncomputable def lawDensityEnergy {n : ℕ} (P Q : Spin n → ℝ) : ℝ :=
  lawDirichlet P (fun x => Real.sqrt (Q x / P x))

lemma binary_root_energy (p r q s : ℝ) (hp : 0 < p) (hr : 0 < r)
    (hq : 0 ≤ q) (hs : 0 ≤ s) :
    p * r / (p+r) * (Real.sqrt (q/p) - Real.sqrt (s/r))^2 =
      (Real.sqrt r * Real.sqrt q - Real.sqrt p * Real.sqrt s)^2 / (p+r) := by
  rw [Real.sqrt_div hq, Real.sqrt_div hs]
  have hp0 := Real.sqrt_pos.2 hp
  have hr0 := Real.sqrt_pos.2 hr
  have hp2 := Real.sq_sqrt hp.le
  have hr2 := Real.sq_sqrt hr.le
  field_simp
  rw [hp2, hr2]

lemma binary_conditional_mean_energy (p r q s : ℝ) (hp : 0 < p) (hr : 0 < r)
    (hq : 0 ≤ q) (hs : 0 ≤ s) :
    (q+s) * ((q-s)/(q+s) - (p-r)/(p+r))^2 ≤
      4 * (Real.sqrt r * Real.sqrt q - Real.sqrt p * Real.sqrt s)^2 / (p+r) := by
  by_cases hqs : q+s=0
  · have hq0 : q=0 := by linarith
    have hs0 : s=0 := by linarith
    simp [hq0, hs0]
  have hqt : 0 < q+s := lt_of_le_of_ne (add_nonneg hq hs) (Ne.symm hqs)
  have hpt : 0 < p+r := add_pos hp hr
  have hp2 := Real.sq_sqrt hp.le
  have hr2 := Real.sq_sqrt hr.le
  have hq2 := Real.sq_sqrt hq
  have hs2 := Real.sq_sqrt hs
  let a := Real.sqrt r * Real.sqrt q - Real.sqrt p * Real.sqrt s
  let b := Real.sqrt r * Real.sqrt q + Real.sqrt p * Real.sqrt s
  have hab : a*b = r*q-p*s := by
    dsimp [a,b]
    nlinarith only [hp2,hr2,hq2,hs2]
  have hb : b^2 ≤ (p+r)*(q+s) := by
    have he : (p+r)*(q+s)-b^2 =
      (Real.sqrt p * Real.sqrt q - Real.sqrt r * Real.sqrt s)^2 := by
      dsimp [b]
      nlinarith only [hp2,hr2,hq2,hs2]
    nlinarith only [he, sq_nonneg (Real.sqrt p * Real.sqrt q - Real.sqrt r * Real.sqrt s)]
  have hd : (q-s)/(q+s) - (p-r)/(p+r) = 2*(a*b)/((q+s)*(p+r)) := by
    rw [hab]
    field_simp
    ring
  rw [hd]
  change (q+s)*(2*(a*b)/((q+s)*(p+r)))^2 ≤ 4*a^2/(p+r)
  apply (le_div_iff₀ hpt).2
  have hd2 : (q+s)*(2*(a*b)/((q+s)*(p+r)))^2*(p+r) =
      4*a^2*b^2/((q+s)*(p+r)) := by field_simp; ring
  rw [hd2]
  apply (div_le_iff₀ (mul_pos hqt hpt)).2
  nlinarith only [mul_le_mul_of_nonneg_left hb (show 0 ≤ 4*a^2 by positivity)]

@[simp] lemma conditionalMean_flip {n : ℕ} (P : Spin n → ℝ)
    (x : Spin n) (i : Fin n) : conditionalMean P (flip x i) i = conditionalMean P x i := by
  simp only [conditionalMean, flip_flip, spin_flip_self]
  rw [add_comm (P (flip x i)), ← neg_sub (P x) (P (flip x i)), neg_div, neg_mul_neg]

lemma lawDensityEnergy_eq {n : ℕ} (P Q : Spin n → ℝ)
    (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 ≤ Q x) :
    lawDensityEnergy P Q = (∑ i, ∑ x,
      (Real.sqrt (P (flip x i)) * Real.sqrt (Q x) -
        Real.sqrt (P x) * Real.sqrt (Q (flip x i)))^2 / (P x + P (flip x i))) / 2 := by
  unfold lawDensityEnergy lawDirichlet
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  exact binary_root_energy _ _ _ _ (hP x) (hP _) (hQ x) (hQ _)

theorem conditional_means_energy {n : ℕ} (P Q : Spin n → ℝ)
    (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 ≤ Q x) :
    (∑ x, Q x * ∑ i, (conditionalMean Q x i - conditionalMean P x i)^2) ≤
      4 * lawDensityEnergy P Q := by
  rw [lawDensityEnergy_eq P Q hP hQ]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsym (i : Fin n) :
      (∑ x, Q (flip x i) * (conditionalMean Q x i - conditionalMean P x i)^2) =
      ∑ x, Q x * (conditionalMean Q x i - conditionalMean P x i)^2 := by
    simpa only [conditionalMean_flip] using sum_flip i
      (fun x => Q x * (conditionalMean Q x i - conditionalMean P x i)^2)
  have hlocal (i : Fin n) (x : Spin n) :
      (Q x + Q (flip x i)) * (conditionalMean Q x i - conditionalMean P x i)^2 ≤
      4 * (Real.sqrt (P (flip x i)) * Real.sqrt (Q x) -
        Real.sqrt (P x) * Real.sqrt (Q (flip x i)))^2 / (P x + P (flip x i)) := by
    have he : (conditionalMean Q x i - conditionalMean P x i)^2 =
        ((Q x-Q (flip x i))/(Q x+Q (flip x i)) -
          (P x-P (flip x i))/(P x+P (flip x i)))^2 := by
      simp only [conditionalMean, ← mul_sub, mul_pow, spin_sq, one_mul]
    rw [he]
    exact binary_conditional_mean_energy _ _ _ _ (hP x) (hP _) (hQ x) (hQ _)
  have hh (i : Fin n) := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hlocal i x)
  simp only [add_mul, Finset.sum_add_distrib, hsym] at hh
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hh i)
  simp only [Finset.sum_add_distrib, mul_div_assoc, ← Finset.mul_sum] at hsum ⊢
  linarith only [hsum]

lemma conditionalMean_mul_mass {n : ℕ} (Q : Spin n → ℝ)
    (hQ : ∀ x, 0 ≤ Q x) (x : Spin n) (i : Fin n) :
    (Q x + Q (flip x i)) * conditionalMean Q x i =
      spin x i * (Q x-Q (flip x i)) := by
  unfold conditionalMean
  by_cases h : Q x + Q (flip x i) = 0
  · have ha : Q x=0 := by have := hQ (flip x i); have := hQ x; linarith
    have hb : Q (flip x i)=0 := by have := hQ x; have := hQ (flip x i); linarith
    simp [ha,hb]
  · field_simp

lemma conditionalMean_abs_le {n : ℕ} (Q : Spin n → ℝ)
    (hQ : ∀ x, 0 ≤ Q x) (x : Spin n) (i : Fin n) :
    |conditionalMean Q x i| ≤ 1 := by
  have hs : |spin x i| = 1 := by cases hx : x i <;> simp [spin,hx]
  simp only [conditionalMean, abs_mul, hs, one_mul, abs_div]
  rw [abs_of_nonneg (add_nonneg (hQ x) (hQ _))]
  apply div_le_one_of_le₀ _ (add_nonneg (hQ x) (hQ _))
  exact abs_sub_le_iff.2 ⟨by linarith [hQ (flip x i)], by linarith [hQ x]⟩

lemma law_coordinate_mean {n : ℕ} (Q : Spin n → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (i : Fin n) (F : Spin n → ℝ) (hF : ∀ x, F (flip x i)=F x) :
    (∑ x, Q x * spin x i * F x) = ∑ x, Q x * conditionalMean Q x i * F x := by
  have ha := sum_flip i (fun x => Q x * spin x i * F x)
  have hb := sum_flip i (fun x => Q x * conditionalMean Q x i * F x)
  simp only [spin_flip_self, conditionalMean_flip, hF] at ha hb
  have he (x : Spin n) :
      Q x * spin x i * F x + Q (flip x i) * -spin x i * F x =
      Q x * conditionalMean Q x i * F x +
        Q (flip x i) * conditionalMean Q x i * F x := by
    have hm := conditionalMean_mul_mass Q hQ x i
    have := congrArg (fun z => z * F x) hm
    nlinarith only [this]
  have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun x _ => he x)
  simp only [Finset.sum_add_distrib, ha, hb] at hh
  linarith only [hh]

lemma law_integration_by_parts {n : ℕ} (Q : Spin n → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (i : Fin n) (F : Spin n → ℝ) :
    (∑ x, Q x * (spin x i - conditionalMean Q x i) * F x) =
      ∑ x, Q x * (1-spin x i*conditionalMean Q x i) * halfDiff i F x := by
  have hh : ∀ x, (F (flip x i) - spin (flip x i) i * halfDiff i F (flip x i)) =
      F x - spin x i * halfDiff i F x := by
    intro x
    rw [spin_flip_self, halfDiff_flip]
    linarith only [flip_sub i F x]
  have he := law_coordinate_mean Q hQ i
    (fun x => F x-spin x i*halfDiff i F x) hh
  have h1 (x : Spin n) : Q x * spin x i * (F x-spin x i*halfDiff i F x) =
      Q x*spin x i*F x - Q x*halfDiff i F x := by
    have hs := spin_sq x i
    nlinarith only [congrArg (fun z : ℝ => Q x*halfDiff i F x*z) hs]
  simp_rw [h1] at he
  simp only [mul_sub, Finset.sum_sub_distrib] at he
  have h2 (x : Spin n) : Q x * (spin x i - conditionalMean Q x i) * F x =
      Q x * spin x i * F x - Q x * conditionalMean Q x i * F x := by ring
  have h3 (x : Spin n) : Q x * (1-spin x i*conditionalMean Q x i) * halfDiff i F x =
      Q x * halfDiff i F x -
        Q x * conditionalMean Q x i * (spin x i * halfDiff i F x) := by ring
  simp_rw [h2, h3, Finset.sum_sub_distrib]
  linarith only [he]

lemma law_integration_by_parts_variance {n : ℕ} (Q : Spin n → ℝ)
    (hQ : ∀ x, 0 ≤ Q x) (i : Fin n) (F : Spin n → ℝ) :
    (∑ x, Q x * (spin x i-conditionalMean Q x i) * F x) =
      ∑ x, Q x*(1-(conditionalMean Q x i)^2)*halfDiff i F x := by
  rw [law_integration_by_parts Q hQ]
  have hh := law_coordinate_mean Q hQ i
    (fun x => conditionalMean Q x i*halfDiff i F x)
    (by intro x; rw [conditionalMean_flip,halfDiff_flip])
  simp only [mul_sub,sub_mul,mul_one,Finset.sum_sub_distrib,pow_two,← mul_assoc] at hh ⊢
  rw [hh]

lemma gibbs_flipRate_fraction {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) (i : Fin n) :
    flipRate J x i = gibbs J (flip x i)/(gibbs J x+gibbs J (flip x i)) := by
  have hf : flipRate J (flip x i) i = 1-flipRate J x i := by
    simp only [flipRate, spin_flip_self, mean_flip J hdiag]
    ring
  have hh := gibbs_detailed_balance J hJ hdiag x i
  rw [hf] at hh
  apply (eq_div_iff (ne_of_gt (add_pos (gibbs_pos J x) (gibbs_pos J _)))).2
  nlinarith only [hh]

lemma conditionalMean_gibbs {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (x : Spin n) (i : Fin n) : conditionalMean (gibbs J) x i = mean J x i := by
  have hh := gibbs_flipRate_fraction J hJ hdiag x i
  have hs := spin_sq x i
  have hr : (gibbs J x-gibbs J (flip x i))/(gibbs J x+gibbs J (flip x i)) =
      1-2*flipRate J x i := by
    rw [hh]
    field_simp [ne_of_gt (add_pos (gibbs_pos J x) (gibbs_pos J (flip x i)))]
    ring
  rw [conditionalMean, hr, flipRate]
  nlinarith only [congrArg (fun z : ℝ => mean J x i*z) hs]

lemma lawDirichlet_gibbs {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (f : Spin n → ℝ) : lawDirichlet (gibbs J) f = dirichlet J f f := by
  have he (i : Fin n) :
      (∑ x, gibbs J x * flipRate J x i * (f x - f (flip x i))^2) =
        2 * (∑ x, gibbs J x * siteVariance J x i * halfDiff i f x * halfDiff i f x) := by
    have hh := sum_flip i (fun x => gibbs J x * flipRate J x i * f x * (f x-f (flip x i)))
    simp only [gibbs_detailed_balance J hJ hdiag, flip_flip] at hh
    have hk (x : Spin n) : gibbs J x * flipRate J x i * (f x-f (flip x i))^2 =
        gibbs J x * flipRate J x i * f x * (f x-f (flip x i)) +
        gibbs J x * flipRate J x i * f (flip x i) * (f (flip x i)-f x) := by ring
    simp_rw [hk]
    rw [Finset.sum_add_distrib, hh]
    have hd : (∑ x, gibbs J x * flipRate J x i * f x * (f x-f (flip x i))) =
        ∑ x, gibbs J x * siteVariance J x i * halfDiff i f x * halfDiff i f x := by
      convert gibbs_edge_dirichlet J hJ hdiag i f f using 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hd]
    ring
  unfold lawDirichlet
  simp_rw [mul_div_assoc, ← gibbs_flipRate_fraction J hJ hdiag]
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hc (z : ℝ) : 2*z/2=z := by ring
  rw [hc]
  unfold dirichlet gibbsExpectation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem gibbs_conditional_means_energy {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (Q : Spin n → ℝ) (hQ : ∀ x, 0 ≤ Q x) :
    (∑ x, Q x * ∑ i, (conditionalMean Q x i - mean J x i)^2) ≤
      4 * dirichlet J (fun x => Real.sqrt (Q x/gibbs J x))
        (fun x => Real.sqrt (Q x/gibbs J x)) := by
  simpa only [conditionalMean_gibbs J hJ hdiag, lawDensityEnergy,
    lawDirichlet_gibbs J hJ hdiag] using conditional_means_energy (gibbs J) Q (gibbs_pos J) hQ

lemma lawDensityEnergy_nonneg {n : ℕ} (P Q : Spin n → ℝ)
    (hP : ∀ x, 0 < P x) : 0 ≤ lawDensityEnergy P Q := by
  unfold lawDensityEnergy lawDirichlet
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun x _ =>
    mul_nonneg (div_nonneg (mul_nonneg (hP x).le (hP _).le)
      (add_nonneg (hP x).le (hP _).le)) (sq_nonneg _)))

lemma lawDensityEnergy_le {n : ℕ} (P Q : Spin n → ℝ)
    (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 ≤ Q x) :
    lawDensityEnergy P Q ≤ (n:ℝ) * ∑ x, Q x := by
  rw [lawDensityEnergy_eq P Q hP hQ]
  have hlocal (i : Fin n) (x : Spin n) :
      (Real.sqrt (P (flip x i))*Real.sqrt (Q x)-
        Real.sqrt (P x)*Real.sqrt (Q (flip x i)))^2/(P x+P (flip x i)) ≤ Q x+Q (flip x i) := by
    apply (div_le_iff₀ (add_pos (hP x) (hP _))).2
    have ha := Real.sq_sqrt (hP x).le
    have hb := Real.sq_sqrt (hP (flip x i)).le
    have hc := Real.sq_sqrt (hQ x)
    have hd := Real.sq_sqrt (hQ (flip x i))
    have he : (Real.sqrt (P (flip x i))*Real.sqrt (Q x))^2 = P (flip x i)*Q x := by
      rw [mul_pow, hb, hc]
    have hf : (Real.sqrt (P x)*Real.sqrt (Q (flip x i)))^2 = P x*Q (flip x i) := by
      rw [mul_pow, ha, hd]
    nlinarith only [he, hf,
      mul_nonneg (hP x).le (hQ x), mul_nonneg (hP (flip x i)).le (hQ (flip x i)),
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg (P (flip x i))) (Real.sqrt_nonneg (Q x)))
        (mul_nonneg (Real.sqrt_nonneg (P x)) (Real.sqrt_nonneg (Q (flip x i))))]
  calc
    _ ≤ (∑ i : Fin n, ∑ x, (Q x+Q (flip x i)))/2 := by
      exact div_le_div_of_nonneg_right
        (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun x _ => hlocal i x)))
          (by norm_num)
    _ = _ := by simp only [Finset.sum_add_distrib, sum_flip, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma weighted_cauchy_sq {α : Type*} [Fintype α] (w f g : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    (∑ a, w a*f a*g a)^2 ≤ (∑ a, w a*f a^2)*(∑ a, w a*g a^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    Finset.univ (fun a _ => mul_nonneg (hw a) (sq_nonneg _))
      (fun a _ => mul_nonneg (hw a) (sq_nonneg _))
  intro a _
  exact le_of_eq (by ring)

theorem weak_residual_base {n : ℕ} (P Q : Spin n → ℝ)
    (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 ≤ Q x) (hQsum : ∑ x, Q x=1)
    (U : Spin n → Fin n → ℝ) (A B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ x, ∑ i, |halfDiff i (fun y => U y i) x| ≤ A)
    (hU : ∀ x, ∑ i, U x i^2 ≤ B^2) :
    |∑ x, Q x * ∑ i, (spin x i-conditionalMean P x i)*U x i| ≤
      2*A+2*B*Real.sqrt (lawDensityEnergy P Q) := by
  let a := ∑ x, Q x * ∑ i, (1-spin x i*conditionalMean Q x i) * halfDiff i (fun y => U y i) x
  let b := ∑ x, Q x * ∑ i, (conditionalMean Q x i-conditionalMean P x i)*U x i
  have he : (∑ x, Q x * ∑ i, (spin x i-conditionalMean P x i)*U x i) = a+b := by
    have hs (x : Spin n) (i : Fin n) :
        (spin x i-conditionalMean P x i)*U x i =
          (spin x i-conditionalMean Q x i)*U x i+
          (conditionalMean Q x i-conditionalMean P x i)*U x i := by ring
    simp_rw [hs, Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
    congr 1
    dsimp [a]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun x i =>
      Q x*((1-spin x i*conditionalMean Q x i)*halfDiff i (fun y => U y i) x))]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [mul_assoc] using law_integration_by_parts Q hQ i (fun y => U y i)
  have ha : |a| ≤ 2*A := by
    have hs (x : Spin n) (i : Fin n) : |1-spin x i*conditionalMean Q x i| ≤ 2 := by
      have hsp : |spin x i|=1 := by cases hx : x i <;> simp [spin,hx]
      calc
        _ ≤ |(1:ℝ)|+|spin x i*conditionalMean Q x i| := abs_sub _ _
        _ ≤ 2 := by rw [abs_one, abs_mul,hsp,one_mul]; linarith [conditionalMean_abs_le Q hQ x i]
    calc
      |a| ≤ ∑ x, |Q x * ∑ i, (1-spin x i*conditionalMean Q x i)*halfDiff i (fun y => U y i) x| :=
        Finset.abs_sum_le_sum_abs ..
      _ = ∑ x, Q x * |∑ i, (1-spin x i*conditionalMean Q x i)*halfDiff i (fun y => U y i) x| := by
        simp only [abs_mul, abs_of_nonneg (hQ _)]
      _ ≤ ∑ x, Q x * (2*A) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (hQ x)
        calc
          _ ≤ ∑ i, |(1-spin x i*conditionalMean Q x i)*halfDiff i (fun y => U y i) x| :=
            Finset.abs_sum_le_sum_abs ..
          _ ≤ ∑ i, 2*|halfDiff i (fun y => U y i) x| := by
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hs x i) (abs_nonneg _)
          _ ≤ 2*A := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hA x) (by norm_num)
      _ = 2*A := by rw [← Finset.sum_mul, hQsum,one_mul]
  have hb : |b| ≤ 2*B*Real.sqrt (lawDensityEnergy P Q) := by
    have hcs := weighted_cauchy_sq (fun a : Spin n × Fin n => Q a.1)
      (fun a => conditionalMean Q a.1 a.2-conditionalMean P a.1 a.2)
      (fun a => U a.1 a.2) (fun a => hQ a.1)
    simp only [Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum] at hcs
    have hUb : (∑ x, Q x*∑ i, U x i^2) ≤ B^2 := by
      calc
        _ ≤ ∑ x, Q x*B^2 := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hU x) (hQ x))
        _ = B^2 := by rw [← Finset.sum_mul,hQsum,one_mul]
    have hc := conditional_means_energy P Q hP hQ
    have hd := lawDensityEnergy_nonneg P Q hP
    have hUI : 0 ≤ ∑ x, Q x*∑ i, U x i^2 := by
      exact Finset.sum_nonneg (fun x _ => mul_nonneg (hQ x)
        (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
    have hbound := mul_le_mul hc hUb hUI (show 0 ≤ 4*lawDensityEnergy P Q by positivity)
    have he2 := Real.sq_sqrt hd
    have hpos : 0 ≤ 2*B*Real.sqrt (lawDensityEnergy P Q) := by positivity
    apply (sq_le_sq₀ (abs_nonneg b) hpos).1
    rw [sq_abs]
    have hid : (2*B*Real.sqrt (lawDensityEnergy P Q))^2 = 4*lawDensityEnergy P Q*B^2 := by
      rw [mul_pow,he2]
      ring
    rw [hid]
    exact hcs.trans hbound
  rw [he]
  exact (abs_add_le a b).trans (add_le_add ha hb)

end SKGapCutoff.Static

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal

end

end OAI
