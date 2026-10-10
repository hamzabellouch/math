import Mathlib

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial

def rhoPolynomial : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => X ^ 2 * (rhoPolynomial n - (rhoPolynomial n).derivative)

def rhoWeight (p : Polynomial ℤ) (k : ℕ) : ℕ :=
  ∑ j ∈ p.support, (p.coeff j).natAbs * (j + k).factorial

def rhoJet (n : ℕ) (x : ℝ) : ℝ :=
  (rhoPolynomial n).eval₂ (Int.castRingHom ℝ) x⁻¹ * expNegInvGlue x

lemma rhoJet_zero (x : ℝ) : rhoJet 0 x = expNegInvGlue x := by
  simp [rhoJet, rhoPolynomial]

lemma rhoJet_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (rhoJet n) (rhoJet (n + 1) x) x := by
  unfold rhoJet
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    ((rhoPolynomial n).map (Int.castRingHom ℝ)) x
  simpa [rhoJet, rhoPolynomial, ← Polynomial.eval₂_eq_eval_map,
    Polynomial.derivative_map] using h

lemma rhoJet_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rhoJet n) := by
  unfold rhoJet
  simpa only [← Polynomial.eval₂_eq_eval_map] using
    (expNegInvGlue.contDiff_polynomial_eval_inv_mul
      ((rhoPolynomial n).map (Int.castRingHom ℝ)) (n := (⊤ : ℕ∞)))

lemma rhoJet_eq_iteratedDeriv (n : ℕ) : rhoJet n = iteratedDeriv n expNegInvGlue := by
  induction n with
  | zero => exact funext rhoJet_zero
  | succ n ih =>
    rw [iteratedDeriv_succ, ← ih]
    exact funext (fun x => (rhoJet_hasDerivAt n x).deriv.symm)

lemma rhoJet_zero_of_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) : rhoJet n x = 0 := by
  simp [rhoJet, expNegInvGlue.zero_of_nonpos hx]

lemma inv_pow_mul_rho_le {x : ℝ} (hx : 0 < x) (j k : ℕ) :
    x⁻¹ ^ j * expNegInvGlue x ≤ ((j + k).factorial : ℝ) * x ^ k := by
  have hf : (0 : ℝ) < (j + k).factorial := by positivity
  have he := Real.pow_div_factorial_le_exp x⁻¹ (inv_nonneg.mpr hx.le) (j + k)
  have hdiv : x⁻¹ ^ (j + k) / Real.exp x⁻¹ ≤ ((j + k).factorial : ℝ) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    simpa [mul_comm] using (div_le_iff₀ hf).mp he
  have hid : x⁻¹ ^ j * expNegInvGlue x =
      (x⁻¹ ^ (j + k) / Real.exp x⁻¹) * x ^ k := by
    rw [expNegInvGlue, ite_eq_right hx.not_ge, Real.exp_neg, pow_add]
    field_simp
    simp [inv_mul_cancel₀ (pow_ne_zero k hx.ne')]
  rw [hid]
  exact mul_le_mul_of_nonneg_right hdiv (pow_nonneg hx.le _)

lemma polynomial_rho_seam_bound (p : Polynomial ℤ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |p.eval₂ (Int.castRingHom ℝ) x⁻¹ * expNegInvGlue x| ≤
      (rhoWeight p k : ℝ) * x ^ k := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  calc
    |∑ j ∈ p.support, (Int.castRingHom ℝ) (p.coeff j) * x⁻¹ ^ j * expNegInvGlue x| ≤
        ∑ j ∈ p.support, |(Int.castRingHom ℝ) (p.coeff j) * x⁻¹ ^ j * expNegInvGlue x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ p.support, ((p.coeff j).natAbs : ℝ) * (x⁻¹ ^ j * expNegInvGlue x) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [abs_mul, abs_of_pos hx,
        abs_of_nonneg (expNegInvGlue.nonneg x), mul_assoc]
    _ ≤ ∑ j ∈ p.support, ((p.coeff j).natAbs : ℝ) *
        (((j + k).factorial : ℝ) * x ^ k) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (inv_pow_mul_rho_le hx j k) (Nat.cast_nonneg _)
    _ = (rhoWeight p k : ℝ) * x ^ k := by
      simp [rhoWeight, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, mul_assoc]

lemma rhoJet_bound (n : ℕ) (x : ℝ) : |rhoJet n x| ≤ (rhoWeight (rhoPolynomial n) 0 : ℝ) := by
  by_cases hx : 0 < x
  · simpa [rhoJet] using polynomial_rho_seam_bound (rhoPolynomial n) 0 hx
  · rw [rhoJet_zero_of_nonpos n (le_of_not_gt hx), abs_zero]
    exact Nat.cast_nonneg _

lemma rhoJet_seam_bound (n k : ℕ) {x ε : ℝ} (hε : 0 ≤ ε) (hx : x ≤ ε) :
    |rhoJet n x| ≤ (rhoWeight (rhoPolynomial n) k : ℝ) * ε ^ k := by
  by_cases hxpos : 0 < x
  · exact (polynomial_rho_seam_bound (rhoPolynomial n) k hxpos).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxpos.le hx _) (Nat.cast_nonneg _))
  · rw [rhoJet_zero_of_nonpos n (le_of_not_gt hxpos), abs_zero]
    positivity

lemma transition_denom_lower (x : ℝ) :
    1 / 9 ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  have hb : (1 / 9 : ℝ) ≤ expNegInvGlue (1 / 2) := by
    have he : Real.exp (2 : ℝ) < 9 := by
      have hh := Real.exp_one_lt_three
      have hp := Real.exp_pos 1
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    norm_num [expNegInvGlue, Real.exp_neg]
    rw [← one_div]
    apply (le_div_iff₀ (Real.exp_pos (2 : ℝ))).mpr
    linarith
  by_cases hx : 1 / 2 ≤ x
  · exact hb.trans ((expNegInvGlue.monotone hx).trans
      (le_add_of_nonneg_right (expNegInvGlue.nonneg _)))
  · have hh : 1 / 2 ≤ 1 - x := by linarith
    exact hb.trans ((expNegInvGlue.monotone hh).trans
      (le_add_of_nonneg_left (expNegInvGlue.nonneg _)))

def transitionWeight : ℕ → ℕ
  | 0 => 1
  | n + 1 => 9 * (rhoWeight (rhoPolynomial (n + 1)) 0 +
      ∑ i : Fin (n + 1),
        (n + 1).choose i * transitionWeight i *
          (2 * rhoWeight (rhoPolynomial (n + 1 - i)) 0))
termination_by n => n
decreasing_by exact i.isLt

def transitionDenom (x : ℝ) : ℝ := expNegInvGlue x + expNegInvGlue (1 - x)

lemma transitionDenom_contDiff : ContDiff ℝ (⊤ : ℕ∞) transitionDenom := by
  unfold transitionDenom
  fun_prop

lemma transitionDenom_jet_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n transitionDenom x| ≤ (2 * rhoWeight (rhoPolynomial n) 0 : ℕ) := by
  have ha : ContDiffAt ℝ n expNegInvGlue x := expNegInvGlue.contDiff.contDiffAt
  have hb : ContDiffAt ℝ n (fun x : ℝ => expNegInvGlue (1 - x)) x := by fun_prop
  unfold transitionDenom
  rw [iteratedDeriv_fun_add ha hb, iteratedDeriv_comp_const_sub]
  calc
    |iteratedDeriv n expNegInvGlue x + (-1 : ℝ) ^ n • iteratedDeriv n expNegInvGlue (1 - x)| ≤
        |iteratedDeriv n expNegInvGlue x| +
          |(-1 : ℝ) ^ n • iteratedDeriv n expNegInvGlue (1 - x)| := abs_add_le _ _
    _ = |rhoJet n x| + |rhoJet n (1 - x)| := by
      simp [← rhoJet_eq_iteratedDeriv, smul_eq_mul, abs_mul, abs_pow]
    _ ≤ (2 * rhoWeight (rhoPolynomial n) 0 : ℕ) := by
      have h₁ := rhoJet_bound n x
      have h₂ := rhoJet_bound n (1 - x)
      push_cast
      linarith

lemma transition_mul_denom : Real.smoothTransition * transitionDenom = expNegInvGlue := by
  funext x
  exact div_mul_cancel₀ _ (Real.smoothTransition.pos_denom x).ne'

lemma transition_jet_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n Real.smoothTransition x| ≤ (transitionWeight n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp only [iteratedDeriv_zero, transitionWeight]
      rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
      simpa using Real.smoothTransition.le_one x
    | succ n =>
      have hs : ContDiffAt ℝ (n + 1) Real.smoothTransition x :=
        Real.smoothTransition.contDiffAt
      have hd : ContDiffAt ℝ (n + 1) transitionDenom x :=
        transitionDenom_contDiff.contDiffAt.of_le
          (WithTop.coe_le_coe.mpr (show (↑(n + 1) : ℕ∞) ≤ ⊤ from le_top))
      have hL := iteratedDeriv_mul hs hd
      rw [transition_mul_denom, Finset.sum_range_succ] at hL
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
        iteratedDeriv_zero] at hL
      let S : ℝ := ∑ i ∈ Finset.range (n + 1),
        (n + 1).choose i * iteratedDeriv i Real.smoothTransition x *
          iteratedDeriv (n + 1 - i) transitionDenom x
      let Q : ℕ := ∑ i ∈ Finset.range (n + 1),
        (n + 1).choose i * transitionWeight i *
          (2 * rhoWeight (rhoPolynomial (n + 1 - i)) 0)
      have hS : |S| ≤ (Q : ℝ) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        dsimp only [Q]
        push_cast
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (ih i (Finset.mem_range.mp hi)) (Nat.cast_nonneg _)
        · simpa using transitionDenom_jet_bound (n + 1 - i) x
        · exact abs_nonneg _
        · positivity
      have he : iteratedDeriv (n + 1) Real.smoothTransition x * transitionDenom x =
          rhoJet (n + 1) x - S := by
        rw [rhoJet_eq_iteratedDeriv]
        linarith [hL]
      have hden := transition_denom_lower x
      change 1 / 9 ≤ transitionDenom x at hden
      have hp : 0 < transitionDenom x := by linarith
      have hbound : |iteratedDeriv (n + 1) Real.smoothTransition x| * transitionDenom x ≤
          (rhoWeight (rhoPolynomial (n + 1)) 0 : ℝ) + (Q : ℝ) := by
        rw [← abs_of_pos hp, ← abs_mul, he]
        exact (abs_sub _ _).trans (add_le_add (rhoJet_bound _ _) hS)
      have habs := abs_nonneg (iteratedDeriv (n + 1) Real.smoothTransition x)
      have hprod := mul_le_mul_of_nonneg_left hden habs
      rw [transitionWeight, show (∑ i : Fin (n + 1),
        (n + 1).choose i * transitionWeight i *
          (2 * rhoWeight (rhoPolynomial (n + 1 - i)) 0)) = Q from
          Fin.sum_univ_eq_sum_range (fun i : ℕ => (n + 1).choose i * transitionWeight i *
            (2 * rhoWeight (rhoPolynomial (n + 1 - i)) 0)) (n + 1)]
      push_cast
      change _ ≤ 9 * ((rhoWeight (rhoPolynomial (n + 1)) 0 : ℝ) + (Q : ℝ))
      nlinarith

end BalancedTransport.Effectivity
end

end OAI
