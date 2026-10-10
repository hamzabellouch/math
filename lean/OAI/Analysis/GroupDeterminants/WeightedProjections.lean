import OAI.Analysis.GroupDeterminants.ClosedTrace

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

open Filter Topology

section WeightedPair
variable {A : Type uA} [Ring A] [Algebra ℝ A]
def weightedPair (Q R : A) (a b c : ℝ) : A := a • Q + b • R + c • (1 - Q - R)
lemma weightedPair_mul (Q R : A) (hQ : Q * Q = Q) (hR : R * R = R)
    (hQR : Q * R = 0) (hRQ : R * Q = 0) (a b c d e f : ℝ) :
    weightedPair Q R a b c * weightedPair Q R d e f = weightedPair Q R (a*d) (b*e) (c*f) := by
  simp only [weightedPair, add_mul, mul_add, smul_mul_smul_comm,
    mul_sub, sub_mul, one_mul, mul_one, hQ, hR, hQR, hRQ, smul_zero,
    smul_sub]
  module
lemma weightedPair_one (Q R : A) : weightedPair Q R 1 1 1 = 1 := by
  simp only [weightedPair, one_smul]; abel
lemma weightedPair_unit (Q R : A) (hQ : Q * Q = Q) (hR : R * R = R)
    (hQR : Q * R = 0) (hRQ : R * Q = 0) (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : IsUnit (weightedPair Q R a b c) := by
  refine ⟨⟨weightedPair Q R a b c, weightedPair Q R a⁻¹ b⁻¹ c⁻¹, ?_, ?_⟩, rfl⟩
  · rw [weightedPair_mul Q R hQ hR hQR hRQ, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb,
      mul_inv_cancel₀ hc, weightedPair_one]
  · rw [weightedPair_mul Q R hQ hR hQR hRQ, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb,
      inv_mul_cancel₀ hc, weightedPair_one]
lemma weightedPair_inverse (Q R : A) (hQ : Q * Q = Q) (hR : R * R = R)
    (hQR : Q * R = 0) (hRQ : R * Q = 0) (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Ring.inverse (weightedPair Q R a b c) = weightedPair Q R a⁻¹ b⁻¹ c⁻¹ := by
  have hu := weightedPair_unit Q R hQ hR hQR hRQ a b c ha hb hc
  apply_fun (weightedPair Q R a b c * ·) using IsUnit.mul_right_injective hu
  dsimp only
  rw [Ring.mul_inverse_cancel _ hu, weightedPair_mul Q R hQ hR hQR hRQ,
    mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, mul_inv_cancel₀ hc, weightedPair_one]
end WeightedPair

section PairTrace
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

lemma trace_log_weightedPair (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (hstar : ∀ a, τ (star a) = star (τ a))
    (Q R : A) (hQ : Q * Q = Q) (hR : R * R = R)
    (hQR : Q * R = 0) (hRQ : R * Q = 0) (hQs : IsSelfAdjoint Q) (x : ℝ) :
    τ (CFC.log (star (weightedPair Q R (Real.exp x) (-Real.exp (-x)) (-1)) *
      weightedPair Q R (Real.exp x) (-Real.exp (-x)) (-1))) =
      (x * (2 * (τ (Q - R)).re) : ℝ) := by
  let M := fun y : ℝ => weightedPair Q R (Real.exp y) (-Real.exp (-y)) (-1)
  let M' := fun y : ℝ => weightedPair Q R (Real.exp y) (Real.exp (-y)) 0
  have hd (y : ℝ) : HasDerivAt M (M' y) y := by
    have h1 := (Real.hasDerivAt_exp y).smul_const Q
    have h2 := ((Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)).neg.smul_const R
    simpa [M, M', weightedPair] using (h1.add h2).add_const ((-1 : ℝ) • (1 - Q - R))
  have hdc : Continuous M' := by dsimp [M', weightedPair]; fun_prop
  have hu (y : ℝ) : IsUnit (M y) :=
    weightedPair_unit Q R hQ hR hQR hRQ _ _ _ (Real.exp_ne_zero y)
      (neg_ne_zero.mpr (Real.exp_ne_zero (-y))) (by norm_num)
  have hi (y : ℝ) : M' y * Ring.inverse (M y) = Q - R := by
    dsimp [M, M']
    rw [weightedPair_inverse Q R hQ hR hQR hRQ _ _ _ (Real.exp_ne_zero y)
      (neg_ne_zero.mpr (Real.exp_ne_zero (-y))) (by norm_num),
      weightedPair_mul Q R hQ hR hQR hRQ]
    simp [weightedPair, Real.exp_ne_zero, sub_eq_add_neg]
  have hdlog (y : ℝ) : HasDerivAt (fun y => τ (CFC.log (star (M y) * M y)))
      (2 * (τ (Q - R)).re : ℝ) y := by
    simpa only [hi y] using
      hasDerivAt_trace_log_star_mul_self τ hτ hstar hd hdc.continuousAt hu (x := y)
  have hdz (y : ℝ) : HasDerivAt (fun y => τ (CFC.log (star (M y) * M y)) -
      (y * (2 * (τ (Q - R)).re) : ℝ)) 0 y := by
    have hh := (((hasDerivAt_id y).mul_const (2 * (τ (Q - R)).re)).ofReal_comp)
    simpa only [Pi.sub_def, id_eq, one_mul, sub_self] using (hdlog y).sub hh
  have he := is_const_of_deriv_eq_zero (fun y => (hdz y).differentiableAt)
    (fun y => (hdz y).deriv) x 0
  have hz : star (M 0) * M 0 = 1 := by
    have he0 : M 0 = (2 : ℝ) • Q - 1 := by simp [M, weightedPair]; module
    rw [he0]
    simp only [star_sub, star_smul, star_one, hQs.star_eq, star_ofNat]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      mul_one, one_mul, hQ]
    module
  simp only [hz, CFC.log_one, map_zero, zero_mul, Complex.ofReal_zero, sub_zero] at he
  exact sub_eq_zero.mp he

end PairTrace

end GroupRingDeterminant

end

end OAI
