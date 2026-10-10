import OAI.Probability.Renewal.Tilt

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

lemma sumLaw_tilt_apply (p : PMF ℕ) (u : ℝ) (hu : 0 ≤ u) (k m : ℕ) :
    sumLaw (tilt p u hu) k m =
      ENNReal.ofReal (Real.exp (-u * (m : ℝ)) / laplace p u ^ k) * sumLaw p k m := by
  classical
  induction k generalizing m with
  | zero =>
    simp only [sumLaw, PMF.pure_apply, pow_zero, div_one]
    split_ifs with hm <;> simp_all
  | succ k hk =>
    simp only [sumLaw, PMF.bind_apply, PMF.map_apply, tilt_apply, hk]
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro j
    simp_rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro r
    split_ifs with hsum
    · subst m
      have hz := laplace_pos p hu
      have hid : Real.exp (-u * ((j + r : ℕ) : ℝ)) / laplace p u ^ (k + 1) =
          (Real.exp (-u * (j : ℝ)) / laplace p u) *
          (Real.exp (-u * (r : ℝ)) / laplace p u ^ k) := by
        rw [div_mul_div_comm, ← Real.exp_add, pow_succ]
        push_cast
        rw [show -u * ((j : ℝ) + r) = -u * (j : ℝ) + -u * (r : ℝ) by ring]
        field_simp
      rw [hid, ENNReal.ofReal_mul (by positivity)]
      ring
    · simp

lemma sumLaw_untilt_real (p : PMF ℕ) (u : ℝ) (hu : 0 ≤ u) (k m : ℕ) :
    (sumLaw p k m).toReal = Real.exp (u * (m : ℝ)) * laplace p u ^ k *
      (sumLaw (tilt p u hu) k m).toReal := by
  rw [sumLaw_tilt_apply, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity [laplace_pos p hu])]
  have he : Real.exp (u * (m : ℝ)) * Real.exp (-u * (m : ℝ)) = 1 := by
    rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
  have hz := laplace_pos p hu
  simp only [neg_mul] at he
  field_simp
  nlinarith [congrArg (fun x : ℝ => (sumLaw p k m).toReal * x) he]

lemma pow_lower_from_deficit {z d : ℝ} (hz : 1 / 2 ≤ z) (hz1 : z ≤ 1)
    (hd : 1 - z ≤ d) (k : ℕ) : Real.exp (-2 * k * d) ≤ z ^ k := by
  have hz0 : 0 < z := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hz0
  have hinv : 1 - z⁻¹ ≥ -2 * (1 - z) := by
    have hh : 0 ≤ (1 - z) * (2 * z - 1) := mul_nonneg (by linarith) (by linarith)
    have hzid : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0.ne'
    nlinarith
  have hlower : -2 * d ≤ Real.log z := by linarith
  rw [← Real.exp_log (pow_pos hz0 k), Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg (α := ℝ) k)
  nlinarith

lemma untilt_lower (p : PMF ℕ) {a u C K : ℝ} (hu : 0 ≤ u)
    (hz : 1 / 2 ≤ laplace p u) (hC : 0 ≤ C)
    (hdef : 1 - laplace p u ≤ C * u ^ a) {k m : ℕ} (hk : (k : ℝ) * u ^ a ≤ K) :
    Real.exp (-2 * C * K) * (sumLaw (tilt p u hu) k m).toReal ≤ (sumLaw p k m).toReal := by
  have hp := pow_lower_from_deficit hz (laplace_le_one p hu) hdef k
  have hm := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 2 * C)
  have he : Real.exp (-2 * C * K) ≤ laplace p u ^ k :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans hp
  have hexp : 1 ≤ Real.exp (u * (m : ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  rw [sumLaw_untilt_real p u hu k m]
  have hfac : Real.exp (-2 * C * K) ≤ Real.exp (u * (m : ℝ)) * laplace p u ^ k :=
    he.trans (le_mul_of_one_le_left (pow_pos (laplace_pos p hu) k).le hexp)
  exact mul_le_mul_of_nonneg_right hfac ENNReal.toReal_nonneg

end HoneycombLocal

end

end OAI
