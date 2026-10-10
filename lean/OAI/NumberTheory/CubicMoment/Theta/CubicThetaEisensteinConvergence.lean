import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinBounds

namespace OAI

/-! Absolute convergence of the actual cubic Eisenstein series in
Re(s)>2, proved from the Eisenstein lattice and the positive height form. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma summable_eisenstein_one_add_norm {t : ℝ} (ht : 1 < t) :
    Summable (fun n : Eisenstein => (1+norm n)^(-t)) := by
  have hsingle : Summable (fun n : Eisenstein => if n = 0 then (1:ℝ) else 0) := by
    apply (hasSum_single 0 ?_).summable
    intro n hn
    simp [hn]
  apply (hsingle.add (summable_eisenstein_norm_rpow ht)).of_nonneg_of_le
  · intro n
    exact Real.rpow_nonneg (by linarith [norm_nonneg n]) _
  · intro n
    by_cases hn : n = 0
    · simpa [hn,norm] using (Real.rpow_nonneg (show (0:ℝ) ≤ 0 from le_rfl) (-t))
    · have h := Real.rpow_le_rpow_of_nonpos (norm_pos_of_ne_zero hn)
        (show norm n ≤ 1+norm n by linarith) (show -t ≤ 0 by linarith)
      simpa only [hn,ite_false,zero_add] using h

lemma cubicThetaEisensteinTerm_bound (r : CubicThetaBottomRow) {p : ℂ × ℝ}
    (hp : 0 < p.2) {s : ℂ} (hs : 2 < s.re) :
    ‖cubicThetaEisensteinTerm r p s‖ ≤
      (p.2*cubicThetaHeightConstant p)^s.re*
        ((1+norm r.c)^(-s.re/2)*(1+norm r.d)^(-s.re/2)) := by
  have hC := cubicThetaHeightConstant_pos hp
  have hN : 0 < 1+norm r.c+norm r.d := by linarith [norm_nonneg r.c,norm_nonneg r.d]
  rw [cubicThetaEisensteinTerm,norm_mul,norm_star,r.phase_norm,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (r.height_pos hp)]
  calc
    _ ≤ ((p.2*cubicThetaHeightConstant p)/(1+norm r.c+norm r.d))^s.re :=
      Real.rpow_le_rpow (r.height_pos hp).le (r.height_le hp) (by linarith)
    _ = (p.2*cubicThetaHeightConstant p)^s.re*(1+norm r.c+norm r.d)^(-s.re) := by
      rw [Real.div_rpow (mul_pos hp hC).le hN.le,Real.rpow_neg hN.le]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (cubicTheta_two_norm_decay (norm_nonneg r.c) (norm_nonneg r.d) (by linarith : 0 ≤ s.re))
      (Real.rpow_nonneg (mul_pos hp hC).le _)

theorem cubicThetaEisenstein_summable {p : ℂ × ℝ} (hp : 0 < p.2) {s : ℂ} (hs : 2 < s.re) :
    Summable (fun r : CubicThetaBottomRow => cubicThetaEisensteinTerm r p s) := by
  have ht : 1 < s.re/2 := by linarith
  have hsum := summable_eisenstein_one_add_norm ht
  have hprod : Summable (fun cd : Eisenstein × Eisenstein =>
      (1+norm cd.1)^(-(s.re/2))*(1+norm cd.2)^(-(s.re/2))) :=
    summable_mul_of_summable_norm hsum.norm hsum.norm
  have hi : Function.Injective (fun r : CubicThetaBottomRow => (r.c,r.d)) := by
    intro r t he
    apply CubicThetaBottomRow.ext
    · exact (Prod.mk.inj he).1
    · exact (Prod.mk.inj he).2
  apply ((hprod.mul_left ((p.2*cubicThetaHeightConstant p)^s.re)).comp_injective hi).of_norm_bounded
  intro r
  simpa only [neg_div,Function.comp_apply] using cubicThetaEisensteinTerm_bound r hp hs

end CubicFirstMoment

end

end OAI
