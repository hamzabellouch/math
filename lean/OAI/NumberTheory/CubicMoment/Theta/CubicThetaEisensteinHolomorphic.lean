import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinConvergence
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace OAI

/-! Holomorphy of the actual cubic Eisenstein series on its initial
half-plane, obtained from a uniform summable row bound. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaHeightConstant_ge_one {p : ℂ × ℝ} (hp : 0 < p.2) :
    1 ≤ p.2*cubicThetaHeightConstant p := by
  have hz := Complex.normSq_nonneg p.1
  unfold cubicThetaHeightConstant
  apply (mul_le_mul_iff_right₀ hp).mp
  have he : p.2*(2*(2+(1+2*Complex.normSq p.1)/p.2^2))*p.2 =
      4*p.2^2+2+4*Complex.normSq p.1 := by field_simp; ring
  nlinarith [he,sq_nonneg (2*p.2-1)]

lemma cubicThetaEisensteinTerm_differentiable (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    Differentiable ℂ (fun s => cubicThetaEisensteinTerm r p s) := by
  let : NeZero (r.height p:ℂ) := ⟨Complex.ofReal_ne_zero.mpr (r.height_pos hp).ne'⟩
  exact (differentiable_const _).mul (differentiable_const_cpow_of_neZero _)

lemma cubicThetaEisensteinTerm_strip_bound (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0 < p.2) {A B : ℝ} (hA : 2 < A)
    {s : ℂ} (hs : A < s.re ∧ s.re < B) :
    ‖cubicThetaEisensteinTerm r p s‖ ≤ (p.2*cubicThetaHeightConstant p)^B*
      ((1+norm r.c)^(-A/2)*(1+norm r.d)^(-A/2)) := by
  have hc : 1 ≤ 1+norm r.c := by linarith [norm_nonneg r.c]
  have hd : 1 ≤ 1+norm r.d := by linarith [norm_nonneg r.d]
  have hc' := Real.rpow_le_rpow_of_exponent_le hc (show -s.re/2 ≤ -A/2 by linarith)
  have hd' := Real.rpow_le_rpow_of_exponent_le hd (show -s.re/2 ≤ -A/2 by linarith)
  have hH := Real.rpow_le_rpow_of_exponent_le (cubicThetaHeightConstant_ge_one hp) hs.2.le
  apply (cubicThetaEisensteinTerm_bound r hp (hA.trans hs.1)).trans
  exact mul_le_mul hH (mul_le_mul hc' hd' (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg (by linarith) _))
    (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg (by linarith [cubicThetaHeightConstant_ge_one hp]) _)

lemma cubicThetaEisenstein_differentiableOn_strip {p : ℂ × ℝ} (hp : 0 < p.2)
    {A B : ℝ} (hA : 2 < A) :
    DifferentiableOn ℂ (cubicThetaEisenstein p) {s : ℂ | A < s.re ∧ s.re < B} := by
  have ht : 1 < A/2 := by linarith
  have hsum := summable_eisenstein_one_add_norm ht
  have hprod : Summable (fun cd : Eisenstein × Eisenstein =>
      (1+norm cd.1)^(-(A/2))*(1+norm cd.2)^(-(A/2))) :=
    summable_mul_of_summable_norm hsum.norm hsum.norm
  have hi : Function.Injective (fun r : CubicThetaBottomRow => (r.c,r.d)) := by
    intro r t he
    exact CubicThetaBottomRow.ext (Prod.mk.inj he).1 (Prod.mk.inj he).2
  have hrows := (hprod.mul_left ((p.2*cubicThetaHeightConstant p)^B)).comp_injective hi
  apply Complex.differentiableOn_tsum_of_summable_norm hrows
  · intro r
    exact (cubicThetaEisensteinTerm_differentiable r hp).differentiableOn
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  · intro r s hs
    simpa only [Function.comp_apply,neg_div] using cubicThetaEisensteinTerm_strip_bound r hp hA hs

theorem cubicThetaEisenstein_differentiableAt {p : ℂ × ℝ} (hp : 0 < p.2)
    {s : ℂ} (hs : 2 < s.re) : DifferentiableAt ℂ (cubicThetaEisenstein p) s := by
  have hA : 2 < (2+s.re)/2 := by linarith
  have hU : IsOpen {z : ℂ | (2+s.re)/2 < z.re ∧ z.re < s.re+1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  exact (cubicThetaEisenstein_differentiableOn_strip (B := s.re+1) hp hA).differentiableAt
    (hU.mem_nhds ⟨by linarith,by linarith⟩)

end CubicFirstMoment

end

end OAI
