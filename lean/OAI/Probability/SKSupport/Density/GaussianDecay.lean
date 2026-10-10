import Mathlib
import OAI.Probability.SKSupport.Backward.BackwardRescale

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma linear_abs_le_quadratic {d : ℝ} (hd : 0 < d) (K x : ℝ) :
    K*|x| ≤ d/2*x^2+K^2/(2*d) := by
  apply (mul_le_mul_iff_of_pos_left (show (0:ℝ)<2*d by positivity)).mp
  have he : (2*d)*(d/2*x^2+K^2/(2*d))=d^2*x^2+K^2 := by field_simp
  rw [he]
  have hs : 0 ≤ d^2*x^2-2*d*K*|x|+K^2 := by
    have heq : d^2*x^2-2*d*K*|x|+K^2=(d*|x|-K)^2 := by
      rw [sub_sq,mul_pow,sq_abs]
      ring
    rw [heq]
    exact sq_nonneg _
  nlinarith only [hs]

lemma integrable_gaussian_linear {d : ℝ} (hd : 0 < d) (K : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-d*x^2+K*|x|)) := by
  apply ((integrable_exp_neg_mul_sq (half_pos hd)).const_mul (Real.exp (K^2/(2*d)))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := linear_abs_le_quadratic hd K x
  linarith

lemma integrable_gaussian_expBound {g : ℝ → ℝ} (hgm : Measurable g) (hg : ExponentialBound g)
    {d : ℝ} (hd : 0 < d) : Integrable (fun x => Real.exp (-d*x^2)*g x) := by
  obtain ⟨A,K,hA⟩ := hg
  apply ((integrable_gaussian_linear hd K).const_mul (A:ℝ)).mono' (by fun_prop)
  filter_upwards [] with x
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-d*x^2)*|g x| ≤ Real.exp (-d*x^2)*((A:ℝ)*Real.exp ((K:ℝ)*|x|)) :=
      mul_le_mul_of_nonneg_left (hA x) (Real.exp_nonneg _)
    _ = (A:ℝ)*Real.exp (-d*x^2+(K:ℝ)*|x|) := by rw [Real.exp_add];ring

lemma ExponentialBound.mul {f g : ℝ → ℝ} (hf : ExponentialBound f) (hg : ExponentialBound g) :
    ExponentialBound (fun x => f x*g x) := by
  obtain ⟨A,K,hA⟩ := hf
  obtain ⟨B,J,hB⟩ := hg
  refine ⟨A*B,K+J,fun x => ?_⟩
  rw [abs_mul]
  calc
    |f x| * |g x| ≤ ((A:ℝ)*Real.exp ((K:ℝ)*|x|))*((B:ℝ)*Real.exp ((J:ℝ)*|x|)) :=
      mul_le_mul (hA x) (hB x) (abs_nonneg _) (by positivity)
    _ = ((A*B:ℝ≥0):ℝ)*Real.exp (((K+J:ℝ≥0):ℝ)*|x|) := by
      simp only [NNReal.coe_mul,NNReal.coe_add,add_mul,Real.exp_add]
      ring

lemma gaussian_convolution_quadratic {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x y : ℝ) :
    (1/(8*(a+t)))*(x^2+y^2) ≤ x^2/(2*a)+(y-x)^2/(2*t) := by
  have hs := add_pos ha ht
  have h1 : 1/(2*(a+t)) ≤ 1/(2*a) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : 1/(2*(a+t)) ≤ 1/(2*t) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hq : x^2+y^2 ≤ 4*(x^2+(y-x)^2) := by nlinarith [sq_nonneg (y-2*x),sq_nonneg x]
  calc
    _ ≤ (1/(8*(a+t)))*(4*(x^2+(y-x)^2)) := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (1/(2*(a+t)))*x^2+(1/(2*(a+t)))*(y-x)^2 := by
      field_simp
      ring
    _ ≤ (1/(2*a))*x^2+(1/(2*t))*(y-x)^2 := add_le_add
      (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
    _ = _ := by ring

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma continuous_dslope_zero {f : ℝ → ℝ} (hf : Differentiable ℝ f) : Continuous (dslope f 0) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x=0
  · subst x;exact continuousAt_dslope_same.mpr (hf 0)
  · exact (continuousAt_dslope_of_ne hx).mpr (hf x).continuousAt

def quotientExtension (g r : ℝ → ℝ) (x : ℝ) := dslope g 0 x/dslope r 0 x

lemma BackwardShape.nonzero {r : ℝ → ℝ} (hr : BackwardShape r) {x : ℝ} (hx : x ≠ 0) : r x ≠ 0 := by
  intro he
  exact hx ((strictMono_of_deriv_pos hr.derivative_pos).injective (he.trans hr.odd.map_zero.symm))

lemma BackwardShape.dslope_nonzero {r : ℝ → ℝ} (hr : BackwardShape r) (x : ℝ) : dslope r 0 x ≠ 0 := by
  by_cases hx : x=0
  · subst x;simpa only [dslope_same] using ne_of_gt (hr.derivative_pos 0)
  · simp only [dslope_of_ne r hx,slope,vsub_eq_sub,sub_zero,hr.odd.map_zero,smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero hx) (hr.nonzero hx)

lemma quotientExtension_continuous {g r : ℝ → ℝ} (hg : Differentiable ℝ g)
    (hr : Differentiable ℝ r) (hshape : BackwardShape r) : Continuous (quotientExtension g r) :=
  (continuous_dslope_zero hg).div (continuous_dslope_zero hr) hshape.dslope_nonzero

lemma quotientExtension_eq {g r : ℝ → ℝ} (hg0 : g 0=0) (hr0 : r 0=0) {x : ℝ} (hx : x ≠ 0) :
    quotientExtension g r x=g x/r x := by
  dsimp [quotientExtension]
  simp only [dslope_of_ne _ hx,slope,vsub_eq_sub,hg0,hr0,sub_zero,smul_eq_mul]
  field_simp

lemma BackwardShape.abs_eq {r : ℝ → ℝ} (hr : BackwardShape r) (x : ℝ) : |r x|=r |x| := by
  have hm := (strictMono_of_deriv_pos hr.derivative_pos).monotone
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx,abs_of_nonneg (by simpa only [hr.odd.map_zero] using hm hx)]
  · have hxn : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    rw [abs_of_nonpos hxn,abs_of_nonpos (by simpa only [hr.odd.map_zero] using hm hxn),hr.odd]

lemma quotient_linear_bound {g r : ℝ → ℝ} {K : ℝ≥0}
    (hg : Differentiable ℝ g) (hLip : LipschitzWith K g) (hg0 : g 0=0)
    (hr : Differentiable ℝ r) (hshape : BackwardShape r) :
    ∃ C : ℝ≥0, ∀ x, |g x/r x| ≤ (C:ℝ)*(1+|x|) := by
  have hq := quotientExtension_continuous hg hr hshape
  obtain ⟨R,hR⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).bddAbove_image hq.abs.continuousOn
  let C := Real.toNNReal (|R|+(K:ℝ)/r 1)
  have hr1 : 0 < r 1 := by
    simpa only [hshape.odd.map_zero] using
      strictMono_of_deriv_pos hshape.derivative_pos (by norm_num : (0:ℝ)<1)
  have hCR : R ≤ (C:ℝ) := (le_abs_self R).trans ((le_add_of_nonneg_right (div_nonneg K.coe_nonneg hr1.le)).trans (Real.le_coe_toNNReal _))
  have hCK : (K:ℝ)/r 1 ≤ (C:ℝ) := (le_add_of_nonneg_left (abs_nonneg R)).trans (Real.le_coe_toNNReal _)
  refine ⟨C,fun x => ?_⟩
  by_cases hx : x=0
  · subst x;simp only [hg0,zero_div,abs_zero,add_zero,mul_one];exact C.coe_nonneg
  by_cases hsmall : |x| ≤ 1
  · have hmem : x ∈ Icc (-1:ℝ) 1 := abs_le.mp hsmall
    have hb : |quotientExtension g r x| ≤ R := hR ⟨x,hmem,rfl⟩
    rw [quotientExtension_eq hg0 hshape.odd.map_zero hx] at hb
    exact (hb.trans hCR).trans (le_mul_of_one_le_right C.coe_nonneg (by linarith [abs_nonneg x]))
  · have hden : r 1 ≤ |r x| := by
      rw [hshape.abs_eq]
      exact (strictMono_of_deriv_pos hshape.derivative_pos).monotone (le_of_lt (lt_of_not_ge hsmall))
    have hnum : |g x| ≤ (K:ℝ)*|x| := by simpa only [Real.norm_eq_abs,hg0,sub_zero] using hLip.norm_sub_le x 0
    rw [abs_div]
    calc
      |g x|/|r x| ≤ ((K:ℝ)*|x|)/|r x| := div_le_div_of_nonneg_right hnum (abs_nonneg _)
      _ ≤ ((K:ℝ)*|x|)/r 1 := div_le_div_of_nonneg_left (by positivity) hr1 hden
      _ = ((K:ℝ)/r 1)*|x| := by ring
      _ ≤ (C:ℝ)*|x| := mul_le_mul_of_nonneg_right hCK (abs_nonneg x)
      _ ≤ (C:ℝ)*(1+|x|) := by nlinarith [C.coe_nonneg]

lemma exponentialBound_of_linear_bound {g : ℝ → ℝ} {C : ℝ≥0}
    (hC : ∀ x, |g x| ≤ (C:ℝ)*(1+|x|)) : ExponentialBound g := by
  refine ⟨C,1,fun x => ?_⟩
  simp only [NNReal.coe_one,one_mul]
  exact (hC x).trans (mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp |x|) C.coe_nonneg)

lemma exponentialBound_quotient {g r : ℝ → ℝ} {K : ℝ≥0}
    (hg : Differentiable ℝ g) (hLip : LipschitzWith K g) (hg0 : g 0=0)
    (hr : Differentiable ℝ r) (hshape : BackwardShape r) : ExponentialBound (fun x => g x/r x) := by
  obtain ⟨C,hC⟩ := quotient_linear_bound hg hLip hg0 hr hshape
  exact exponentialBound_of_linear_bound hC

end ZeroTemperatureSK.Heat

end
end

end OAI
