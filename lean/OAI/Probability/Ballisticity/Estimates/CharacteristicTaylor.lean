import Mathlib
import OAI.Probability.Ballisticity.Crossings.NearCrossEstimates

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def charPhase (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)

lemma charPhase_norm (x : ℝ) : ‖charPhase x‖=1 := Complex.norm_exp_ofReal_mul_I x
lemma charPhase_add (x y : ℝ) : charPhase (x+y)=charPhase x*charPhase y := by
  simp only [charPhase,Complex.ofReal_add,add_mul,Complex.exp_add]

noncomputable def charTaylorConstant : ℝ := Real.exp 1+4
lemma charTaylorConstant_nonneg : 0 ≤ charTaylorConstant := by unfold charTaylorConstant; positivity

lemma charPhase_quadratic_error (x : ℝ) :
    ‖charPhase x-(1+(x:ℂ)*Complex.I-(x:ℂ)^2/2)‖ ≤ charTaylorConstant*|x|^3 := by
  have hx0 := abs_nonneg x
  have heq : (∑ m ∈ Finset.range 3, (((x:ℂ)*Complex.I)^m)/(m.factorial:ℂ)) =
      1+(x:ℂ)*Complex.I-(x:ℂ)^2/2 := by
    simp [Finset.sum_range_succ, pow_succ]
    ring_nf
    simp [Complex.I_sq]
    ring
  by_cases hx : |x| ≤ 1
  · have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((x:ℂ)*Complex.I) 3
    rw [heq] at h
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] at h
    exact h.trans (by
      have he := Real.exp_le_exp.mpr hx
      have hp : 0 ≤ |x|^3 := by positivity
      unfold charTaylorConstant
      nlinarith)
  · have hx1 : 1 ≤ |x| := le_of_not_ge hx
    have hn : ‖charPhase x-(1+(x:ℂ)*Complex.I-(x:ℂ)^2/2)‖ ≤ 2+|x|+|x|^2/2 := by
      calc
        _ ≤ ‖charPhase x‖+‖1+(x:ℂ)*Complex.I-(x:ℂ)^2/2‖ := norm_sub_le _ _
        _ ≤ 1+(‖(1:ℂ)‖+‖(x:ℂ)*Complex.I‖+‖(x:ℂ)^2/2‖) := by
          rw [charPhase_norm]
          exact add_le_add (le_refl 1) ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _)))
        _ = 2+|x|+|x|^2/2 := by simp [norm_pow]; ring
    have h2 : |x| ≤ |x|^2 := by nlinarith
    have h3 : |x|^2 ≤ |x|^3 := by nlinarith [mul_le_mul_of_nonneg_right hx1 (sq_nonneg |x|)]
    have hp : 0 ≤ Real.exp 1*|x|^3 := by positivity
    unfold charTaylorConstant
    nlinarith

lemma abs_linear_cube_bound (a b x y : ℝ) :
    |a*x+b*y|^3 ≤ 4*(|a|+|b|)^3*(|x|^3+|y|^3) := by
  have hsum := abs_add_le (a*x) (b*y)
  rw [abs_mul,abs_mul] at hsum
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hx := abs_nonneg x
  have hy := abs_nonneg y
  have hlin : |a*x+b*y| ≤ (|a|+|b|)*(|x|+|y|) := by nlinarith
  have hpow := pow_le_pow_left₀ (abs_nonneg _) hlin 3
  have hc : (|x|+|y|)^3 ≤ 4*(|x|^3+|y|^3) := by
    nlinarith [mul_nonneg (sq_nonneg (|x|-|y|)) (add_nonneg hx hy)]
  calc
    _ ≤ ((|a|+|b|)*(|x|+|y|))^3 := hpow
    _ = (|a|+|b|)^3*(|x|+|y|)^3 := mul_pow _ _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc (pow_nonneg (add_nonneg ha hb) 3)]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma normalJointPast_complex_weighted_moment_integrable {q k : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    Integrable (fun P => F (pairPastCoordinates v P)*((pairPathIncrement b s t P:ℂ)^k)) μ := by
  have hi := normalJointPast_integrable_abs_pow μ c h s t hst ht b k
  have hj : Integrable (fun P => (pairPathIncrement b s t P)^k) μ :=
    (integrable_norm_iff (by fun_prop : Measurable (fun P => (pairPathIncrement b s t P)^k)).aestronglyMeasurable).mp
      (by simpa [Real.norm_eq_abs,abs_pow] using hi)
  have hc := hj.ofReal (𝕜 := ℂ)
  simp only [RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_pow] at hc
  apply hc.bdd_mul (by fun_prop)
  filter_upwards [] with P
  exact F.norm_coe_le_norm _

lemma normalJointPast_complex_moment {q k : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    (∫ P, F (pairPastCoordinates v P)*((pairPathIncrement b s t P:ℂ)^k) ∂μ)=
      (∫ P, F (pairPastCoordinates v P) ∂μ)*
        ((∫ z : ℝ, (z^k:ℝ) ∂gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)) : ℝ):ℂ) := by
  have hh := product_law_integral_mul μ (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)))
    (pairPastCoordinates v) (pairPathIncrement b s t) (by fun_prop) (by fun_prop)
    (h q v s t hv hst ht b) F (fun z => (z:ℂ)^k) F.continuous.measurable (by fun_prop)
  simpa only [← Complex.ofReal_pow,integral_complex_ofReal] using hh

lemma normalJointPast_complex_mean {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    (∫ P, F (pairPastCoordinates v P)*(pairPathIncrement b s t P:ℂ) ∂μ)=0 := by
  simpa using normalJointPast_complex_moment (k := 1) μ c h v s t hv hst ht b F

lemma normalJointPast_complex_second {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    (∫ P, F (pairPastCoordinates v P)*(pairPathIncrement b s t P:ℂ)^2 ∂μ)=
      (∫ P, F (pairPastCoordinates v P) ∂μ)*(((c:ℝ)*((t:ℝ)-s)):ℂ) := by
  rw [normalJointPast_complex_moment μ c h v s t hv hst ht b F,gaussianReal_second_moment,
    NNReal.coe_mul,Real.toNNReal_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le))]
  push_cast
  rfl

lemma normalJointPast_complex_cross_integrable {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hst : s < t) (ht : (t:ℝ) < 1)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    Integrable (fun P => F (pairPastCoordinates v P)*
      ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ)) μ := by
  apply (normalJointPast_cross_integrable μ c h s t hst ht).ofReal.bdd_mul (by fun_prop)
  filter_upwards [] with P
  exact F.norm_coe_le_norm _

lemma normalJointPast_complex_cross_bound {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) {A K : ℝ} (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖∫ P, F (pairPastCoordinates v P)*
      ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ‖ ≤
      2*‖F‖*(K*Real.exp (-A*ρ^2/((t:ℝ)-s))+
        4*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment+
        ((c:ℝ)*((t:ℝ)-s))*(∫ P, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ)) := by
  let Fr := F.comp Complex.reCLM Complex.reCLM.lipschitzWith
  let Fi := F.comp Complex.imCLM Complex.imCLM.lipschitzWith
  have hrn : ‖Fr‖ ≤ ‖F‖ := (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
    (fun z => (Complex.abs_re_le_norm (F z)).trans (F.norm_coe_le_norm z))
  have hin : ‖Fi‖ ≤ ‖F‖ := (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
    (fun z => (Complex.abs_im_le_norm (F z)).trans (F.norm_coe_le_norm z))
  have hr := normalJointPast_cross_bound μ c h hcross v s t hv hst ht Fr hρ
  have hi := normalJointPast_cross_bound μ c h hcross v s t hv hst ht Fi hρ
  have hI := normalJointPast_complex_cross_integrable μ c h v s t hst ht F
  have hre := integral_re hI
  have him := integral_im hI
  change (∫ P, (F (pairPastCoordinates v P)*
    ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ)).re ∂μ)=_ at hre
  change (∫ P, (F (pairPastCoordinates v P)*
    ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ)).im ∂μ)=_ at him
  simp only [RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at hre
  simp only [RCLike.im_eq_complex_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add] at him
  have hpos : 0 ≤ K*Real.exp (-A*ρ^2/((t:ℝ)-s))+
        4*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment+
        ((c:ℝ)*((t:ℝ)-s))*(∫ P, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ) := by
    have hh : 0 ≤ ∫ P : RealPathPair, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ :=
      integral_nonneg (fun P => (nearDiagonalCutoff_unit ρ (P.1 s-P.2 s)).1)
    have hd : 0 ≤ (t:ℝ)-s := sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le)
    have hm := normalThirdMoment_nonneg
    positivity
  calc
    _ ≤ |(∫ P, F (pairPastCoordinates v P)*
      ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ).re|+
      |(∫ P, F (pairPastCoordinates v P)*
      ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by
      rw [← hre,← him]
      have hr' := hr.trans (mul_le_mul_of_nonneg_right hrn hpos)
      have hi' := hi.trans (mul_le_mul_of_nonneg_right hin hpos)
      change |∫ P, Fr (pairPastCoordinates v P)*(pairPathIncrement false s t P*pairPathIncrement true s t P) ∂μ|+
        |∫ P, Fi (pairPastCoordinates v P)*(pairPathIncrement false s t P*pairPathIncrement true s t P) ∂μ| ≤ _
      nlinarith only [hr',hi']

end DirectionalTransience

end

end

end OAI
