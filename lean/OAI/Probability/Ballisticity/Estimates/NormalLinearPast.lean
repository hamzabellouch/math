import Mathlib
import OAI.Probability.Ballisticity.Estimates.CharacteristicTaylor

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def pairLinearIncrement (a b : ℝ) (s t : unitInterval) : C(RealPathPair,ℝ) :=
  ⟨fun P => a*pairPathIncrement false s t P+b*pairPathIncrement true s t P,by fun_prop⟩

lemma normalJointPast_linear_mean_integrable {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hst : s < t) (ht : (t:ℝ) < 1)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    Integrable (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)) μ := by
  have hx := normalJointPast_complex_weighted_moment_integrable (k := 1) μ c h v s t hst ht false F
  have hy := normalJointPast_complex_weighted_moment_integrable (k := 1) μ c h v s t hst ht true F
  simp only [pow_one] at hx hy
  have hid : (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ))=
      (fun P => (a:ℂ)*(F (pairPastCoordinates v P)*(pairPathIncrement false s t P:ℂ))+
        (b:ℂ)*(F (pairPastCoordinates v P)*(pairPathIncrement true s t P:ℂ))) := by
    funext P
    simp only [pairLinearIncrement,ContinuousMap.coe_mk,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  rw [hid]
  exact (hx.const_mul (a:ℂ)).add (hy.const_mul (b:ℂ))

lemma normalJointPast_linear_mean {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    (∫ P, F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ) ∂μ)=0 := by
  have hx := normalJointPast_complex_weighted_moment_integrable (k := 1) μ c h v s t hst ht false F
  have hy := normalJointPast_complex_weighted_moment_integrable (k := 1) μ c h v s t hst ht true F
  simp only [pow_one] at hx hy
  have hid : (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ))=
      (fun P => (a:ℂ)*(F (pairPastCoordinates v P)*(pairPathIncrement false s t P:ℂ))+
        (b:ℂ)*(F (pairPastCoordinates v P)*(pairPathIncrement true s t P:ℂ))) := by
    funext P
    simp only [pairLinearIncrement,ContinuousMap.coe_mk,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  rw [hid,integral_add (hx.const_mul _) (hy.const_mul _),integral_const_mul,integral_const_mul,
    normalJointPast_complex_mean μ c h v s t hv hst ht false,
    normalJointPast_complex_mean μ c h v s t hv hst ht true]
  simp

lemma normalJointPast_linear_second_integrable {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hst : s < t) (ht : (t:ℝ) < 1)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    Integrable (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2) μ := by
  have hx := normalJointPast_complex_weighted_moment_integrable (k := 2) μ c h v s t hst ht false F
  have hy := normalJointPast_complex_weighted_moment_integrable (k := 2) μ c h v s t hst ht true F
  have hxy := normalJointPast_complex_cross_integrable μ c h v s t hst ht F
  have hid : (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2)=
      (fun P => (a:ℂ)^2*(F (pairPastCoordinates v P)*(pairPathIncrement false s t P:ℂ)^2)+
        (b:ℂ)^2*(F (pairPastCoordinates v P)*(pairPathIncrement true s t P:ℂ)^2)+
        2*(a:ℂ)*b*(F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ))) := by
    funext P
    simp only [pairLinearIncrement,ContinuousMap.coe_mk,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  rw [hid]
  exact ((hx.const_mul ((a:ℂ)^2)).add (hy.const_mul ((b:ℂ)^2))).add
    (hxy.const_mul (2*(a:ℂ)*b))

lemma normalJointPast_linear_second {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    (∫ P, F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2 ∂μ)=
      (((c:ℝ)*((t:ℝ)-s)*(a^2+b^2):ℝ):ℂ)*(∫ P, F (pairPastCoordinates v P) ∂μ)+
      2*(a:ℂ)*b*(∫ P, F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ) := by
  have hx := normalJointPast_complex_weighted_moment_integrable (k := 2) μ c h v s t hst ht false F
  have hy := normalJointPast_complex_weighted_moment_integrable (k := 2) μ c h v s t hst ht true F
  have hxy := normalJointPast_complex_cross_integrable μ c h v s t hst ht F
  have hid : (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2)=
      (fun P => (a:ℂ)^2*(F (pairPastCoordinates v P)*(pairPathIncrement false s t P:ℂ)^2)+
        (b:ℂ)^2*(F (pairPastCoordinates v P)*(pairPathIncrement true s t P:ℂ)^2)+
        2*(a:ℂ)*b*(F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ))) := by
    funext P
    simp only [pairLinearIncrement,ContinuousMap.coe_mk,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  have hadd := integral_add ((hx.const_mul ((a:ℂ)^2)).add (hy.const_mul ((b:ℂ)^2)))
      (hxy.const_mul (2*(a:ℂ)*b))
  simp only [Pi.add_apply] at hadd
  rw [hid,hadd,
    integral_add (hx.const_mul ((a:ℂ)^2)) (hy.const_mul ((b:ℂ)^2)),integral_const_mul,integral_const_mul,integral_const_mul,
    normalJointPast_complex_second μ c h v s t hv hst ht false,
    normalJointPast_complex_second μ c h v s t hv hst ht true]
  push_cast
  ring

lemma normalJointPast_linear_absolute_third_bound
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (s t : unitInterval) (hst : s < t) (ht : (t:ℝ) < 1) (a b : ℝ) :
    Integrable (fun P => |pairLinearIncrement a b s t P|^3) μ ∧
    (∫ P, |pairLinearIncrement a b s t P|^3 ∂μ) ≤
      8*(|a|+|b|)^3*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment := by
  have hx := normalJointPast_integrable_abs_pow μ c h s t hst ht false 3
  have hy := normalJointPast_integrable_abs_pow μ c h s t hst ht true 3
  have hi := (hx.add hy).const_mul (4*(|a|+|b|)^3)
  have hb : ∀ P, |pairLinearIncrement a b s t P|^3 ≤
      4*(|a|+|b|)^3*(|pairPathIncrement false s t P|^3+|pairPathIncrement true s t P|^3) := by
    intro P
    exact abs_linear_cube_bound a b _ _
  have hI : Integrable (fun P => |pairLinearIncrement a b s t P|^3) μ := hi.mono (by fun_prop)
    (by filter_upwards [] with P
        change ‖|(pairLinearIncrement a b s t) P|^3‖ ≤
          ‖4*(|a|+|b|)^3*(|pairPathIncrement false s t P|^3+|pairPathIncrement true s t P|^3)‖
        simp only [norm_pow,Real.norm_eq_abs,abs_abs]
        exact (hb P).trans (le_abs_self _))
  refine ⟨hI,?_⟩
  calc
    _ ≤ ∫ P, 4*(|a|+|b|)^3*(|pairPathIncrement false s t P|^3+|pairPathIncrement true s t P|^3) ∂μ :=
      integral_mono hI hi hb
    _ = _ := by
      rw [integral_const_mul,integral_add hx hy,
        normalJointPast_absolute_third_moment μ c h s t hst ht false,
        normalJointPast_absolute_third_moment μ c h s t hst ht true]
      ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma pairPastTest_integrable {q : ℕ} (μ : Measure RealPathPair) [IsFiniteMeasure μ]
    (v : Fin q → unitInterval) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    Integrable (fun P => F (pairPastCoordinates v P)) μ := by
  apply Integrable.of_bound (by fun_prop) ‖F‖
  filter_upwards [] with P
  exact F.norm_coe_le_norm _

lemma pairPastPhase_integrable {q : ℕ} (μ : Measure RealPathPair) [IsFiniteMeasure μ]
    (v : Fin q → unitInterval) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) (s t : unitInterval) :
    Integrable (fun P => F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P)) μ := by
  apply Integrable.of_bound (by unfold charPhase; fun_prop) ‖F‖
  filter_upwards [] with P
  rw [norm_mul,charPhase_norm,mul_one]
  exact F.norm_coe_le_norm _

lemma normalJointPast_integral_quadratic {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    (∫ P, F (pairPastCoordinates v P)*(1+(pairLinearIncrement a b s t P:ℂ)*Complex.I-
      (pairLinearIncrement a b s t P:ℂ)^2/2) ∂μ)=
    (1-(((c:ℝ)*((t:ℝ)-s)*(a^2+b^2)/2:ℝ):ℂ))*(∫ P, F (pairPastCoordinates v P) ∂μ)-
    (a:ℂ)*b*(∫ P, F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ) := by
  have h0 := pairPastTest_integrable μ v F
  have h1 := normalJointPast_linear_mean_integrable μ c h v s t hst ht F a b
  have h2 := normalJointPast_linear_second_integrable μ c h v s t hst ht F a b
  have hid : (fun P => F (pairPastCoordinates v P)*(1+(pairLinearIncrement a b s t P:ℂ)*Complex.I-
      (pairLinearIncrement a b s t P:ℂ)^2/2))=
      (fun P => F (pairPastCoordinates v P)+
        Complex.I*(F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ))-
        (1/2:ℂ)*(F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2)) := by
    funext P; ring
  have hadd := integral_sub (h0.add (h1.const_mul Complex.I)) (h2.const_mul (1/2:ℂ))
  simp only [Pi.add_apply] at hadd
  rw [hid,hadd,integral_add h0 (h1.const_mul Complex.I),integral_const_mul,integral_const_mul,
    normalJointPast_linear_mean μ c h v s t hv hst ht F a b,
    normalJointPast_linear_second μ c h v s t hv hst ht F a b]
  push_cast
  ring

lemma normalJointPast_taylor_error {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      ((1-(((c:ℝ)*((t:ℝ)-s)*(a^2+b^2)/2:ℝ):ℂ))*(∫ P, F (pairPastCoordinates v P) ∂μ)-
      (a:ℂ)*b*(∫ P, F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ))‖ ≤
      8*charTaylorConstant*‖F‖*(|a|+|b|)^3*
        (Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment := by
  have h0 := pairPastTest_integrable μ v F
  have h1 := normalJointPast_linear_mean_integrable μ c h v s t hst ht F a b
  have h2 := normalJointPast_linear_second_integrable μ c h v s t hst ht F a b
  have hchar := pairPastPhase_integrable μ v F a b s t
  have hQ : Integrable (fun P => F (pairPastCoordinates v P)*(1+(pairLinearIncrement a b s t P:ℂ)*Complex.I-
      (pairLinearIncrement a b s t P:ℂ)^2/2)) μ := by
    have hid : (fun P => F (pairPastCoordinates v P)*(1+(pairLinearIncrement a b s t P:ℂ)*Complex.I-
      (pairLinearIncrement a b s t P:ℂ)^2/2))=
      (fun P => F (pairPastCoordinates v P)+
        Complex.I*(F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ))-
        (1/2:ℂ)*(F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2)) := by
      funext P; ring
    rw [hid]
    exact (h0.add (h1.const_mul Complex.I)).sub (h2.const_mul (1/2:ℂ))
  rw [← normalJointPast_integral_quadratic μ c h v s t hv hst ht F a b,← integral_sub hchar hQ]
  have h3 := normalJointPast_linear_absolute_third_bound μ c h s t hst ht a b
  have hb : ∀ P, ‖F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P)-
      F (pairPastCoordinates v P)*(1+(pairLinearIncrement a b s t P:ℂ)*Complex.I-
      (pairLinearIncrement a b s t P:ℂ)^2/2)‖ ≤
      ‖F‖*charTaylorConstant*|pairLinearIncrement a b s t P|^3 := by
    intro P
    rw [← mul_sub,norm_mul]
    exact (mul_le_mul (F.norm_coe_le_norm _) (charPhase_quadratic_error _) (norm_nonneg _) (norm_nonneg F)).trans_eq (by ring)
  calc
    _ ≤ ∫ P, ‖F‖*charTaylorConstant*|pairLinearIncrement a b s t P|^3 ∂μ :=
      norm_integral_le_of_norm_le (h3.1.const_mul _) (ae_of_all _ hb)
    _ = ‖F‖*charTaylorConstant*(∫ P, |pairLinearIncrement a b s t P|^3 ∂μ) := integral_const_mul _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left h3.2 (mul_nonneg (norm_nonneg F) charTaylorConstant_nonneg)
      nlinarith only [hh]

end DirectionalTransience

end

end

end OAI
