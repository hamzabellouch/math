import Mathlib
import OAI.Probability.Ballisticity.Estimates.JointPastMoments

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def nearDiagonalCutoff (ρ : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun z => max 0 (min 1 (2-|z|/ρ)),by fun_prop⟩ 2
    (fun x y => by
      rw [Real.dist_eq]
      change |max 0 (min 1 (2-|x|/ρ))-max 0 (min 1 (2-|y|/ρ))| ≤ 2
      have hx0 : 0 ≤ max 0 (min 1 (2-|x|/ρ)) := le_max_left _ _
      have hy0 : 0 ≤ max 0 (min 1 (2-|y|/ρ)) := le_max_left _ _
      have hx1 : max 0 (min 1 (2-|x|/ρ)) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
      have hy1 : max 0 (min 1 (2-|y|/ρ)) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
      exact abs_le.mpr ⟨by linarith,by linarith⟩)

lemma nearDiagonalCutoff_unit (ρ z : ℝ) : 0 ≤ nearDiagonalCutoff ρ z ∧ nearDiagonalCutoff ρ z ≤ 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

lemma nearDiagonalCutoff_one {ρ : ℝ} (hρ : 0 < ρ) {z : ℝ} (hz : |z| ≤ ρ) :
    nearDiagonalCutoff ρ z=1 := by
  change max 0 (min 1 (2-|z|/ρ))=1
  have h := (div_le_one hρ).mpr hz
  rw [min_eq_left (by linarith),max_eq_right (by norm_num)]

lemma nearDiagonalCutoff_zero {ρ : ℝ} (hρ : 0 < ρ) {z : ℝ} (hz : 2*ρ ≤ |z|) :
    nearDiagonalCutoff ρ z=0 := by
  change max 0 (min 1 (2-|z|/ρ))=0
  have h := (le_div_iff₀ hρ).mpr hz
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

lemma nearDiagonalCutoff_uc (ρ : ℝ) : UniformContinuous (nearDiagonalCutoff ρ) := by
  have hh := (LipschitzWith.const (0:ℝ)).max ((LipschitzWith.const (1:ℝ)).min
    ((LipschitzWith.const (2:ℝ)).sub ((lipschitzWith_smul (ρ⁻¹)).comp
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)))))
  change UniformContinuous (fun z : ℝ => max 0 (min 1 (2-|z|/ρ)))
  simpa only [Function.comp_def,smul_eq_mul,Real.norm_eq_abs,mul_comm,div_eq_mul_inv] using hh.uniformContinuous

noncomputable def farDiagonalCutoff (ρ : ℝ) : ℝ →ᵇ ℝ := .const ℝ 1-nearDiagonalCutoff ρ

lemma farDiagonalCutoff_unit (ρ z : ℝ) : 0 ≤ farDiagonalCutoff ρ z ∧ farDiagonalCutoff ρ z ≤ 1 := by
  have h := nearDiagonalCutoff_unit ρ z
  change 0 ≤ 1-nearDiagonalCutoff ρ z ∧ 1-nearDiagonalCutoff ρ z ≤ 1
  constructor <;> linarith

lemma farDiagonalCutoff_uc (ρ : ℝ) : UniformContinuous (farDiagonalCutoff ρ) :=
  uniformContinuous_const.sub (nearDiagonalCutoff_uc ρ)

lemma farDiagonalCutoff_zero {ρ : ℝ} (hρ : 0 < ρ) {z : ℝ} (hz : |z| ≤ ρ) :
    farDiagonalCutoff ρ z=0 := by
  change 1-nearDiagonalCutoff ρ z=0
  rw [nearDiagonalCutoff_one hρ hz]; ring

noncomputable def currentGapTest {q : ℕ} (g : ℝ →ᵇ ℝ) : (Fin (q+1) → ℝ × ℝ) →ᵇ ℝ :=
  g.compContinuous ⟨fun z => (z 0).1-(z 0).2,by fun_prop⟩

lemma normalJointPast_gap_second (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (g : ℝ →ᵇ ℝ) :
    (∫ P, g (P.1 s-P.2 s)*(pairPathIncrement b s t P)^2 ∂μ)=
      (∫ P, g (P.1 s-P.2 s) ∂μ)*((c:ℝ)*((t:ℝ)-s)) := by
  simpa [currentGapTest,pairPastCoordinates] using
    normalJointPast_second μ c h (fun _ : Fin 1 => s) s t (fun _ => le_rfl) hst ht b (currentGapTest (q := 0) g)

lemma abs_mul_le_half_squares (x y : ℝ) : |x*y| ≤ (x^2+y^2)/2 := by
  rw [abs_mul]
  nlinarith [sq_abs x,sq_abs y,sq_nonneg (|x|-|y|)]

lemma normalJointPast_cross_integrable (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) :
    Integrable (fun P => pairPathIncrement false s t P*pairPathIncrement true s t P) μ := by
  have hx := normalJointPast_integrable_abs_pow μ c h s t hst ht false 2
  have hy := normalJointPast_integrable_abs_pow μ c h s t hst ht true 2
  simp only [sq_abs] at hx hy
  apply ((hx.add hy).div_const 2).mono (by fun_prop : Measurable
    (fun P => pairPathIncrement false s t P*pairPathIncrement true s t P)).aestronglyMeasurable
  filter_upwards [] with P
  change |pairPathIncrement false s t P*pairPathIncrement true s t P| ≤
    |((pairPathIncrement false s t P)^2+(pairPathIncrement true s t P)^2)/2|
  rw [abs_of_nonneg (by positivity : 0 ≤
    ((pairPathIncrement false s t P)^2+(pairPathIncrement true s t P)^2)/2)]
  exact abs_mul_le_half_squares _ _

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma normalJointPast_weighted_cross_integrable {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ) :
    Integrable (fun P => F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (pairPathIncrement false s t P*pairPathIncrement true s t P)) μ := by
  apply (normalJointPast_cross_integrable μ c h s t hst ht).bdd_mul (by fun_prop)
  filter_upwards [] with P
  exact (norm_mul_le _ _).trans (mul_le_mul (F.norm_coe_le_norm _) (g.norm_coe_le_norm _)
    (norm_nonneg _) (norm_nonneg _))

lemma normalJointPast_weighted_clip_integrable {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (v : Fin q → unitInterval) (s t : unitInterval)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ) :
    Integrable (fun P => F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (symmetricClip 1 (pairPathIncrement false s t P)*symmetricClip 1 (pairPathIncrement true s t P))) μ := by
  apply Integrable.of_bound (by fun_prop) (‖F‖*‖g‖)
  filter_upwards [] with P
  rw [norm_mul,norm_mul,norm_mul]
  have hx : ‖symmetricClip 1 (pairPathIncrement false s t P)‖ ≤ 1 := symmetricClip_bound 1 _
  have hy : ‖symmetricClip 1 (pairPathIncrement true s t P)‖ ≤ 1 := symmetricClip_bound 1 _
  have hc : ‖symmetricClip 1 (pairPathIncrement false s t P)‖*
      ‖symmetricClip 1 (pairPathIncrement true s t P)‖ ≤ 1 := by
    simpa using mul_le_mul hx hy (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hf := mul_le_mul (F.norm_coe_le_norm (pairPastCoordinates v P)) (g.norm_coe_le_norm (P.1 s-P.2 s))
    (norm_nonneg _) (norm_nonneg _)
  simpa using mul_le_mul hf hc (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

lemma normalJointPast_unclip_error {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ)
    (hgb : ∀ z, |g z| ≤ 1) :
    |(∫ P, F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (pairPathIncrement false s t P*pairPathIncrement true s t P) ∂μ)-
      (∫ P, F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (symmetricClip 1 (pairPathIncrement false s t P)*symmetricClip 1 (pairPathIncrement true s t P)) ∂μ)| ≤
      4*‖F‖*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment := by
  let X := pairPathIncrement false s t
  let Y := pairPathIncrement true s t
  have hi := normalJointPast_weighted_cross_integrable μ c h v s t hst ht F g
  have hj := normalJointPast_weighted_clip_integrable μ v s t F g
  have hx := normalJointPast_integrable_abs_pow μ c h s t hst ht false 3
  have hy := normalJointPast_integrable_abs_pow μ c h s t hst ht true 3
  rw [← integral_sub hi hj]
  calc
    _ ≤ ∫ P, |F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)-
        F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(symmetricClip 1 (X P)*symmetricClip 1 (Y P))| ∂μ := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := μ)
        (fun P => F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)-
        F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(symmetricClip 1 (X P)*symmetricClip 1 (Y P))))
    _ ≤ ∫ P, 2*‖F‖*(|X P|^3+|Y P|^3) ∂μ := by
      apply integral_mono (hi.sub hj).norm ((hx.add hy).const_mul (2*‖F‖))
      intro P
      change |F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)-
        F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(symmetricClip 1 (X P)*symmetricClip 1 (Y P))| ≤
          2*‖F‖*(|X P|^3+|Y P|^3)
      rw [← mul_sub,abs_mul,abs_mul]
      have hf : |F (pairPastCoordinates v P)| * |g (P.1 s-P.2 s)| ≤ ‖F‖ := by
        simpa using mul_le_mul (F.norm_coe_le_norm _) (hgb _) (abs_nonneg _) (norm_nonneg _)
      have hh := mul_le_mul hf (unit_clip_product_error (X P) (Y P)) (abs_nonneg _)
        (norm_nonneg F)
      nlinarith only [hh]
    _ = _ := by
      rw [integral_const_mul,integral_add hx hy,
        normalJointPast_absolute_third_moment μ c h s t hst ht false,
        normalJointPast_absolute_third_moment μ c h s t hst ht true]
      ring

end DirectionalTransience

end

end

end OAI
