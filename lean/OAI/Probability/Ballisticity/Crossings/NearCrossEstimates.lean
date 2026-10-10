import Mathlib
import OAI.Probability.Ballisticity.Crossings.PastCutoffs

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma normalJointPast_weighted_square_integrable (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (g : ℝ →ᵇ ℝ) :
    Integrable (fun P => g (P.1 s-P.2 s)*(pairPathIncrement b s t P)^2) μ := by
  have hi := normalJointPast_integrable_abs_pow μ c h s t hst ht b 2
  simp only [sq_abs] at hi
  apply hi.bdd_mul (by fun_prop)
  filter_upwards [] with P
  exact g.norm_coe_le_norm _

lemma normalJointPast_near_cross {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ)
    (hg : ∀ z, 0 ≤ g z) :
    |∫ P, F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (pairPathIncrement false s t P*pairPathIncrement true s t P) ∂μ| ≤
      ‖F‖*((c:ℝ)*((t:ℝ)-s))*(∫ P, g (P.1 s-P.2 s) ∂μ) := by
  let X := pairPathIncrement false s t
  let Y := pairPathIncrement true s t
  have hi := normalJointPast_weighted_cross_integrable μ c h v s t hst ht F g
  have hx := normalJointPast_weighted_square_integrable μ c h s t hst ht false g
  have hy := normalJointPast_weighted_square_integrable μ c h s t hst ht true g
  calc
    _ ≤ ∫ P, |F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)| ∂μ := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := μ)
        (fun P => F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)))
    _ ≤ ∫ P, ‖F‖/2*(g (P.1 s-P.2 s)*(X P)^2+g (P.1 s-P.2 s)*(Y P)^2) ∂μ := by
      apply integral_mono hi.norm ((hx.add hy).const_mul (‖F‖/2))
      intro P
      change |F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)| ≤ _
      rw [abs_mul,abs_mul,abs_of_nonneg (hg _)]
      have hb := mul_le_mul (mul_le_mul_of_nonneg_right (F.norm_coe_le_norm (pairPastCoordinates v P)) (hg (P.1 s-P.2 s)))
        (abs_mul_le_half_squares (X P) (Y P)) (abs_nonneg _) (mul_nonneg (norm_nonneg _) (hg (P.1 s-P.2 s)))
      simp only [Real.norm_eq_abs] at hb
      change |F (pairPastCoordinates v P)| *g (P.1 s-P.2 s)*|X P*Y P| ≤
        ‖F‖/2*(g (P.1 s-P.2 s)*(X P)^2+g (P.1 s-P.2 s)*(Y P)^2)
      nlinarith only [hb]
    _ = _ := by
      rw [integral_const_mul,integral_add hx hy,
        normalJointPast_gap_second μ c h s t hst ht false,
        normalJointPast_gap_second μ c h s t hst ht true]
      ring

def SeparatedCrossBound (μ : Measure RealPathPair) (A K : ℝ) : Prop :=
  ∀ (q : ℕ) (v : Fin q → unitInterval) (s t : unitInterval),
    (∀ z, v z ≤ s) → s < t → (t:ℝ) < 1 →
    ∀ (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ), UniformContinuous g →
      (∀ z, |g z| ≤ 1) → ∀ ρ : ℝ, 0 < ρ → (∀ z, |z| ≤ ρ → g z=0) →
    |∫ P, F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (symmetricClip 1 (pairPathIncrement false s t P)*symmetricClip 1 (pairPathIncrement true s t P)) ∂μ| ≤
      ‖F‖*(K*Real.exp (-A*ρ^2/((t:ℝ)-s)))

lemma normalJointPast_cross_bound {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) {A K : ℝ} (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    |∫ P, F (pairPastCoordinates v P)*
      (pairPathIncrement false s t P*pairPathIncrement true s t P) ∂μ| ≤
      ‖F‖*(K*Real.exp (-A*ρ^2/((t:ℝ)-s))+
        4*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment+
        ((c:ℝ)*((t:ℝ)-s))*(∫ P, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ)) := by
  let X := pairPathIncrement false s t
  let Y := pairPathIncrement true s t
  let G := farDiagonalCutoff ρ
  let N := nearDiagonalCutoff ρ
  have hGb : ∀ z, |G z| ≤ 1 := fun z => by
    rw [abs_of_nonneg (farDiagonalCutoff_unit ρ z).1]
    exact (farDiagonalCutoff_unit ρ z).2
  have hfar := hcross q v s t hv hst ht F G (farDiagonalCutoff_uc ρ) hGb ρ hρ
    (fun _ hz => farDiagonalCutoff_zero hρ hz)
  have he := normalJointPast_unclip_error μ c h v s t hst ht F G hGb
  have hn := normalJointPast_near_cross μ c h v s t hst ht F N (fun z => (nearDiagonalCutoff_unit ρ z).1)
  have hI := normalJointPast_weighted_cross_integrable μ c h v s t hst ht F G
  have hJ := normalJointPast_weighted_cross_integrable μ c h v s t hst ht F N
  have hid : (∫ P, F (pairPastCoordinates v P)*(X P*Y P) ∂μ)=
      (∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*(X P*Y P) ∂μ)+
      (∫ P, F (pairPastCoordinates v P)*N (P.1 s-P.2 s)*(X P*Y P) ∂μ) := by
    rw [← integral_add hI hJ]
    congr 1
    funext P
    change _ = F (pairPastCoordinates v P)*(1-N (P.1 s-P.2 s))*(X P*Y P)+_
    ring
  change |∫ P, F (pairPastCoordinates v P)*(X P*Y P) ∂μ| ≤ _
  rw [hid]
  have hab := abs_add_le
    (∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*(X P*Y P) ∂μ)
    (∫ P, F (pairPastCoordinates v P)*N (P.1 s-P.2 s)*(X P*Y P) ∂μ)
  have hf : |∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*(X P*Y P) ∂μ| ≤
      4*‖F‖*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment+
      ‖F‖*(K*Real.exp (-A*ρ^2/((t:ℝ)-s))) := by
    have hh := abs_add_le
      ((∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*(X P*Y P) ∂μ)-
      (∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*
        (symmetricClip 1 (X P)*symmetricClip 1 (Y P)) ∂μ))
      (∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*
        (symmetricClip 1 (X P)*symmetricClip 1 (Y P)) ∂μ)
    rw [sub_add_cancel] at hh
    exact hh.trans (add_le_add he hfar)
  nlinarith only [hab,hf,hn]

end DirectionalTransience

end

end

end OAI
