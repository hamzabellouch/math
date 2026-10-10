import Mathlib
import OAI.Probability.Ballisticity.Estimates.NormalLinearPast

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma charPhase_continuous : Continuous charPhase := by unfold charPhase; fun_prop

noncomputable def phaseAugmentedTimes {q : ℕ} (v : Fin q → unitInterval) (s u : unitInterval) :
    Fin (q+2) → unitInterval := Fin.cons u (Fin.cons s v)

noncomputable def phaseAugmentedTest {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    (Fin (q+2) → ℝ × ℝ) →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => F (fun i => z i.succ.succ)*
      charPhase (a*((z 0).1-(z 1).1)+b*((z 0).2-(z 1).2)),by
        apply Continuous.mul (F.continuous.comp (by fun_prop))
        exact charPhase_continuous.comp (by fun_prop)⟩ (2*‖F‖) (by
      intro x y
      calc
        _ ≤ ‖F (fun i => x i.succ.succ)*charPhase (a*((x 0).1-(x 1).1)+b*((x 0).2-(x 1).2))‖+
          ‖F (fun i => y i.succ.succ)*charPhase (a*((y 0).1-(y 1).1)+b*((y 0).2-(y 1).2))‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
        _ ≤ _ := by
          rw [norm_mul,norm_mul,charPhase_norm,charPhase_norm,mul_one,mul_one]
          nlinarith only [F.norm_coe_le_norm (fun i => x i.succ.succ),F.norm_coe_le_norm (fun i => y i.succ.succ)])

lemma phaseAugmentedTest_norm {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    ‖phaseAugmentedTest F a b‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro z
  change ‖F (fun i => z i.succ.succ)*charPhase _‖ ≤ ‖F‖
  rw [norm_mul,charPhase_norm,mul_one]
  exact F.norm_coe_le_norm _

lemma phaseAugmentedTest_eval {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ)
    (v : Fin q → unitInterval) (s u : unitInterval) (P : RealPathPair) :
    phaseAugmentedTest F a b (pairPastCoordinates (phaseAugmentedTimes v s u) P)=
      F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s u P) := by
  simp [phaseAugmentedTest,phaseAugmentedTimes,pairPastCoordinates,pairLinearIncrement,
    pairPathIncrement,Fin.cons_zero,Fin.cons_succ]

lemma phaseAugmentedTimes_le {q : ℕ} (v : Fin q → unitInterval) (s u : unitInterval)
    (hv : ∀ z,v z ≤ s) (hsu : s ≤ u) : ∀ z,phaseAugmentedTimes v s u z ≤ u := by
  intro z
  refine Fin.cases ?_ (fun z => ?_) z
  · exact le_rfl
  · refine Fin.cases ?_ (fun z => ?_) z
    · exact hsu
    · exact (hv z).trans hsu

lemma pairLinearIncrement_add (a b : ℝ) (s u t : unitInterval) (P : RealPathPair) :
    pairLinearIncrement a b s u P+pairLinearIncrement a b u t P=pairLinearIncrement a b s t P := by
  simp only [pairLinearIncrement,pairPathIncrement,ContinuousMap.coe_mk,Bool.false_eq_true,
    ↓reduceIte]
  ring

lemma phaseAugmentedTest_mul {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ)
    (v : Fin q → unitInterval) (s u t : unitInterval) (P : RealPathPair) :
    phaseAugmentedTest F a b (pairPastCoordinates (phaseAugmentedTimes v s u) P)*
      charPhase (pairLinearIncrement a b u t P)=
      F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) := by
  rw [phaseAugmentedTest_eval,mul_assoc,← charPhase_add,pairLinearIncrement_add]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def jointTaylorCoeff (a b : ℝ) : ℝ :=
  8*charTaylorConstant*(|a|+|b|)^3*normalThirdMoment+8*|a*b| *normalThirdMoment

lemma jointTaylorCoeff_nonneg (a b : ℝ) : 0 ≤ jointTaylorCoeff a b := by
  have hT := charTaylorConstant_nonneg
  have hM := normalThirdMoment_nonneg
  unfold jointTaylorCoeff
  positivity

lemma normalJointPast_phase_step {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    {A K : ℝ} (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      (1-(((c:ℝ)*((t:ℝ)-s)*(a^2+b^2)/2:ℝ):ℂ))*(∫ P, F (pairPastCoordinates v P) ∂μ)‖ ≤
      ‖F‖*(2*|a*b| *K*Real.exp (-A*ρ^2/((t:ℝ)-s))+
        jointTaylorCoeff a b*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3+
        2*|a*b| *(c:ℝ)*((t:ℝ)-s)*(∫ P, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ)) := by
  have htay := normalJointPast_taylor_error μ c h v s t hv hst ht F a b
  have hcr := normalJointPast_complex_cross_bound μ c h hK hcross v s t hv hst ht F hρ
  let Z := ∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ
  let W := (1-(((c:ℝ)*((t:ℝ)-s)*(a^2+b^2)/2:ℝ):ℂ))*(∫ P, F (pairPastCoordinates v P) ∂μ)
  let Q := ∫ P, F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ
  have hid : Z-W=(Z-(W-(a:ℂ)*b*Q))-(a:ℂ)*b*Q := by ring
  change ‖Z-W‖ ≤ _
  rw [hid]
  have hn := norm_sub_le (Z-(W-(a:ℂ)*b*Q)) ((a:ℂ)*b*Q)
  have hm : ‖(a:ℂ)*b*Q‖=|a*b| *‖Q‖ := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  rw [hm] at hn
  have hcr' := mul_le_mul_of_nonneg_left hcr (abs_nonneg (a*b))
  change ‖Z-(W-(a:ℂ)*b*Q)‖ ≤ _ at htay
  change |a*b| *‖Q‖ ≤ _ at hcr'
  unfold jointTaylorCoeff
  nlinarith only [hn,htay,hcr']

lemma normalJointPast_cumulative_phase_step {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    {A K : ℝ} (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s u t : unitInterval) (hv : ∀ z, v z ≤ s) (hsu : s ≤ u)
    (hut : u < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      (1-(((c:ℝ)*((t:ℝ)-u)*(a^2+b^2)/2:ℝ):ℂ))*
      (∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s u P) ∂μ)‖ ≤
      ‖F‖*(2*|a*b| *K*Real.exp (-A*ρ^2/((t:ℝ)-u))+
        jointTaylorCoeff a b*(Real.sqrt ((c:ℝ)*((t:ℝ)-u)))^3+
        2*|a*b| *(c:ℝ)*((t:ℝ)-u)*(∫ P, nearDiagonalCutoff ρ (P.1 u-P.2 u) ∂μ)) := by
  have hh := normalJointPast_phase_step μ c h hK hcross (phaseAugmentedTimes v s u) u t
    (phaseAugmentedTimes_le v s u hv hsu) hut ht (phaseAugmentedTest F a b) a b hρ
  simp only [phaseAugmentedTest_eval,mul_assoc,← charPhase_add,pairLinearIncrement_add] at hh
  have hpos : 0 ≤ 2*|a*b| *K*Real.exp (-A*ρ^2/((t:ℝ)-u))+
        jointTaylorCoeff a b*(Real.sqrt ((c:ℝ)*((t:ℝ)-u)))^3+
        2*|a*b| *(c:ℝ)*((t:ℝ)-u)*(∫ P : RealPathPair, nearDiagonalCutoff ρ (P.1 u-P.2 u) ∂μ) := by
    have hM := jointTaylorCoeff_nonneg a b
    have hd : 0 ≤ (t:ℝ)-u := sub_nonneg.mpr (show (u:ℝ) ≤ t from hut.le)
    have hi : 0 ≤ ∫ P : RealPathPair, nearDiagonalCutoff ρ (P.1 u-P.2 u) ∂μ :=
      integral_nonneg (fun P => (nearDiagonalCutoff_unit ρ _).1)
    positivity
  simpa only [mul_assoc] using hh.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (phaseAugmentedTest_norm F a b) hpos)

end DirectionalTransience

end

end

end OAI
