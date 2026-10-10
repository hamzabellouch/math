import Mathlib
import OAI.Probability.SKSupport.Moments.StripSquareMoment
import OAI.Probability.SKSupport.Moments.JetFields

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def thirdCurvatureField (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c : ℝ) : TimeField T :=
  (((compactJetField W γ hT0 hT1 3).mul (compactJetField W γ hT0 hT1 3)).add
    (((compactJetField W γ hT0 hT1 1).mul
      ((compactJetField W γ hT0 hT1 2).mul (compactJetField W γ hT0 hT1 2))).const_mul (-12*c))).add
        (((curvatureField W γ hT0 hT1).mul (curvatureField W γ hT0 hT1)).const_mul (6*c^2))

lemma thirdCurvatureField_eq (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c t x : ℝ) :
    (thirdCurvatureField W γ hT0 hT1 c).f t x=
      (compactJet W γ T 3 t x)^2-12*c*compactJet W γ T 1 t x*(compactJet W γ T 2 t x)^2+
        6*c^2*(compactJet W γ T 1 t x)^4 := by
  dsimp only [thirdCurvatureField,curvatureField,TimeField.add,TimeField.mul,TimeField.const_mul,compactJetField]
  ring

lemma secondCurvatureField_generator_eq (W : BrownianSystem Ω) (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (c t x : ℝ) (hc : compactCoeff γ T t=c) :
    (secondCurvatureField W γ hT0 hT1 c).generator (compactDrift W γ T) t x=
      (thirdCurvatureField W γ hT0 hT1 c).f t x := by
  rw [thirdCurvatureField_eq]
  exact secondCurvatureField_generator W γ hT0 hT1 c t x hc

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK

lemma hasDerivAt_of_right_on_Ioo {F G : ℝ → ℝ} {a b t : ℝ}
    (hF : Continuous F) (hG : Continuous G) (ht : t ∈ Ioo a b)
    (hd : ∀ s ∈ Ioo a b, HasDerivWithinAt F (G s) (Ioi s) s) :
    HasDerivAt F (G t) t := by
  have he (s : ℝ) (hs : s ∈ Ioo a b) : F s=(∫ r in a..s, G r)+F a := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs.1.le hF.continuousOn
      (fun r hr => hd r ⟨hr.1,hr.2.trans hs.2⟩) (hG.intervalIntegrable a s)
    linarith
  have hh := (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable a t)
    hG.stronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt).add_const (F a)
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact he s hs

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def stripSecond (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (c : ℝ) : ℝ → ℝ :=
  (secondCurvatureField W γ T.property.1 T.property.2 c).expected (stripDrift W γ T) W

def stripThird (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (c : ℝ) : ℝ → ℝ :=
  (thirdCurvatureField W γ T.property.1 T.property.2 c).expected (stripDrift W γ T) W

lemma stripSecond_continuous (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (c : ℝ) :
    Continuous (stripSecond W γ T c) := TimeField.expected_continuous _ _ _

lemma stripThird_continuous (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) (c : ℝ) :
    Continuous (stripThird W γ T c) := TimeField.expected_continuous _ _ _

lemma curvatureField_expected (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time) :
    (curvatureField W γ T.property.1 T.property.2).expected (stripDrift W γ T) W=stripA W γ T := by
  funext t
  unfold TimeField.expected stripA
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [curvatureField_eq]
  simp only [compactJet,iteratedDeriv_one]

lemma stripA_hasDerivWithinAt_right (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : Time) (s : ℝ≥0) (hs : (s:ℝ) < T) :
    HasDerivWithinAt (stripA W γ T) (stripSecond W γ T (compactCoeff γ T s) s) (Ioi (s:ℝ)) s := by
  have hd := (curvatureField W γ T.property.1 T.property.2).expected_hasDerivWithinAt_right
    (stripDrift W γ T) W s hs (stripDrift_pathDrift_right W γ T s)
  rw [curvatureField_expected] at hd
  convert hd using 1
  unfold stripSecond TimeField.expected
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [Real.toNNReal_coe,stripDrift]
  exact (curvatureField_generator W γ T.property.1 T.property.2 (s:ℝ) _).symm

lemma stripSecond_hasDerivWithinAt_right (W : BrownianSystem Ω) (γ : OrderParameter)
    (T : Time) (c : ℝ) (s : ℝ≥0) (hs : (s:ℝ) < T) (hc : compactCoeff γ T s=c) :
    HasDerivWithinAt (stripSecond W γ T c) (stripThird W γ T c s) (Ioi (s:ℝ)) s := by
  have hd := (secondCurvatureField W γ T.property.1 T.property.2 c).expected_hasDerivWithinAt_right
    (stripDrift W γ T) W s hs (stripDrift_pathDrift_right W γ T s)
  change HasDerivWithinAt (stripSecond W γ T c) _ _ _ at hd
  convert hd using 1
  unfold stripThird TimeField.expected
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [Real.toNNReal_coe,stripDrift]
  exact (secondCurvatureField_generator_eq W γ T.property.1 T.property.2 c (s:ℝ) _ hc).symm

lemma stripA_hasDerivAt_on_constant (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {a b c t : ℝ} (ha : 0 ≤ a) (hbT : b ≤ T) (ht : t ∈ Ioo a b)
    (hc : ∀ s ∈ Ioo a b, compactCoeff γ T s=c) :
    HasDerivAt (stripA W γ T) (stripSecond W γ T c t) t := by
  apply hasDerivAt_of_right_on_Ioo (stripA_continuous W γ T) (stripSecond_continuous W γ T c) ht
  intro s hs
  have hs0 := ha.trans hs.1.le
  have hd := stripA_hasDerivWithinAt_right W γ T (Real.toNNReal s)
    (by rw [Real.coe_toNNReal _ hs0]; exact hs.2.trans_le hbT)
  simpa only [Real.coe_toNNReal _ hs0,hc s hs] using hd

lemma stripSecond_hasDerivAt_on_constant (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    {a b c t : ℝ} (ha : 0 ≤ a) (hbT : b ≤ T) (ht : t ∈ Ioo a b)
    (hc : ∀ s ∈ Ioo a b, compactCoeff γ T s=c) :
    HasDerivAt (stripSecond W γ T c) (stripThird W γ T c t) t := by
  apply hasDerivAt_of_right_on_Ioo (stripSecond_continuous W γ T c) (stripThird_continuous W γ T c) ht
  intro s hs
  have hs0 := ha.trans hs.1.le
  have hd := stripSecond_hasDerivWithinAt_right W γ T c (Real.toNNReal s)
    (by rw [Real.coe_toNNReal _ hs0]; exact hs.2.trans_le hbT)
    (by rw [Real.coe_toNNReal _ hs0];exact hc s hs)
  simpa only [Real.coe_toNNReal _ hs0] using hd

end ZeroTemperatureSK

end
end

end OAI
