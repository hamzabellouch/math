import OAI.Analysis.KadisonKastler.GaussianStateAverage
import OAI.Analysis.KadisonKastler.NormContinuousStateAverage
import OAI.Analysis.KadisonKastler.ModularStateAction

namespace OAI

/-! # Probability averages of the implemented modular action

These maps are defined by vector integration. They are contractions and
preserve the reference vector state whenever the implementing group fixes
the reference vector.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

def stateActionAverage (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : H →L[ℂ] H) : H →L[ℂ] H :=
  probabilityOperatorIntegral μ (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)

theorem stateActionAverage_norm_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : H →L[ℂ] H) : ‖stateActionAverage U hU μ a‖ ≤ ‖a‖ :=
  norm_probabilityOperatorIntegral_le μ (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    (norm_nonneg a) (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)

@[simp] theorem stateActionAverage_one (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    stateActionAverage U hU μ (1 : H →L[ℂ] H)=1 := by
  ext x
  change (∫ t, stateActionOrbit U (1 : H →L[ℂ] H) t x ∂μ)=x
  have he (t : ℝ) : stateActionOrbit U (1 : H →L[ℂ] H) t=1 :=
    (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U (Multiplicative.ofAdd t))).map_one
  simp only [he,one_apply_eq_self,integral_const,probReal_univ,one_smul]

def stateActionAverageMap (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := stateActionAverage U hU μ
      map_add' a b := by
        ext x
        change (∫ t, stateActionOrbit U (a+b) t x ∂μ)=
          (∫ t, stateActionOrbit U a t x ∂μ)+(∫ t, stateActionOrbit U b t x ∂μ)
        have he (t : ℝ) : stateActionOrbit U (a+b) t=
            stateActionOrbit U a t+stateActionOrbit U b t := by
          simp only [stateActionOrbit,unitaryConj,mul_add,add_mul]
        simp only [he,add_apply]
        exact integral_add
          (integrable_bounded_operator_vector μ (stateActionOrbit U a)
            (fun y => (stateActionOrbit_continuous U hU a y).aestronglyMeasurable)
            (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) x)
          (integrable_bounded_operator_vector μ (stateActionOrbit U b)
            (fun y => (stateActionOrbit_continuous U hU b y).aestronglyMeasurable)
            (Eventually.of_forall fun t => (stateActionOrbit_norm U b t).le) x)
      map_smul' c a := by
        ext x
        change (∫ t, stateActionOrbit U (c • a) t x ∂μ)=
          c • (∫ t, stateActionOrbit U a t x ∂μ)
        have he (t : ℝ) : stateActionOrbit U (c • a) t=c • stateActionOrbit U a t := by
          simp only [stateActionOrbit,unitaryConj,mul_smul_comm,smul_mul_assoc]
        simp only [he,smul_apply]
        exact integral_smul c _ }
    1 (fun a => by
      change ‖stateActionAverage U hU μ a‖ ≤ 1*‖a‖
      rw [one_mul]
      exact stateActionAverage_norm_le U hU μ a)

theorem stateActionAverage_mem (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : VonNeumannAlgebra H)
    (hnormal : ∀ t a, a ∈ M → stateActionOrbit U a t ∈ M)
    (a : H →L[ℂ] H) (ha : a ∈ M) : stateActionAverage U hU μ a ∈ M :=
  probabilityOperatorIntegral_mem μ (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) M
    (Eventually.of_forall fun t => hnormal t a ha)

theorem stateActionAverage_vectorState (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Ω : H) (hΩ : ∀ t : ℝ, (U (Multiplicative.ofAdd t) : H →L[ℂ] H) Ω=Ω)
    (a : H →L[ℂ] H) :
    productVectorState Ω (stateActionAverage U hU μ a)=productVectorState Ω a := by
  have hi := integrable_bounded_operator_vector μ (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) Ω
  change (innerSL ℂ Ω) (∫ t, stateActionOrbit U a t Ω ∂μ)=productVectorState Ω a
  rw [← (innerSL ℂ Ω).integral_comp_comm hi]
  have he (t : ℝ) : (innerSL ℂ Ω) (stateActionOrbit U a t Ω)=productVectorState Ω a :=
    productVectorState_unitaryConj_of_fixes Ω (U (Multiplicative.ofAdd t)) (hΩ t) a
  simp only [he,integral_const,probReal_univ,one_smul]

end

end KadisonKastler

end OAI
