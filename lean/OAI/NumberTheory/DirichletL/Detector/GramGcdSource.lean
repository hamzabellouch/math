import OAI.NumberTheory.DirichletL.Detector.GramFrequency
import OAI.NumberTheory.DirichletL.Detector.LowGramPoisson

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma gcd_generator_left (I J : SupportedIdeal) :
    primaryGenerator I.val=primaryGenerator (gcdCommon I J).val*primaryGenerator (gcdLeft I J).val := by
  rw [←primaryGenerator_mul,gcd_common_left]

lemma gcd_generator_right (I J : SupportedIdeal) :
    primaryGenerator J.val=primaryGenerator (gcdCommon I J).val*primaryGenerator (gcdRight I J).val := by
  rw [←primaryGenerator_mul,gcd_common_right]

lemma gcd_generator_coprime (I J : SupportedIdeal) :
    IsCoprime (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).1,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).1]
  exact gcd_residual_coprime I J

theorem actual_gcd_lift (I J : SupportedIdeal) (k : O) :
    let C:=primaryGenerator (gcdCommon I J).val
    let n₁:=primaryGenerator (gcdLeft I J).val
    let n₂:=primaryGenerator (gcdRight I J).val
    actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)=
      idealRowHom k (gcdLeft I J).val*star (idealRowHom (-k) (gcdRight I J).val)*
        sexticReciprocityPhase n₁ n₂*
          actualCommon C ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property) n₁ n₂ k := by
  dsimp only
  have h₁ := (supported_span_primaryGenerator_iff _).mpr (gcdLeft I J).property
  have h₂ := (supported_span_primaryGenerator_iff _).mpr (gcdRight I J).property
  have hp₁ : ConcretePrimeRowBridge.goodLambda^2∣primaryGenerator (gcdLeft I J).val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).2
  have hp₂ : ConcretePrimeRowBridge.goodLambda^2∣primaryGenerator (gcdRight I J).val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).2
  have hh := actual_common_lift (primaryGenerator (gcdCommon I J).val)
    (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val) k
    ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property) h₁ h₂ hp₁ hp₂
    (gcd_generator_coprime I J)
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).1,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).1] using hh

theorem actual_gcd_frequency_source (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    (∑'h : O,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (-h)*
      paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      ∑'k : O,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (primaryGenerator (gcdCommon I J).val*k)*
        paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator (gcdCommon I J).val*k)‖^2/
          ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  have hneg := (Equiv.neg O).tsum_eq (fun h : O=>
    actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) h*
      paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simp only [Equiv.neg_apply,map_neg,norm_neg] at hneg
  rw [hneg]
  have hh := actual_common_frequency_tsum (primaryGenerator (gcdCommon I J).val)
    (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val)
    ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdLeft I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdRight I J).property)
    (fun h=>paperRadialFourier U (Q*‖eisEmbedding h‖^2/
      ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J] using hh

end SevenEighths.ProbeGramCommon
end

end OAI
