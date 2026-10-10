import Mathlib
import OAI.Analysis.BrownMeasure.FunctionalCalculus

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal
namespace FiniteFactor
local instance : Module ℝ ProductOp := Module.complexToReal ProductOp
local instance : IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

lemma sourceLog_measurable (θ : SourceCoordinate → ℝ) (c : SourceCoordinate → ℝ) (k : ℤ) :
    Measurable (sourceLog θ c k) := by
  have he : sourceLog θ c k = fun x=> -Real.log (sourceCocycle θ c k x) := by
    funext x
    simp [sourceCocycle]
  rw [he]
  exact (Real.measurable_log.comp (sourceCocycle_measurable θ c k)).neg

lemma sourceWeight_cfc (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (φ : C(ℝ,ℝ)) :
    cfc φ (sourcePi θ (sourceWeightBase θ hθ))=
      sourceContinuousWeight θ (φ.restrict WeightInterval) := by
  have he := congrArg (fun H : C(WeightInterval,ℝ) →⋆ₐ[ℝ] ProductOp=>H (φ.restrict WeightInterval))
    (sourceContinuousWeightHom_eq_cfc θ hθ)
  rw [cfcHomSuperset_apply] at he
  rw [cfc_apply φ _ (sourceWeight_positive θ hθ).isSelfAdjoint φ.continuous.continuousOn]
  exact he.symm

lemma logarithmCutoff_exp_neg (n : ℕ) (x : ℝ) : logarithmCutoff n (Real.exp (-x))= -min (n:ℝ) x := by
  change Real.log (max (Real.exp (-(n:ℝ))) (Real.exp (-x)))= -min (n:ℝ) x
  by_cases h : (n:ℝ)≤x
  · rw [min_eq_left h,max_eq_left (Real.exp_le_exp.mpr (neg_le_neg h)),Real.log_exp]
  · have h' := le_of_not_ge h
    rw [min_eq_right h',max_eq_right (Real.exp_le_exp.mpr (neg_le_neg h')),Real.log_exp]

lemma sourceLog_trunc_integrable (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℕ) :
    Integrable (fun x=>min (n:ℝ) (sourceLog θ sourceLogWeight 1 x)) sourceBaseMeasure := by
  apply Integrable.of_bound ((measurable_const.min (sourceLog_measurable _ _ _)).aestronglyMeasurable) (n:ℝ)
  filter_upwards [sourceSamplingHaar_cube] with x hx
  rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg n) (sourceLog_nonneg θ hθ hx))]
  exact min_le_left _ _

lemma sourceDeterminant_trace_logCutoff (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℕ) :
    (sourceVacuumFunctional (cfc (logarithmCutoff n)
      (CFC.abs (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)))).re =
      -(∫ x,min (n:ℝ) (sourceLog θ sourceLogWeight 1 x) ∂sourceBaseMeasure) := by
  rw [sourceOperator_abs θ hθ,sourceWeight_cfc θ hθ]
  change (sourceVacuumFunctional (sourcePi θ (sourceContinuousWeightBase θ ((logarithmCutoff n).restrict WeightInterval)))).re=_
  rw [sourcePi_trace]
  have he : (fun x=>(sourceContinuousWeightBase θ ((logarithmCutoff n).restrict WeightInterval)).toFun x)=ᵐ[sourceBaseMeasure]
      fun x=>(-min (n:ℝ) (sourceLog θ sourceLogWeight 1 x):ℝ) := by
    filter_upwards [sourceSamplingHaar_cube] with x hx
    change (logarithmCutoff n (sourceWeightPoint θ x):ℂ)=((-min (n:ℝ) (sourceLog θ sourceLogWeight 1 x):ℝ):ℂ)
    rw [sourceWeightPoint_val θ hθ hx]
    exact congrArg Complex.ofReal (logarithmCutoff_exp_neg n (sourceLog θ sourceLogWeight 1 x))
  rw [integral_congr_ae he,integral_complex_ofReal,Complex.ofReal_re,integral_neg]

lemma sourceLog_trunc_antibounded (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (a : ℝ) :
    ∃ n : ℕ,a≤∫ x,min (n:ℝ) (sourceLog θ sourceLogWeight 1 x) ∂sourceBaseMeasure := by
  let f : ℕ → (SourceCoordinate → ℝ) → ℝ≥0∞ := fun n x=> ENNReal.ofReal (min (n:ℝ) (sourceLog θ sourceLogWeight 1 x))
  have hmeas (n) : Measurable (f n) := ENNReal.measurable_ofReal.comp (measurable_const.min (sourceLog_measurable _ _ _))
  have hmono : Monotone f := by
    intro n m hnm x
    apply ENNReal.ofReal_le_ofReal
    exact min_le_min_right _ (by exact_mod_cast hnm)
  have hs : (⨆ n,∫⁻ x,f n x ∂sourceBaseMeasure)=∞ := by
    rw [← lintegral_iSup hmeas hmono]
    have he (x) : (⨆ n,f n x)=ENNReal.ofReal (sourceLog θ sourceLogWeight 1 x) := by
      apply le_antisymm
      · exact iSup_le (fun n=>ENNReal.ofReal_le_ofReal (min_le_right _ _))
      · obtain ⟨n,hn⟩ := exists_nat_ge (sourceLog θ sourceLogWeight 1 x)
        exact le_iSup_of_le n (by dsimp [f]; rw [min_eq_right hn])
    simp_rw [he]
    exact sourceLog_lintegral_top θ hθ
  by_contra hn
  have hb : ∀ n,∫⁻ x,f n x ∂sourceBaseMeasure≤ENNReal.ofReal a := by
    intro n
    have hnn : ∀ᵐ x ∂sourceBaseMeasure,0 ≤ min (n:ℝ) (sourceLog θ sourceLogWeight 1 x) := by
      filter_upwards [sourceSamplingHaar_cube] with x hx
      exact le_min (Nat.cast_nonneg n) (sourceLog_nonneg θ hθ hx)
    rw [← ofReal_integral_eq_lintegral_ofReal (sourceLog_trunc_integrable θ hθ n) hnn]
    exact ENNReal.ofReal_le_ofReal (le_of_lt (not_le.mp (fun h=>hn ⟨n,h⟩)))
  have := iSup_le hb
  rw [hs] at this
  exact ENNReal.ofReal_ne_top (top_le_iff.mp this)

theorem sourceOperator_determinant_zero (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    FugledeKadisonDeterminant sourceVacuumFunctional
      (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)=0 := by
  let Δ := FugledeKadisonDeterminant sourceVacuumFunctional
    (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)
  have hb (k : ℕ) : Δ≤ENNReal.ofReal (Real.exp (-(k:ℝ))) := by
    obtain ⟨n,hn⟩ := sourceLog_trunc_antibounded θ hθ (k:ℝ)
    apply (iInf_le _ n).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact (sourceDeterminant_trace_logCutoff θ hθ n).trans_le (neg_le_neg hn)
  have ht : Tendsto (fun k:ℕ=>ENNReal.ofReal (Real.exp (-(k:ℝ)))) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp he
  exact le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) bot_le
end FiniteFactor
end

end OAI
