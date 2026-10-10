import OAI.Analysis.AncientFlat.Weighted.WeightedRow

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction SchwartzMap
namespace SourceFrozenOrder
open SchwartzTimeScale SourceFrozenCancellation
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma normalized_integrable [CompleteSpace E]
    (K : SchwartzMap V E) (j : ℕ) (α β : ℝ) (hα : 0<α)
    (A : V → ℝ) (hA : Continuous A) (hAr : ∀ y, A y∈Icc α β)
    (r : ℝ) (f : V →ᵇ ℂ) (x : V) :
    Integrable (fun z => f (x-r • z) • atTime K (Module.finrank ℝ V+j) (A (x-r • z)) z) := by
  obtain ⟨B,hiB,_,_,hb⟩ := parameter_envelope K (Module.finrank ℝ V+j) α β hα
  apply (hiB.const_mul ‖f‖).mono'
  · exact ((f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul
      (continuous_variable K _ (fun z => A (x-r • z))
        (hA.comp (continuous_const.sub (continuous_const.smul continuous_id)))
        (fun z => hα.trans_le (hAr _).1))).aestronglyMeasurable
  · filter_upwards with z
    rw [norm_smul]
    exact mul_le_mul (f.norm_coe_le_norm _) (hb _ (hAr _) z) (norm_nonneg _) (norm_nonneg _)
variable [CompleteSpace E]
lemma value_smul_sub (K : SchwartzMap V E) (j : ℕ) (α β : ℝ) (hα : 0<α)
    (A : V → ℝ) (hA : Continuous A) (hAr : ∀ y, A y∈Icc α β)
    (r : ℝ) (hr : 0<r) (f g : V →ᵇ ℂ) (c : ℂ) (x : V) :
    value K A r (c • f-g) j x=c • value K A r f j x-value K A r g j x := by
  rw [normalized K A (fun y => hα.trans_le (hAr y).1) r hr,
    normalized K A (fun y => hα.trans_le (hAr y).1) r hr,
    normalized K A (fun y => hα.trans_le (hAr y).1) r hr]
  simp only [BoundedContinuousFunction.coe_sub,BoundedContinuousFunction.coe_smul,Pi.sub_apply,
    sub_smul,smul_eq_mul,mul_smul]
  have hi : Integrable (fun z => c • (f (x-r • z) • atTime K (Module.finrank ℝ V+j) (A (x-r • z)) z)) := by
    exact (normalized_integrable K j α β hα A hA hAr r f x).smul c
  have he : (fun z => c • f (x-r • z) • atTime K (Module.finrank ℝ V+j) (A (x-r • z)) z) =
      (fun z => c • (f (x-r • z) • atTime K (Module.finrank ℝ V+j) (A (x-r • z)) z)) := rfl
  rw [integral_sub hi (normalized_integrable K j α β hα A hA hAr r g x), integral_smul]
  module
end SourceFrozenOrder

end

end OAI
