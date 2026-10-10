import OAI.Analysis.CircleDomains.Probability.MeasureFamilyModulusBasic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

namespace OAI

/-! An admissible bounded continuous real function bounds the pointwise
modulus through its actual L² norm. Absolute values preserve admissibility. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ]

lemma boundedContinuous_integral_sq_eq_norm_sq (f : Z →ᵇ ℝ) :
    (∫ z, f z ^ 2 ∂σ) = ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ ^ 2 := by
  let F : Lp ℝ 2 σ := BoundedContinuousFunction.toLp 2 σ ℝ f
  have he : F =ᵐ[σ] f := BoundedContinuousFunction.coeFn_toLp 2 σ ℝ f
  calc
    (∫ z, f z ^ 2 ∂σ) = ∫ z, (F z)^2 ∂σ := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      rw [hz]
    _ = inner ℝ F F := by
      rw [L2.inner_def]
      simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    _ = ‖F‖^2 := real_inner_self_eq_norm_sq _

lemma measureFamilyModulus_le_boundedContinuous_norm {A : Type*}
    (K : A → FiniteMeasure Z) (f : Z →ᵇ ℝ)
    (ha : ∀ a, 1 ≤ ∫ z, f z ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤
      ENNReal.ofReal (‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ ^ 2) := by
  let h : Z → ℝ≥0∞ := fun z => ENNReal.ofReal |f z|
  have hh : Measurable h := by
    simpa only [Real.norm_eq_abs] using f.continuous.norm.measurable.ennreal_ofReal
  have hb (a : A) : 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z) := by
    have hfi : Integrable f (K a : Measure Z) := f.integrable (μ := (K a : Measure Z))
    have hn : Integrable (fun z => |f z|) (K a : Measure Z) := by
      simpa only [Real.norm_eq_abs] using hfi.norm
    have hi : 1 ≤ ∫ z, |f z| ∂(K a : Measure Z) :=
      (ha a).trans (integral_mono hfi hn (fun z => le_abs_self (f z)))
    rw [← ofReal_integral_eq_lintegral_ofReal hn (Eventually.of_forall (fun z => abs_nonneg (f z)))]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hi
  have he : (∫⁻ z, h z ^ 2 ∂σ) =
      ENNReal.ofReal (‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ ^ 2) := by
    have hsq : (fun z => h z^2) = fun z => ENNReal.ofReal (f z^2) := by
      funext z
      simp only [h,← ENNReal.ofReal_pow (abs_nonneg _) 2,sq_abs]
    rw [hsq,← ofReal_integral_eq_lintegral_ofReal]
    · rw [boundedContinuous_integral_sq_eq_norm_sq σ f]
    · convert (f*f).integrable (μ := σ) using 1
      ext z
      simp only [pow_two,BoundedContinuousFunction.mul_apply]
    · exact Eventually.of_forall (fun z => sq_nonneg (f z))
  exact he ▸ measureFamilyModulus_le_admissible σ K hh hb

end CircleDomainRigidity

end

end OAI
