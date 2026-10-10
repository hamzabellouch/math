import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace ZeroTemperatureSK.WeakIto

def normalThirdMoment : ℝ := ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1

lemma gaussian_abs_pow_integrable (p : ℕ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => |x|^p) (gaussianReal 0 v) := by
  simpa only [id_eq, Real.norm_eq_abs] using
    (memLp_id_gaussianReal (μ := 0) (v := v) p).integrable_norm_pow'

lemma normalThirdMoment_nonneg : 0 ≤ normalThirdMoment :=
  integral_nonneg (fun x => pow_nonneg (abs_nonneg x) 3)

lemma gaussian_abs_pow (p : ℕ) (v : ℝ≥0) :
    (∫ x : ℝ, |x|^p ∂gaussianReal 0 v) =
      (Real.sqrt (v : ℝ))^p * ∫ x : ℝ, |x|^p ∂gaussianReal 0 1 := by
  have hs : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (v:ℝ)*x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt v.coe_nonneg]
  rw [← hs, integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  exact integral_const_mul _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma increment_abs_cube (hB : IsPreBrownianReal B P) (s h : ℝ≥0) :
    (∫ ω, |B (s+h) ω - B s ω|^3 ∂P) = (h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment := by
  have he := (hB.hasLaw_sub (s+h) s).integral_comp
    (f := fun x : ℝ => |x|^3) ((continuous_abs.pow 3).measurable.aestronglyMeasurable)
  change (∫ ω, |B (s+h) ω - B s ω|^3 ∂P) = _ at he
  rw [he, gaussian_abs_pow]
  have hd : nndist ((s+h : ℝ≥0):ℝ) (s:ℝ) = h := by
    ext
    rw [coe_nndist, Real.dist_eq]
    rw [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg h.coe_nonneg]
  change Real.sqrt ((nndist ((s+h : ℝ≥0):ℝ) (s:ℝ) : ℝ≥0):ℝ)^3 *
    normalThirdMoment = _
  rw [hd]
  rw [pow_succ, Real.sq_sqrt h.coe_nonneg]

end ZeroTemperatureSK.WeakIto

end

end OAI
