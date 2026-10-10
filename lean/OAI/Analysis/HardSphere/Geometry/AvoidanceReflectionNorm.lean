import Mathlib
import OAI.Analysis.HardSphere.Operators.FreeTransition

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open Wiener
open scoped ComplexConjugate

lemma avoidance_reflection_norm (N : ℕ) (L : Length) (a t : ℝ) (f : FreePathL2 N L t) :
    ‖(2:ℂ) • avoidanceMultiplier N L a t f-f‖≤‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub ((2:ℂ) • avoidanceMultiplier N L a t f) f,
    Lp.coeFn_smul (2:ℂ) (avoidanceMultiplier N L a t f),
    avoidanceMultiplier_ae N L a t f] with ω hsub hsmul hf
  rw [hsub,Pi.sub_apply,hsmul,Pi.smul_apply,hf]
  by_cases h : ω∈staysAllowed N L a
  · simp only [Set.indicator_of_mem h,smul_eq_mul]
    convert le_refl ‖f ω‖ using 1
    congr 1
    ring
  · simp only [Set.indicator_of_notMem h,smul_zero,zero_sub,norm_neg,le_refl]

lemma free_deficit_le_twice_killed (N : ℕ) (L : Length) (a t : ℝ) (f : ScalarL2 N L) :
    ‖f‖^2-(inner ℂ f (freeTransition N L t f)).re ≤
      2*(‖f‖^2-(inner ℂ f (killedTransition N L a t f)).re) := by
  have h := re_inner_le_norm (𝕜 := ℂ) (endpointPull N L t 0 f)
    ((2:ℂ) • avoidanceMultiplier N L a t (endpointPull N L t 1 f)-endpointPull N L t 1 f)
  have hb := avoidance_reflection_norm N L a t (endpointPull N L t 1 f)
  have hn0 := (endpointPull N L t 0).norm_map f
  have hn1 := (endpointPull N L t 1).norm_map f
  have hi0 : inner ℂ (endpointPull N L t 0 f) (endpointPull N L t 1 f) =
      inner ℂ f (freeTransition N L t f) := by
    rw [freeTransition,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
    rfl
  have hi1 : inner ℂ (endpointPull N L t 0 f)
      (avoidanceMultiplier N L a t (endpointPull N L t 1 f)) =
        inner ℂ f (killedTransition N L a t f) := by
    rw [killedTransition,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right]
    rfl
  rw [inner_sub_right,inner_smul_right,hi0,hi1] at h
  change (2 * inner ℂ f (killedTransition N L a t f)-inner ℂ f (freeTransition N L t f)).re≤_ at h
  rw [Complex.sub_re,Complex.mul_re] at h
  norm_num at h
  simp only [LinearIsometry.norm_map] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (norm_nonneg f)
  nlinarith

end HardSphere

end

end OAI
