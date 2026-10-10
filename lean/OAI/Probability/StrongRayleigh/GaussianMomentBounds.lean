import Mathlib

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem336AdditiveD139.GaussianMomentBounds

def standardThirdAbsMoment : ℝ := ∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 1

lemma standardThirdAbsMoment_nonneg : 0 ≤ standardThirdAbsMoment := by
  exact integral_nonneg fun x => pow_nonneg (abs_nonneg x) 3

lemma integral_sq_gaussianReal (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at h
  simpa only [integral_id_gaussianReal, sub_zero] using h

lemma integral_abs_gaussianReal_le (v : ℝ≥0) :
    (∫ x : ℝ, |x| ∂gaussianReal 0 v) ≤ Real.sqrt v := by
  have hLp : MemLp (fun x : ℝ => |x|) 2 (gaussianReal 0 v) := by
    simpa only [Real.norm_eq_abs, id_eq] using
      (memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by norm_num)).norm
  have hv := variance_nonneg (fun x : ℝ => |x|) (gaussianReal 0 v)
  rw [variance_eq_sub hLp] at hv
  have hs : (∫ x : ℝ, |x| ^ 2 ∂gaussianReal 0 v) = v := by
    simpa only [sq_abs] using integral_sq_gaussianReal v
  change 0 ≤ (∫ x : ℝ, |x| ^ 2 ∂gaussianReal 0 v) -
    (∫ x : ℝ, |x| ∂gaussianReal 0 v) ^ 2 at hv
  rw [hs] at hv
  exact (Real.le_sqrt (by positivity) (by positivity)).2 (by linarith)

lemma gaussianReal_map_sqrt (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp [Real.sq_sqrt v.coe_nonneg]

lemma integral_abs_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, |x| ^ n ∂gaussianReal 0 v) =
      Real.sqrt v ^ n * (∫ x : ℝ, |x| ^ n ∂gaussianReal 0 1) := by
  rw [← gaussianReal_map_sqrt v, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [integral_const_mul]

lemma integral_abs_cube_gaussianReal (v : ℝ≥0) :
    (∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 v) =
      standardThirdAbsMoment * (v : ℝ) * Real.sqrt v := by
  rw [integral_abs_pow_gaussianReal]
  change Real.sqrt v ^ 3 * standardThirdAbsMoment = _
  rw [pow_succ, Real.sq_sqrt v.coe_nonneg]
  ring

lemma integrable_abs_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) (gaussianReal 0 v) := by
  simpa only [Real.norm_eq_abs, id_eq] using
    (memLp_id_gaussianReal' (μ := 0) (v := v) n (by simp)).integrable_norm_pow'

section RandomVariable

variable {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Q : Ω → ℝ}
  {v : ℝ≥0}

lemma integral_eq_zero_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, Q ω ∂P) = 0 := by
  simpa using hQ.integral_eq

lemma integral_sq_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, Q ω ^ 2 ∂P) = v := by
  calc
    _ = ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v :=
      hQ.integral_comp (by fun_prop)
    _ = v := integral_sq_gaussianReal v

lemma integral_abs_le_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, |Q ω| ∂P) ≤ Real.sqrt v := by
  calc
    _ = ∫ x : ℝ, |x| ∂gaussianReal 0 v :=
      hQ.integral_comp (by fun_prop)
    _ ≤ Real.sqrt v := integral_abs_gaussianReal_le v

lemma integral_abs_cube_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, |Q ω| ^ 3 ∂P) = standardThirdAbsMoment * (v : ℝ) * Real.sqrt v := by
  calc
    _ = ∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 v :=
      hQ.integral_comp (by fun_prop)
    _ = _ := integral_abs_cube_gaussianReal v

lemma integrable_abs_pow_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) (n : ℕ) :
    Integrable (fun ω => |Q ω| ^ n) P := by
  have hi := integrable_abs_pow_gaussianReal v n
  rw [← hQ.map_eq] at hi
  exact (integrable_map_measure (by fun_prop) hQ.aemeasurable).mp hi

lemma integrable_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) : Integrable Q P := by
  have hi := integrable_abs_pow_of_hasLaw hQ 1
  simpa only [pow_one, ← Real.norm_eq_abs, integrable_norm_iff hQ.aemeasurable.aestronglyMeasurable]
    using hi

lemma integrable_sq_of_hasLaw (hQ : HasLaw Q (gaussianReal 0 v) P) :
    Integrable (fun ω => Q ω ^ 2) P := by
  simpa only [sq_abs] using integrable_abs_pow_of_hasLaw hQ 2

end RandomVariable

section Conditional

variable {Ω : Type u_2} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {mQ mH : MeasurableSpace Ω} {Q : Ω → ℝ} {v : ℝ≥0}

lemma conditional_gaussian_moments
    (hQ : HasLaw Q (gaussianReal 0 v) P)
    (hleQ : mQ ≤ mΩ) (hleH : mH ≤ mΩ)
    (hmQ : StronglyMeasurable[mQ] Q) (hind : Indep mQ mH P) :
    (P[Q | mH] =ᵐ[P] fun _ => (0 : ℝ)) ∧
    (P[fun ω => Q ω ^ 2 | mH] =ᵐ[P] fun _ => (v : ℝ)) ∧
    (∀ᵐ ω ∂P, P[fun ω => |Q ω| | mH] ω ≤ Real.sqrt v) ∧
    (P[fun ω => |Q ω| ^ 3 | mH] =ᵐ[P]
      fun _ => standardThirdAbsMoment * (v : ℝ) * Real.sqrt v) := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  have hmean := condExp_indep_eq hleQ hleH hmQ hind
  have hsq := condExp_indep_eq hleQ hleH (hmQ.pow 2) hind
  have hmabs : StronglyMeasurable[mQ] (fun ω => |Q ω|) := by
    simpa only [Real.norm_eq_abs] using hmQ.norm
  have habs := condExp_indep_eq hleQ hleH hmabs hind
  have hcube := condExp_indep_eq hleQ hleH (hmabs.pow 3) hind
  change P[fun ω => Q ω ^ 2 | mH] =ᵐ[P]
    (fun _ => ∫ ω, Q ω ^ 2 ∂P) at hsq
  change P[fun ω => |Q ω| ^ 3 | mH] =ᵐ[P]
    (fun _ => ∫ ω, |Q ω| ^ 3 ∂P) at hcube
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [integral_eq_zero_of_hasLaw hQ] using hmean
  · simpa only [integral_sq_of_hasLaw hQ] using hsq
  · filter_upwards [habs] with ω hω
    exact hω.le.trans (integral_abs_le_of_hasLaw hQ)
  · simpa only [integral_abs_cube_of_hasLaw hQ] using hcube

end Conditional

end Problem336AdditiveD139.GaussianMomentBounds

end

end OAI
