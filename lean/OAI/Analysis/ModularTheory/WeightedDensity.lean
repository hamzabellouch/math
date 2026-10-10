import OAI.Analysis.ModularTheory.WeightMonomials
import OAI.Analysis.ModularTheory.WeightFaithful

namespace OAI

/-! Removing the scalar exponential weight by bounded inverse cutoffs. This
approximates ordinary L2 vectors by the actual finite-weight test functions. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPureInfiniteness

private def inverseWeightFactor (n : ℕ) (t : ℝ) : ℂ :=
  modularWeightCutoffInverse n t * (Real.exp (Real.pi * t) : ℂ)

private lemma inverseWeightFactor_bound (n : ℕ) (t : ℝ) :
    ‖inverseWeightFactor n t‖ ≤ 1 := by
  change ‖(Real.exp (-Real.pi * max (-(n : ℝ)) t) : ℂ) *
    (Real.exp (Real.pi * t) : ℂ)‖ ≤ 1
  rw [← Complex.ofReal_mul, ← Real.exp_add, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have hm := le_max_right (-(n : ℝ)) t
  nlinarith [Real.pi_pos]

private lemma inverseWeightFactor_tendsto (t : ℝ) :
    Tendsto (fun n => inverseWeightFactor n t) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have htn : |t| ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
  exact (modularWeightCutoffInverse_cancel n (abs_le.mp htn)).symm

private def inverseWeightVector (f : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  boundedVectorLp volume (inverseWeightFactor n) (by
    unfold inverseWeightFactor
    fun_prop) 1 (inverseWeightFactor_bound n) f

lemma modularWeightedInverse_integrable (f : BoundedContinuousFunction ℝ ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (n : ℕ) :
    Integrable (fun ω : ℝ => ‖(f * modularWeightCutoffInverse n) ω‖ ^ 2 *
      Real.exp (2 * Real.pi * ω)) := by
  have he : modularWeightedFunction (f * modularWeightCutoffInverse n) =ᵐ[volume]
      (inverseWeightVector (hf.toLp f) n : ℝ → ℂ) := by
    dsimp only [inverseWeightVector]
    filter_upwards [boundedVectorLp_ae volume (inverseWeightFactor n) (by
      unfold inverseWeightFactor
      fun_prop) 1 (inverseWeightFactor_bound n) (hf.toLp f),
      MemLp.coeFn_toLp hf] with t hv hf'
    rw [hv, hf']
    change (f t * modularWeightCutoffInverse n t) * (Real.exp (Real.pi * t) : ℂ) =
      inverseWeightFactor n t * f t
    unfold inverseWeightFactor
    ring
  have hm : MemLp (modularWeightedFunction (f * modularWeightCutoffInverse n)) 2
      (volume : Measure ℝ) := (memLp_congr_ae he).mpr (Lp.memLp _)
  simpa only [modularWeightedFunction_norm_sq] using
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

lemma modularWeightedInverse_tendsto (f : BoundedContinuousFunction ℝ ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    Tendsto (fun n => modularWeightedVector (f * modularWeightCutoffInverse n)
      (modularWeightedInverse_integrable f hf n)) atTop (𝓝 (hf.toLp f)) := by
  have he (n : ℕ) : modularWeightedVector (f * modularWeightCutoffInverse n)
      (modularWeightedInverse_integrable f hf n) = inverseWeightVector (hf.toLp f) n := by
    apply Lp.ext
    dsimp only [inverseWeightVector]
    filter_upwards [modularWeightedVector_ae (f * modularWeightCutoffInverse n)
      (modularWeightedInverse_integrable f hf n),
      boundedVectorLp_ae volume (inverseWeightFactor n) (by
        unfold inverseWeightFactor
        fun_prop) 1 (inverseWeightFactor_bound n) (hf.toLp f),
      MemLp.coeFn_toLp hf] with t hg hv hf'
    rw [hg, hv, hf']
    change (f t * modularWeightCutoffInverse n t) * (Real.exp (Real.pi * t) : ℂ) =
      inverseWeightFactor n t * f t
    unfold inverseWeightFactor
    ring
  simp_rw [he]
  have h := boundedVectorLp_strong inverseWeightFactor (fun _ => (1 : ℂ))
    (fun n => by unfold inverseWeightFactor; fun_prop) (by fun_prop) 1 zero_le_one
    inverseWeightFactor_bound (by simp) inverseWeightFactor_tendsto (hf.toLp f)
  have hi : boundedVectorLp volume (fun _ => (1 : ℂ)) (by fun_prop) 1 (by simp)
      (hf.toLp f) = hf.toLp f := by
    apply Lp.ext
    filter_upwards [boundedVectorLp_ae volume (fun _ => (1 : ℂ)) (by fun_prop)
      1 (by simp) (hf.toLp f)] with t ht
    simpa only [one_smul] using ht
  simpa only [inverseWeightVector, hi] using h

end WeakPureInfiniteness

end

end OAI
