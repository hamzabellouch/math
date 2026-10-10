import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDuhamel
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! # The strong initial derivative of the actual Duhamel term

Continuity of the forcing suffices at the initial time. This is the
bounded-perturbation part of the generator of the constructed evolution.
-/

open Filter Set MeasureTheory Topology

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

theorem hasDerivAt_zero_smul_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E) (hA : ContinuousAt A 0) :
    HasDerivAt (fun t => t • A t) (A 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply (hA.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  simp only [zero_add, zero_smul, sub_zero, inv_smul_smul₀ ht0]

theorem hasDerivAt_homogeneousDuhamel_zero (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (r : ℝ → HomogeneousY a k) (hr : Continuous r) :
    HasDerivAt (fun t => homogeneousDuhamel a b k ha ha1 hk t r) (r 0) 0 := by
  let A : ℝ → HomogeneousY a k := fun t =>
    ∫ u in Icc (0 : ℝ) 1,
      homogeneousFreeOperator a b k (t - t * u) ha ha1 hk (r (t * u))
  have hc : Continuous (fun p : ℝ × ℝ =>
      homogeneousFreeOperator a b k (p.1 - p.1 * p.2) ha ha1 hk (r (p.1 * p.2))) :=
    (continuous_homogeneousFreeOperator_uncurry a b k ha ha1 hk).comp
      ((continuous_fst.sub (continuous_fst.mul continuous_snd)).prodMk
        (hr.comp (continuous_fst.mul continuous_snd)))
  have hA : Continuous A :=
    continuous_parametric_integral_of_continuous hc isCompact_Icc
  have hA0 : A 0 = r 0 := by
    simp only [A, zero_mul, sub_zero, homogeneousFreeOperator_zero,
      setIntegral_const, Real.volume_real_Icc_of_le zero_le_one, sub_zero, one_smul]
  have hf : (fun t => t • A t) =
      (fun t => homogeneousDuhamel a b k ha ha1 hk t r) := by
    funext t
    exact (homogeneousDuhamel_eq_unitIntegral a b k ha ha1 hk t r).symm
  have h := hasDerivAt_zero_smul_continuous A hA.continuousAt
  rw [hf, hA0] at h
  exact h

end DefocusingNLS

end OAI
