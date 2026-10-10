import OAI.Analysis.ModularTheory.WeightMonotone
import OAI.Analysis.ModularTheory.CoreSeparation
import OAI.Analysis.OperatorAlgebra.ScalarLpLocalizedFunctions
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace OAI

/-! The actual modular cutoff vectors separate squares in the core. This
proves faithfulness of the proposed weight, without presupposing its
traciality or semifiniteness. -/

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology ENNReal

namespace WeakPureInfiniteness

def modularWeightCutoffInverse (n : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ => (Real.exp (-Real.pi * max (-(n : ℝ)) t) : ℂ))
    (by fun_prop) (Real.exp (Real.pi * n)) (by
      intro t
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h := le_max_left (-(n : ℝ)) t
      nlinarith [Real.pi_pos])

lemma modularWeightCutoffInverse_cancel (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (-(n : ℝ)) n) :
    modularWeightCutoffInverse n t * (Real.exp (Real.pi * t) : ℂ) = 1 := by
  change (Real.exp (-Real.pi * max (-(n : ℝ)) t) : ℂ) *
    (Real.exp (Real.pi * t) : ℂ) = 1
  rw [max_eq_right ht.1, ← Complex.ofReal_mul, ← Real.exp_add]
  simp

lemma modularWeightCutoffInverse_apply (n : ℕ) (f : BoundedContinuousFunction ℝ ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    scalarLpRepresentation volume (f * modularWeightCutoffInverse n)
        (modularWeightCutoffVector n) =
      scalarIntervalProjection n (hf.toLp f) := by
  apply Lp.ext
  filter_upwards [scalarLpMultiplier_ae volume (f * modularWeightCutoffInverse n)
      (modularWeightCutoffVector n), modularWeightCutoffVector_ae n,
    scalarIntervalProjection_ae n (hf.toLp f), MemLp.coeFn_toLp hf] with t h₁ h₂ h₃ h₄
  change (scalarLpRepresentation volume (f * modularWeightCutoffInverse n)
    (modularWeightCutoffVector n)) t =
    (f * modularWeightCutoffInverse n) t * modularWeightCutoffVector n t at h₁
  rw [h₁, h₃]
  by_cases ht : t ∈ Icc (-(n : ℝ)) n
  · rw [indicator_of_mem ht, h₄, h₂]
    change (f t * modularWeightCutoffInverse n t) *
      (Icc (-(n : ℝ)) n).indicator (fun t => (Real.exp (Real.pi * t) : ℂ)) t = f t
    rw [indicator_of_mem ht, mul_assoc, modularWeightCutoffInverse_cancel n ht, mul_one]
  · rw [indicator_of_notMem ht, h₂]
    change _ * (Icc (-(n : ℝ)) n).indicator (fun t => (Real.exp (Real.pi * t) : ℂ)) t = 0
    rw [indicator_of_notMem ht, mul_zero]

lemma scalarLp_eq_zero_of_weightCutoffs
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hc : ∀ s, Commute T
      (modularDualUnitary (H := ℂ) volume s : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume))
    (hz : ∀ n, T (modularWeightCutoffVector n) = 0) : T = 0 := by
  have hfzero (f : BoundedContinuousFunction ℝ ℂ) (hf : MemLp f 2 (volume : Measure ℝ)) :
      T (hf.toLp f) = 0 := by
    have hcut (n : ℕ) : T (scalarIntervalProjection n (hf.toLp f)) = 0 := by
      rw [← modularWeightCutoffInverse_apply n f hf]
      have h := congrArg (fun R : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
          Lp ℂ 2 (volume : Measure ℝ) => R (modularWeightCutoffVector n))
        (scalarLp_commute_continuousMultiplier T hc (f * modularWeightCutoffInverse n)).eq
      change T (scalarLpRepresentation volume (f * modularWeightCutoffInverse n)
        (modularWeightCutoffVector n)) =
        scalarLpRepresentation volume (f * modularWeightCutoffInverse n)
          (T (modularWeightCutoffVector n)) at h
      rw [h, hz, map_zero]
    exact tendsto_nhds_unique
      (T.continuous.continuousAt.tendsto.comp (scalarIntervalProjection_strong (hf.toLp f)))
      (by simpa only [Function.comp_def, hcut] using
        tendsto_const_nhds (x := (0 : Lp ℂ 2 (volume : Measure ℝ))))
  apply ContinuousLinearMap.ext
  intro g
  change T g = 0
  refine (Lp.boundedContinuousFunction_dense ℂ (volume : Measure ℝ)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).induction ?_
      (isClosed_eq T.continuous continuous_const) g
  intro f hf
  obtain ⟨b, hb⟩ := Lp.mem_boundedContinuousFunction_iff.mp hf
  have hbf : (f : ℝ → ℂ) =ᵐ[volume] b := by
    have h := b.toContinuousMap.coeFn_toAEEqFun (volume : Measure ℝ)
    rw [hb] at h
    exact h
  have hbLp : MemLp b 2 (volume : Measure ℝ) := MemLp.ae_eq hbf (Lp.memLp f)
  have he : hbLp.toLp b = f := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp hbLp).trans hbf.symm
  rw [← he]
  exact hfzero b hbLp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

/-- Faithfulness for squares follows from the concrete cutoff functionals. -/
theorem modularCoreCutoffs_faithful_square
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (hz : ∀ n, modularCoreCutoffFunctional S n (star T * T) = 0) : T = 0 := by
  have hvec (n : ℕ) : T (modularCoreWeightVector S n) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    have h := hz n
    change inner ℂ (modularCoreWeightVector S n)
      (star T (T (modularCoreWeightVector S n))) = 0 at h
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right] at h
    exact h
  have hx : modularFourierCompression S (star T * T) = 0 := by
    apply scalarLp_eq_zero_of_weightCutoffs
    · exact modularFourierCompression_commutes S _ (mul_mem (star_mem hT) hT)
    · intro n
      change (modularFourierInclusion S).toContinuousLinearMap.adjoint
        (star T (T (modularFourierInclusion S (modularWeightCutoffVector n)))) = 0
      change (modularFourierInclusion S).toContinuousLinearMap.adjoint
        (star T (T (modularCoreWeightVector S n))) = 0
      rw [hvec, map_zero, map_zero]
  apply modularScalarCompression_faithful_square (volume : Measure ℝ) S T hT
  rw [modularFourierCompression_conjugate] at hx
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).conjStarAlgEquiv.injective (hx.trans (map_zero _).symm)

end WeakPureInfiniteness

end

end OAI
