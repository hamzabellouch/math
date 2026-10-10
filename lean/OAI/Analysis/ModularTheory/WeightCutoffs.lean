import OAI.Analysis.ModularTheory.FourierCompression

namespace OAI

/-! Actual finite vector functionals for the modular-core weight construction.
The frequency cutoff is exp(πt) on [-n,n], with the sign fixed by the
Fourier convention in `ModularFourierTranslation`. These are positive
functionals, not yet an assertion of a tracial or semifinite limit. -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

def modularWeightCutoffFunction (n : ℕ) : ℝ → ℂ :=
  (Icc (-(n : ℝ)) n).indicator (fun t => (Real.exp (Real.pi * t) : ℂ))

lemma modularWeightCutoff_memLp (n : ℕ) :
    MemLp (modularWeightCutoffFunction n) 2 (volume : Measure ℝ) := by
  apply (memLp_indicator_iff_restrict measurableSet_Icc).mpr
  apply MemLp.of_bound (by fun_prop) (Real.exp (Real.pi * n))
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro t ht
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le)

def modularWeightCutoffVector (n : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (modularWeightCutoff_memLp n).toLp (modularWeightCutoffFunction n)

lemma modularWeightCutoffVector_ae (n : ℕ) :
    modularWeightCutoffVector n =ᵐ[volume] modularWeightCutoffFunction n :=
  MemLp.coeFn_toLp _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

def modularCoreWeightVector (n : ℕ) : Lp H 2 (volume : Measure ℝ) :=
  modularFourierInclusion S (modularWeightCutoffVector n)

def modularCoreCutoffFunctional (n : ℕ) :
    (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) →ₚ[ℂ] ℂ where
  toFun T := inner ℂ (modularCoreWeightVector S n) (T (modularCoreWeightVector S n))
  map_add' T U := by simp only [add_apply, inner_add_right]
  map_smul' c T := by
    simp only [smul_apply, inner_smul_right, RingHom.id_apply, smul_eq_mul]
  monotone' := by
    intro T U hTU
    have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (sub_nonneg.mpr hTU)).inner_nonneg_right (modularCoreWeightVector S n)
    simpa only [sub_apply, inner_sub_right, sub_nonneg] using hp

lemma modularCoreCutoffFunctional_compression (n : ℕ)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    modularCoreCutoffFunctional S n T =
      inner ℂ (modularWeightCutoffVector n)
        (modularFourierCompression S T (modularWeightCutoffVector n)) := by
  change inner ℂ (modularFourierInclusion S (modularWeightCutoffVector n))
      (T (modularFourierInclusion S (modularWeightCutoffVector n))) =
    inner ℂ (modularWeightCutoffVector n)
      ((modularFourierInclusion S).toContinuousLinearMap.adjoint
        (T (modularFourierInclusion S (modularWeightCutoffVector n))))
  exact (ContinuousLinearMap.adjoint_inner_right
    (modularFourierInclusion S).toContinuousLinearMap (modularWeightCutoffVector n)
    (T (modularFourierInclusion S (modularWeightCutoffVector n)))).symm

@[simp] lemma modularCoreCutoffFunctional_one (n : ℕ) :
    modularCoreCutoffFunctional S n 1 = (‖modularWeightCutoffVector n‖ ^ 2 : ℝ) := by
  rw [modularCoreCutoffFunctional_compression, modularFourierCompression_one,
    one_apply_eq_self, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma modularCoreCutoffFunctional_monomial (n : ℕ) (T : H →L[ℂ] H) (s : ℝ) :
    modularCoreCutoffFunctional S n
      (modularLpRepresentation volume S.D T *
        (modularLpTranslateEquiv (H := H) volume s :
          Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))) =
      inner ℂ S.xi (T S.xi) *
        inner ℂ (modularWeightCutoffVector n)
          (modularDual volume (-2 * Real.pi * s) (modularWeightCutoffVector n)) := by
  rw [modularCoreCutoffFunctional_compression,
    modularFourierCompression_coefficient_translate, smul_apply, inner_smul_right]
  rfl

lemma modularCoreCutoffFunctional_bound (n : ℕ)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    ‖modularCoreCutoffFunctional S n T‖ ≤ ‖modularWeightCutoffVector n‖ ^ 2 * ‖T‖ := by
  have hn : ‖modularCoreWeightVector S n‖ = ‖modularWeightCutoffVector n‖ :=
    (modularFourierInclusion S).norm_map _
  calc
    _ ≤ ‖modularCoreWeightVector S n‖ * ‖T (modularCoreWeightVector S n)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖modularCoreWeightVector S n‖ * (‖T‖ * ‖modularCoreWeightVector S n‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = ‖modularWeightCutoffVector n‖ ^ 2 * ‖T‖ := by rw [hn]; ring

end WeakPureInfiniteness

end

end OAI
