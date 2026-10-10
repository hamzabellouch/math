import OAI.Analysis.ModularTheory.WeightGNS
import OAI.Analysis.ModularTheory.TranslationWeight
import OAI.Analysis.OperatorAlgebra.VectorLpStrongConvergence

namespace OAI

/-! Exact finite-weight vectors for translation multipliers. Their frequency
function is the multiplier times exp(πt), with the normalization fixed by the
actual regular representation. These are the starting vectors for the
Tomita symmetry calculation on normal-ordered core elements. -/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology ENNReal

namespace WeakPureInfiniteness

def modularWeightedFunction (g : BoundedContinuousFunction ℝ ℂ) (t : ℝ) : ℂ :=
  g t * (Real.exp (Real.pi * t) : ℂ)

lemma modularWeightedFunction_norm_sq (g : BoundedContinuousFunction ℝ ℂ) (t : ℝ) :
    ‖modularWeightedFunction g t‖ ^ 2 = ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t) := by
  rw [modularWeightedFunction, norm_mul, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_nat_mul]
  congr 2
  norm_num
  ring

lemma modularWeightedFunction_memLp (g : BoundedContinuousFunction ℝ ℂ)
    (hi : Integrable (fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t))) :
    MemLp (modularWeightedFunction g) 2 (volume : Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq_norm (by
    unfold modularWeightedFunction
    exact (g.continuous.mul (by fun_prop)).aestronglyMeasurable)).mpr
  simpa only [modularWeightedFunction_norm_sq] using hi

def modularWeightedVector (g : BoundedContinuousFunction ℝ ℂ)
    (hi : Integrable (fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t))) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (modularWeightedFunction_memLp g hi).toLp (modularWeightedFunction g)

lemma modularWeightedVector_ae (g : BoundedContinuousFunction ℝ ℂ)
    (hi : Integrable (fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t))) :
    modularWeightedVector g hi =ᵐ[volume] modularWeightedFunction g := MemLp.coeFn_toLp _

lemma modularWeightedVector_cutoff (g : BoundedContinuousFunction ℝ ℂ)
    (hi : Integrable (fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t))) (n : ℕ) :
    scalarLpRepresentation volume g (modularWeightCutoffVector n) =
      scalarIntervalProjection n (modularWeightedVector g hi) := by
  apply Lp.ext
  filter_upwards [scalarLpMultiplier_ae volume g (modularWeightCutoffVector n),
    modularWeightCutoffVector_ae n,
    scalarIntervalProjection_ae n (modularWeightedVector g hi),
    modularWeightedVector_ae g hi] with t hg hn hp hv
  change (scalarLpMultiplier volume g (modularWeightCutoffVector n)) t = _
  rw [hg, hn, hp]
  by_cases ht : t ∈ Set.Icc (-(n : ℝ)) n
  · rw [modularWeightCutoffFunction, Set.indicator_of_mem ht,
      Set.indicator_of_mem ht, hv]
    rfl
  · rw [modularWeightCutoffFunction, Set.indicator_of_notMem ht,
      Set.indicator_of_notMem ht, mul_zero]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

lemma modularTranslationCalculus_finite
    (g : BoundedContinuousFunction ℝ ℂ)
    (hi : Integrable (fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t))) :
    modularCoreSquareWeight S (modularTranslationCalculus g) < ⊤ :=
  (modularTranslationCalculus_weight_le S g hi).trans_lt ENNReal.ofReal_lt_top

lemma modularTranslationCalculus_weightVector
    (g : BoundedContinuousFunction ℝ ℂ)
    (hi : Integrable (fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t))) :
    modularWeightVector S (modularTranslationCalculus g)
        (modularTranslationCalculus_mem S g) (modularTranslationCalculus_finite S g hi) =
      modularFourierInclusion S (modularWeightedVector g hi) := by
  apply tendsto_nhds_unique (modularWeightVector_tendsto S _ _ _)
  have h := (modularFourierInclusion S).continuous.continuousAt.tendsto.comp
    (scalarIntervalProjection_strong (modularWeightedVector g hi))
  simpa only [Function.comp_def, ← modularWeightedVector_cutoff,
    ← modularTranslationCalculus_fourierInclusion, modularCoreWeightVector] using h

lemma modularTranslationCalculus_weight_exact
    (g : BoundedContinuousFunction ℝ ℂ)
    (hi : Integrable (fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t))) :
    (modularCoreSquareWeight S (modularTranslationCalculus g)).toReal =
      ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t) := by
  rw [← modularWeightVector_norm_sq S _ (modularTranslationCalculus_mem S g)
    (modularTranslationCalculus_finite S g hi),
    modularTranslationCalculus_weightVector S g hi, (modularFourierInclusion S).norm_map,
    scalarLp_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [modularWeightedVector_ae g hi] with t ht
  rw [ht, modularWeightedFunction_norm_sq]

lemma modularCoefficient_scalar_norm_sq (a : H →L[ℂ] H)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖modularLpRepresentation volume S.D a (modularScalarInclusion volume S f)‖ ^ 2 =
      ‖a S.xi‖ ^ 2 * ‖f‖ ^ 2 := by
  rw [vectorLp_norm_sq_integral, scalarLp_norm_sq_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [modularLpRepresentation_ae volume S.D a
    (modularScalarInclusion volume S f), modularScalarInclusion_ae volume S f]
    with t ha hf
  rw [ha, hf, map_smul, S.fixes_xi, map_smul, S.D.norm_unitary_apply,
    norm_smul, mul_pow]
  ring

lemma modularNormalOrdered_weight_exact (a : S.M.toStarSubalgebra)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hi : Integrable (fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t))) :
    (modularCoreSquareWeight S
      (modularLpRepresentation volume S.D (a : H →L[ℂ] H) *
        modularTranslationCalculus g)).toReal =
      ‖(a : H →L[ℂ] H) S.xi‖ ^ 2 *
        ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t) := by
  let R := modularLpRepresentation volume S.D (a : H →L[ℂ] H)
  have hR : R ∈ modularCrossedProduct volume S := modularCrossedProduct_coeff volume S a
  have hg := modularTranslationCalculus_mem S g
  have hfin := modularTranslationCalculus_finite S g hi
  rw [← modularWeightVector_norm_sq S _ (mul_mem hR hg)
    (modularCoreSquareWeight_mul_finite S _ hfin R),
    modularWeightVector_mul S _ hg hfin R hR,
    modularTranslationCalculus_weightVector S g hi]
  change ‖modularLpRepresentation volume S.D (a : H →L[ℂ] H)
    (modularScalarInclusion volume S (𝓕⁻ (modularWeightedVector g hi)))‖ ^ 2 = _
  have hn : ‖𝓕⁻ (modularWeightedVector g hi)‖ = ‖modularWeightedVector g hi‖ :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map _
  rw [modularCoefficient_scalar_norm_sq, hn, scalarLp_norm_sq_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [modularWeightedVector_ae g hi] with t ht
  rw [ht, modularWeightedFunction_norm_sq]

end WeakPureInfiniteness

end

end OAI
