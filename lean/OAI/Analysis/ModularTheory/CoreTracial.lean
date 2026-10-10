import OAI.Analysis.ModularTheory.AlgebraicAdjoint
import OAI.Analysis.OperatorAlgebra.BicommutantStrongStar

namespace OAI

/-! Tracial symmetry of the constructed modular-core square weight.
Finite two-vector approximations suffice; no norm-bounded density theorem
or traciality assumption is used. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma core_twoVector_sequence (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (x y : Lp H 2 (volume : Measure ℝ)) :
    ∃ P : ℕ → (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)),
      (∀ n, P n ∈ algebraicModularCore (volume : Measure ℝ) S) ∧
      Tendsto (fun n => P n x) atTop (𝓝 (T x)) ∧
      Tendsto (fun n => star (P n) y) atTop (𝓝 (star T y)) := by
  classical
  rw [← SetLike.mem_coe, modularCrossedProduct_carrier] at hT
  have hex (n : ℕ) := exists_finite_strongStar_approximation
    (algebraicModularCore (volume : Measure ℝ) S) hT
    (fun _ : Unit => x) (fun _ : Unit => y)
    (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
  choose P hP hx hy using hex
  refine ⟨P, hP, ?_, ?_⟩
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (Eventually.of_forall (fun n => (hx n ()).le))
      tendsto_one_div_add_atTop_nhds_zero_nat
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (Eventually.of_forall (fun n => (hy n ()).le))
      tendsto_one_div_add_atTop_nhds_zero_nat

lemma modularCore_regularized_adjoint_weight_le (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    modularCoreSquareWeight S (star (T * modularTranslationCalculus g)) ≤
      modularCoreSquareWeight S (T * modularTranslationCalculus g) := by
  let C := modularTranslationCalculus (H := H) g
  have hC : C ∈ modularCrossedProduct (volume : Measure ℝ) S :=
    modularTranslationCalculus_mem S g
  have hCf : modularCoreSquareWeight S C < ⊤ := modularTranslationCalculus_finite S g hg
  let v := modularWeightVector S C hC hCf
  have hw (R : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
      (hR : R ∈ modularCrossedProduct (volume : Measure ℝ) S) :
      modularCoreSquareWeight S (R * C) = ENNReal.ofReal (‖R v‖ ^ 2) := by
    have hf := modularCoreSquareWeight_mul_finite S C hCf R
    rw [← modularWeightVector_mul S C hC hCf R hR,
      modularWeightVector_norm_sq S (R * C) (mul_mem hR hC) hf,
      ENNReal.ofReal_toReal hf.ne]
  change modularCoreSquareWeight S (star (T * C)) ≤ modularCoreSquareWeight S (T * C)
  rw [hw T hT]
  apply iSup_le
  intro m
  obtain ⟨P, hP, hx, hy⟩ := core_twoVector_sequence S T hT v (modularCoreWeightVector S m)
  have hl := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (((star C).continuous.continuousAt.tendsto.comp hy).norm.pow 2)
  have hr := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hx.norm.pow 2)
  have hle := le_of_tendsto_of_tendsto hl hr (Eventually.of_forall (fun n => show
      ENNReal.ofReal (‖star C (star (P n) (modularCoreWeightVector S m))‖ ^ 2) ≤
        ENNReal.ofReal (‖P n v‖ ^ 2) from by
    have hb := le_iSup (fun k : ℕ => ENNReal.ofReal
      (‖star (P n * C) (modularCoreWeightVector S k)‖ ^ 2)) m
    change ENNReal.ofReal _ ≤ modularCoreSquareWeight S (star (P n * C)) at hb
    rw [modularAlgebraic_regularized_adjoint_weight S (P n) (hP n) g hg,
      hw (P n) (algebraicModularCore_le volume S (hP n))] at hb
    simpa only [star_mul, mul_apply_eq_comp] using hb))
  simpa only [star_mul, mul_apply_eq_comp] using hle

lemma modularCoreSquareWeight_le_of_strong_bound (S : StandardModularData H)
    (R : ℕ → (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)))
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hstrong : ∀ f, Tendsto (fun n => R n f) atTop (𝓝 (T f)))
    (C : ℝ≥0∞) (hC : ∀ n, modularCoreSquareWeight S (R n) ≤ C) :
    modularCoreSquareWeight S T ≤ C := by
  apply iSup_le
  intro m
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (((hstrong (modularCoreWeightVector S m)).norm).pow 2))
  apply Eventually.of_forall
  intro n
  exact (le_iSup (fun k : ℕ => ENNReal.ofReal
    (‖R n (modularCoreWeightVector S k)‖ ^ 2)) m).trans (hC n)

private lemma frequencyGaussian_selfAdjoint (n : ℕ) :
    star (modularFrequencyGaussian n) = modularFrequencyGaussian n := by
  ext ω
  change star (Real.exp (-(2 * Real.pi * ω) ^ 2 / (n + 1)) : ℂ) = _
  exact Complex.conj_ofReal _

private lemma core_adjoint_weight_le (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S) :
    modularCoreSquareWeight S (star T) ≤ modularCoreSquareWeight S T := by
  apply modularCoreSquareWeight_le_of_strong_bound S
    (fun n => star (T * modularTranslationCalculus (modularFrequencyGaussian n))) (star T)
  · intro f
    simpa only [star_mul, ← map_star, frequencyGaussian_selfAdjoint, mul_apply_eq_comp] using
      (modularFrequencyGaussian_strong (star T f))
  · intro n
    exact (modularCore_regularized_adjoint_weight_le S T hT
      (modularFrequencyGaussian n) (modularFrequencyGaussian_integrable n)).trans
      (modularCoreSquareWeight_rightMultiplier S T hT (modularFrequencyGaussian n)
        ((BoundedContinuousFunction.norm_le zero_le_one).mpr (modularFrequencyGaussian_norm n)))

/-- The actual extended square weight of the modular core is tracial.
The statement includes infinite weight and requires no extra trace hypothesis. -/
theorem modularCoreSquareWeight_adjoint (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S) :
    modularCoreSquareWeight S (star T) = modularCoreSquareWeight S T := by
  apply le_antisymm (core_adjoint_weight_le S T hT)
  simpa only [star_star] using core_adjoint_weight_le S (star T) (star_mem hT)

end WeakPureInfiniteness

end

end OAI
