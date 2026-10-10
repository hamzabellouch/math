import OAI.Analysis.ModularTheory.FiniteProjections

namespace OAI

/-! A concrete exhaustion of the modular core by finite-weight corners. -/

noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped Topology ENNReal

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularFiniteProjection_strong (f : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => modularFiniteProjection (H := H) n f) atTop (𝓝 f) := by
  let b (n : ℕ) : ℝ → ℂ := (Icc (-(n : ℝ)) n).indicator (fun _ => 1)
  have hb (n : ℕ) : AEStronglyMeasurable (b n) volume :=
    (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable
  have hn (n : ℕ) (t : ℝ) : ‖b n t‖ ≤ 1 := by
    by_cases ht : t ∈ Icc (-(n : ℝ)) n <;> simp [b, ht]
  have ht (t : ℝ) : Tendsto (fun n => b n t) atTop (𝓝 1) := by
    obtain ⟨N, hN⟩ := exists_nat_gt |t|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hNn
    have htn : |t| ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hNn)
    dsimp only [b]
    have ht' : t ∈ Icc (-(n : ℝ)) n := abs_le.mp htn
    simp only [Set.indicator_of_mem ht']
  have hs := boundedVectorLp_strong b (fun _ => (1 : ℂ)) hb (by fun_prop)
    1 zero_le_one hn (by simp) ht (𝓕 f)
  have he : boundedVectorLp (H := H) volume (fun _ => (1 : ℂ))
      (by fun_prop) 1 (by simp) = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    change boundedVectorLp volume (fun _ => (1 : ℂ)) (by fun_prop) 1 (by simp) v = v
    apply Lp.ext
    filter_upwards [boundedVectorLp_ae volume (fun _ => (1 : ℂ))
      (by fun_prop) 1 (by simp) v] with t ht
    simpa only [one_smul] using ht
  rw [he, one_apply_eq_self] at hs
  have hout := (Lp.fourierTransformₗᵢ ℝ H).symm.continuous.continuousAt.tendsto.comp hs
  change Tendsto (fun n => modularFiniteProjection (H := H) n f) atTop
    (𝓝 (𝓕⁻ (𝓕 f))) at hout
  simpa only [fourierInv_fourier_eq] using hout

lemma modularFiniteProjection_right_strong
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => (T * modularFiniteProjection (H := H) n) f) atTop (𝓝 (T f)) :=
  T.continuous.continuousAt.tendsto.comp (modularFiniteProjection_strong f)

lemma modularFiniteProjection_corner_strong
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => (modularFiniteProjection (H := H) n * T * modularFiniteProjection (H := H) n) f)
      atTop (𝓝 (T f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hx := (tendsto_iff_norm_sub_tendsto_zero.mp
    (modularFiniteProjection_right_strong T f)).add
      (tendsto_iff_norm_sub_tendsto_zero.mp (modularFiniteProjection_strong (T f)))
  rw [add_zero] at hx
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hx
  apply Eventually.of_forall
  intro n
  let P := modularFiniteProjection (H := H) n
  have he : (P * T * P) f - T f = P (T (P f) - T f) + (P (T f) - T f) := by
    simp only [mul_apply_eq_comp, map_sub]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  change ‖P (T (P f) - T f)‖ ≤ ‖T (P f) - T f‖
  exact (P.le_opNorm _).trans (by
    dsimp only [P]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (modularFiniteProjection_norm_le (H := H) n) (norm_nonneg _))

lemma modularCore_finite_right_dense (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S) :
    (∀ n, T * modularFiniteProjection (H := H) n ∈ modularCrossedProduct (volume : Measure ℝ) S) ∧
    (∀ n, modularCoreSquareWeight S (T * modularFiniteProjection (H := H) n) < ⊤) ∧
    (∀ f, Tendsto (fun n => (T * modularFiniteProjection (H := H) n) f) atTop (𝓝 (T f))) :=
  ⟨fun n => mul_mem hT (modularFiniteProjection_mem S n),
    fun n => modularCoreSquareWeight_mul_finite S _ (modularFiniteProjection_finite S n) T,
    modularFiniteProjection_right_strong T⟩

lemma modularCore_finite_corner_weight (S : StandardModularData H) (n : ℕ)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (hTP : T * modularFiniteProjection (H := H) n = T) :
    modularCoreSquareWeight S T = ENNReal.ofReal (‖T (modularCoreWeightVector S n)‖ ^ 2) := by
  have hfin := modularCoreSquareWeight_mul_finite S _ (modularFiniteProjection_finite S n) T
  have he := modularWeightVector_norm_sq S (T * modularFiniteProjection (H := H) n)
    (mul_mem hT (modularFiniteProjection_mem S n)) hfin
  rw [modularWeightVector_mul S _ (modularFiniteProjection_mem S n)
    (modularFiniteProjection_finite S n) T hT, modularFiniteProjection_weightGNS] at he
  have h := congrArg ENNReal.ofReal he
  rw [ENNReal.ofReal_toReal hfin.ne, hTP] at h
  exact h.symm

lemma modularCore_finite_corner_adjoint_norm (S : StandardModularData H) (n : ℕ)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (hTP : T * modularFiniteProjection (H := H) n = T)
    (hPT : modularFiniteProjection (H := H) n * T = T) :
    ‖star T (modularCoreWeightVector S n)‖ ^ 2 =
      ‖T (modularCoreWeightVector S n)‖ ^ 2 := by
  have hstarP := (modularFiniteProjection_isStarProjection (H := H) n).isSelfAdjoint.star_eq
  have hsTP : star T * modularFiniteProjection (H := H) n = star T := by
    simpa only [star_mul, hstarP] using congrArg star hPT
  have h := modularCoreSquareWeight_adjoint S T hT
  rw [modularCore_finite_corner_weight S n (star T) (star_mem hT) hsTP,
    modularCore_finite_corner_weight S n T hT hTP] at h
  have hh := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hh

end WeakPureInfiniteness

end

end OAI
