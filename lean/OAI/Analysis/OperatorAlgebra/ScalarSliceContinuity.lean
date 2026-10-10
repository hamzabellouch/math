import OAI.Analysis.OperatorAlgebra.ScalarOperatorSlices

namespace OAI

/-! Norm-continuous scalar slices, used to regularize operators in the
modular fixed-point algebra. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ)

omit [CompleteSpace H] in
lemma scalarVectorLpCLM_norm_le (f : Lp ℂ 2 μ) : ‖scalarVectorLpCLM (H := H) μ f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro x
  exact (scalarVectorLp_norm μ f x).le

def scalarVectorLpOperatorLinear : Lp ℂ 2 μ →ₗ[ℂ] (H →L[ℂ] Lp H 2 μ) where
  toFun := scalarVectorLpCLM (H := H) μ
  map_add' f g := by
    apply ContinuousLinearMap.ext
    intro x
    exact map_add ((ContinuousLinearMap.toSpanSingleton ℂ x).compLpL 2 μ) f g
  map_smul' c f := by
    apply ContinuousLinearMap.ext
    intro x
    exact map_smul ((ContinuousLinearMap.toSpanSingleton ℂ x).compLpL 2 μ) c f

def scalarVectorLpOperator : Lp ℂ 2 μ →L[ℂ] (H →L[ℂ] Lp H 2 μ) where
  toLinearMap := scalarVectorLpOperatorLinear (H := H) μ
  cont := AddMonoidHomClass.continuous_of_bound (scalarVectorLpOperatorLinear (H := H) μ) 1
    (fun f => by
      change ‖scalarVectorLpCLM (H := H) μ f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using scalarVectorLpCLM_norm_le (H := H) μ f)

lemma scalarOperatorSlice_continuous (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) :
    Continuous (fun p : Lp ℂ 2 μ × Lp ℂ 2 μ => scalarOperatorSlice μ T p.1 p.2) := by
  have hf : Continuous (fun p : Lp ℂ 2 μ × Lp ℂ 2 μ =>
      scalarVectorLpCLM (H := H) μ p.1) :=
    (scalarVectorLpOperator (H := H) μ).continuous.comp continuous_fst
  have hg : Continuous (fun p : Lp ℂ 2 μ × Lp ℂ 2 μ =>
      scalarVectorLpCLM (H := H) μ p.2) :=
    (scalarVectorLpOperator (H := H) μ).continuous.comp continuous_snd
  exact (ContinuousLinearMap.adjoint.continuous.comp hf).clm_comp
    (continuous_const.clm_comp hg)

lemma scalarOperatorSlice_norm_le (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (f g : Lp ℂ 2 μ) :
    ‖scalarOperatorSlice μ T f g‖ ≤ ‖f‖ * ‖T‖ * ‖g‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have ha : ‖(scalarVectorLpCLM (H := H) μ f).adjoint‖ ≤ ‖f‖ := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact scalarVectorLpCLM_norm_le μ f
  have hb : ‖T.comp (scalarVectorLpCLM (H := H) μ g)‖ ≤ ‖T‖ * ‖g‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (scalarVectorLpCLM_norm_le μ g) (norm_nonneg T))
  exact (mul_le_mul ha hb
    (norm_nonneg (T.comp (scalarVectorLpCLM (H := H) μ g))) (norm_nonneg f)).trans_eq
    (mul_assoc _ _ _).symm

end WeakPureInfiniteness

end

end OAI
