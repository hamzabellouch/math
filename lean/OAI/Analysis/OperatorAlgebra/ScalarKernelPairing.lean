import OAI.Analysis.OperatorAlgebra.ScalarTranslationConvolution
import OAI.Analysis.ModularTheory.CovariantKernel

namespace OAI

/-! Matrix coefficients of the actual convolution-smoothed operator are
the double integrals of its covariant scalar-slice kernel. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace WeakPureInfiniteness

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma inner_integral_left {F : ℝ → K} (hF : Integrable F) (y : K) :
    inner ℂ (∫ t, F t) y = ∫ t, inner ℂ (F t) y := by
  calc
    _ = conj (inner ℂ y (∫ t, F t)) := (inner_conj_symm _ _).symm
    _ = conj (∫ t, inner ℂ y (F t)) := congrArg conj (integral_inner hF y).symm
    _ = ∫ t, conj (inner ℂ y (F t)) := integral_conj.symm
    _ = _ := by simp only [inner_conj_symm]

lemma inner_integral_pair (T : K →L[ℂ] K) {F G : ℝ → K}
    (hF : Integrable F) (hG : Integrable G) :
    inner ℂ (T (∫ t, F t)) (∫ s, G s) =
      ∫ t, ∫ s, inner ℂ (T (F t)) (G s) := by
  rw [← T.integral_comp_comm hF, inner_integral_left (T.integrable_comp hF)]
  apply integral_congr_ae
  filter_upwards [] with t
  exact (integral_inner hG _).symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma scalarTranslationSynthesis_integrable (g u : Lp ℂ 2 (volume : Measure ℝ))
    (hu : Integrable (u : ℝ → ℂ)) (x : H) :
    Integrable (fun t : ℝ => u t • scalarVectorLp volume (modularLpTranslate volume t g) x) := by
  have hc : Continuous (fun t => scalarVectorLp volume (modularLpTranslate volume t g) x) :=
    ((ContinuousLinearMap.toSpanSingleton ℂ x).compLpL 2 volume).continuous.comp
      (continuous_modularLpTranslate g)
  apply BoundedRecovery.integrable_smul_bounded_orbit hu hc
  intro t
  rw [scalarVectorLp_norm, (modularLpTranslate volume t).norm_map]

theorem scalarKernel_convolution_pairing
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g u v : Lp ℂ 2 (volume : Measure ℝ))
    (hf : Integrable (f : ℝ → ℂ)) (hg : Integrable (g : ℝ → ℂ))
    (hu : Integrable (u : ℝ → ℂ)) (hv : Integrable (v : ℝ → ℂ)) (x y : H) :
    inner ℂ (T (integratedModularTranslation g hg (scalarVectorLp volume u x)))
      (integratedModularTranslation f hf (scalarVectorLp volume v y)) =
      ∫ t : ℝ, ∫ s : ℝ, star (u t) * v s * inner ℂ (modularSliceKernel T f g s t x) y := by
  rw [scalarVectorLp_convolution_synthesis g u hg hu,
    scalarVectorLp_convolution_synthesis f v hf hv]
  refine (inner_integral_pair T (scalarTranslationSynthesis_integrable g u hu x)
    (scalarTranslationSynthesis_integrable f v hv y)).trans ?_
  apply integral_congr_ae
  filter_upwards [] with t
  apply integral_congr_ae
  filter_upwards [] with s
  rw [map_smul, inner_smul_left, inner_smul_right]
  change _ = star (u t) * v s * inner ℂ
    (scalarOperatorSlice volume T (modularLpTranslate volume s f)
      (modularLpTranslate volume t g) x) y
  rw [scalarOperatorSlice_inner]
  simp only [starRingEnd_apply]
  ring

def convolutionSmoothedOperator
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ))
    (hf : Integrable (f : ℝ → ℂ)) (hg : Integrable (g : ℝ → ℂ)) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  (integratedModularTranslation f hf).adjoint * T * integratedModularTranslation g hg

theorem convolutionSmoothedOperator_pairing
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g u v : Lp ℂ 2 (volume : Measure ℝ))
    (hf : Integrable (f : ℝ → ℂ)) (hg : Integrable (g : ℝ → ℂ))
    (hu : Integrable (u : ℝ → ℂ)) (hv : Integrable (v : ℝ → ℂ)) (x y : H) :
    inner ℂ (convolutionSmoothedOperator T f g hf hg (scalarVectorLp volume u x))
      (scalarVectorLp volume v y) =
      ∫ t : ℝ, ∫ s : ℝ, star (u t) * v s * inner ℂ (modularSliceKernel T f g s t x) y := by
  change inner ℂ ((integratedModularTranslation f hf).adjoint
    (T (integratedModularTranslation g hg (scalarVectorLp volume u x)))) _ = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact scalarKernel_convolution_pairing T f g u v hf hg hu hv x y

end WeakPureInfiniteness

end

end OAI
