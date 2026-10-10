import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Basic

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings.VectorSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (μ : Measure E) [IsAddHaarMeasure μ]
lemma hasFDerivAt_convolution_lipschitz {f : E → F} {g : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : Continuous g) (hgc : HasCompactSupport g) (x : E) :
    HasFDerivAt (g ⋆[lsmul ℝ ℝ, μ] f)
      ((g ⋆[lsmul ℝ ℝ, μ] (fderiv ℝ f)) x) x := by
  have hsub := (μ.measurePreserving_sub_left x).quasiMeasurePreserving
  have hD : ∀ᵐ t ∂μ, DifferentiableAt ℝ f (x - t) :=
    hsub.ae (hf.ae_differentiableAt (μ := μ))
  have hgI := hg.integrable_of_hasCompactSupport (μ := μ) hgc
  have hFI (y : E) : Integrable (fun t => g t • f (y-t)) μ :=
    (hg.smul (hf.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hgc.smul_right
  have hDm : AEStronglyMeasurable (fun t => g t • fderiv ℝ f (x-t)) μ :=
    hg.aestronglyMeasurable.smul
      ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hdif : ∀ᵐ t ∂μ, HasFDerivAt (fun y => g t • f (y-t))
      (g t • fderiv ℝ f (x-t)) x := by
    filter_upwards [hD] with t ht
    have H := ((ht.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const t)).const_smul (g t))
    change HasFDerivAt (fun y => g t • f (y-t)) _ x at H
    simpa using H
  have hbound : ∀ᵐ t ∂μ, ∀ y ∈ (univ : Set E),
      ‖g t • f (y-t) - g t • f (x-t)‖ ≤ (‖g t‖ * K) * ‖y-x‖ := by
    filter_upwards with t y _
    rw [← smul_sub, norm_smul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa [dist_eq_norm] using hf.dist_le_mul (y-t) (x-t)
  have H := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (μ := μ) (s := univ) (F := fun y t => g t • f (y-t))
    (F' := fun t => g t • fderiv ℝ f (x-t)) (bound := fun t => ‖g t‖ * K)
    (x₀ := x) univ_mem (fun y _ => (hFI y).aestronglyMeasurable) (hFI x)
    hDm hbound (hgI.norm.mul_const K) hdif
  simpa +unfoldPartialApp [convolution, lsmul_apply] using H.2

lemma locallyIntegrable_fderiv_lipschitz {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LocallyIntegrable (fderiv ℝ f) μ := by
  apply (locallyIntegrable_const (μ := μ) (K : ℝ)).mono
    (measurable_fderiv ℝ f).aestronglyMeasurable
  filter_upwards with x
  simpa using norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)

lemma fderiv_bump_convolution {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x =
      ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f) x) :=
  (hasFDerivAt_convolution_lipschitz μ hf (φ.contDiff_normed (n := 1)).continuous
    φ.hasCompactSupport_normed x).fderiv

lemma ae_fderiv_bump_convolution_tendsto {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} {C : ℝ}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hφ' : ∀ᶠ i in l, (φ i).rOut ≤ C * (φ i).rIn) :
    ∀ᵐ x ∂μ, Tendsto (fun i => fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) x)
      l (𝓝 (fderiv ℝ f x)) := by
  simp_rw [fderiv_bump_convolution μ hf]
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hφ'
    (locallyIntegrable_fderiv_lipschitz μ hf)

lemma norm_fderiv_bump_convolution_le {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (x : E) :
    ‖fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ ≤ K := by
  rw [fderiv_bump_convolution μ hf, convolution_def]
  have hI := ((φ.contDiff_normed (μ := μ) (n := 1)).continuous.integrable_of_hasCompactSupport
    (μ := μ) φ.hasCompactSupport_normed).mul_const (K : ℝ)
  have H := norm_integral_le_of_norm_le hI (Eventually.of_forall (fun t => show
      ‖lsmul ℝ ℝ (φ.normed μ t) (fderiv ℝ f (x-t))‖ ≤ φ.normed μ t * K from by
    rw [lsmul_apply, norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hf) (φ.nonneg_normed t)))
  simpa only [integral_mul_const, φ.integral_normed, one_mul] using H

lemma lipschitzWith_bump_convolution {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) :
    LipschitzWith K (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact fun x => (hasFDerivAt_convolution_lipschitz μ hf
      (φ.contDiff_normed (n := 1)).continuous φ.hasCompactSupport_normed x).differentiableAt
  · intro x
    exact_mod_cast norm_fderiv_bump_convolution_le μ hf φ x

lemma contDiff_bump_convolution {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (n : ℕ∞) :
    ContDiff ℝ n (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hf.continuous.locallyIntegrable

noncomputable def shrinkingBump (j : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / (j + 1 : ℝ)
  rOut := 2 / (j + 1 : ℝ)
  rIn_pos := by positivity
  rIn_lt_rOut := by gcongr; norm_num

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma shrinkingBump_tendsto : Tendsto (fun j : ℕ => (shrinkingBump (E := E) j).rOut)
    atTop (𝓝 0) := by
  simpa [shrinkingBump, div_eq_mul_inv] using
    (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))

lemma exists_smooth_lipschitz_approximation {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) : ∃ f' : ℕ → E → F,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (f' j) ∧ LipschitzWith K (f' j)) ∧
      (∀ x, Tendsto (fun j => f' j x) atTop (𝓝 (f x))) ∧
      (∀ᵐ x ∂μ, Tendsto (fun j => fderiv ℝ (f' j) x) atTop (𝓝 (fderiv ℝ f x))) := by
  refine ⟨fun j => (shrinkingBump j).normed μ ⋆[lsmul ℝ ℝ, μ] f, ?_, ?_, ?_⟩
  · intro j
    exact ⟨contDiff_bump_convolution μ hf _ ⊤, lipschitzWith_bump_convolution μ hf _⟩
  · exact ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_tendsto hf.continuous
  · apply ae_fderiv_bump_convolution_tendsto μ hf shrinkingBump_tendsto (C := 2)
    filter_upwards with j
    dsimp [shrinkingBump]
    ring_nf
    rfl

end CAT0Fillings.VectorSmoothing

end

end OAI
