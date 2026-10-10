import Mathlib
import OAI.Geometry.CAT0Fillings.Jacobian.Mixed
import OAI.Geometry.CAT0Fillings.Jacobian.Smoothing

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

namespace CAT0Fillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
lemma integral_lipschitz_mixedJacobian_mul {n : ℕ} {f h : E → ℝ} {g : E → Fin n → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) {K L : ℝ≥0}
    (hh : LipschitzWith K h) (hg : LipschitzWith L g) (v : Fin (n+1) → E) :
    (∫ x, f x * mixedJacobian h g v x ∂μ) =
      -(∫ x, h x * mixedJacobian f g v x ∂μ) := by
  obtain ⟨hs, hhs, hhlim, hhD⟩ := VectorSmoothing.exists_smooth_lipschitz_approximation μ hh
  obtain ⟨gs, hgs, hglim, hgD⟩ := VectorSmoothing.exists_smooth_lipschitz_approximation μ hg
  have hfI : Integrable f μ := hf.continuous.integrable_of_hasCompactSupport hfc
  have H₁ := tendsto_integral_weighted_mixedJacobian μ
    (fs := hs) (gs := gs) (as := fun _ => f) (a := f) (A := fun x => ‖f x‖)
    (K := K) (L := L)
    (fun j x => norm_fderiv_le_of_lipschitz ℝ (hhs j).2)
    (fun j x => norm_fderiv_le_of_lipschitz ℝ (hgs j).2)
    hhD hgD (fun _ => hfI.aestronglyMeasurable) (Eventually.of_forall (fun _ => tendsto_const_nhds))
    hfI.norm (fun _ => Eventually.of_forall fun _ => le_rfl) v
  obtain ⟨N, hN⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf one_ne_zero
  obtain ⟨B, hB0, hB⟩ := uniformly_bounded_lipschitz_on_compact
    (fun j => (hhs j).2) (hhlim 0) hfc
  have hAd : Integrable ((tsupport f).indicator (fun _ : E => B)) μ := by
    apply (integrable_indicator_iff (isClosed_tsupport f).measurableSet).2
    exact continuous_const.continuousOn.integrableOn_compact hfc
  have Hd : ∀ j, AEStronglyMeasurable ((tsupport f).indicator (hs j)) μ :=
    fun j => (hhs j).2.continuous.aestronglyMeasurable.indicator (isClosed_tsupport f).measurableSet
  have Hlim : ∀ᵐ x ∂μ, Tendsto (fun j => (tsupport f).indicator (hs j) x) atTop
      (𝓝 ((tsupport f).indicator h x)) := by
    filter_upwards with x
    by_cases hx : x ∈ tsupport f
    · simpa [hx] using hhlim x
    · simp [hx]
  have Hbound : ∀ j, ∀ᵐ x ∂μ,
      ‖(tsupport f).indicator (hs j) x‖ ≤ (tsupport f).indicator (fun _ => B) x := by
    intro j
    filter_upwards with x
    by_cases hx : x ∈ tsupport f
    · simpa [hx] using hB j x hx
    · simp [hx]
  have H₂ := tendsto_integral_weighted_mixedJacobian μ
    (fs := fun _ => f) (gs := gs) (as := fun j => (tsupport f).indicator (hs j))
    (a := (tsupport f).indicator h) (K := N) (L := L)
    (fun j x => norm_fderiv_le_of_lipschitz ℝ hN)
    (fun j x => norm_fderiv_le_of_lipschitz ℝ (hgs j).2)
    (Eventually.of_forall (fun _ => tendsto_const_nhds)) hgD Hd Hlim hAd Hbound v
  have hcut (u : E → ℝ) (g' : E → Fin n → ℝ) :
      (fun x => (tsupport f).indicator u x * mixedJacobian f g' v x) =
        (fun x => u x * mixedJacobian f g' v x) := by
    funext x
    by_cases hx : x ∈ tsupport f
    · simp [hx]
    · rw [mixedJacobian_eq_zero_of_fderiv_eq_zero v (fderiv_of_notMem_tsupport ℝ hx)]
      simp
  simp_rw [hcut] at H₂
  have heq : (fun j => ∫ x, f x * mixedJacobian (hs j) (gs j) v x ∂μ) =
      fun j => -(∫ x, hs j x * mixedJacobian f (gs j) v x ∂μ) := by
    funext j
    exact integral_smooth_mixedJacobian_mul μ hf hfc ((hhs j).1.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)))
      ((hgs j).1.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) v
  rw [heq] at H₁
  exact tendsto_nhds_unique H₁ H₂.neg

end CAT0Fillings

open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff

namespace CAT0Fillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

lemma continuous_compact_smooth_L1_approx {p : E → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧
      (∫ x, ‖p x - g x‖ ∂μ) ≤ ε := by
  obtain ⟨R, hR⟩ := hpc.isBounded.exists_norm_le
  let φ : ContDiffBump (0 : E) := ⟨|R|+1, |R|+2, by positivity, by linarith⟩
  have hpφ (x : E) : φ x * p x = p x := by
    by_cases hx : p x = 0
    · simp [hx]
    · have H : φ x = 1 := φ.one_of_mem_closedBall (by
        simpa [φ] using (hR x (subset_tsupport p hx)).trans
          ((le_abs_self R).trans (by linarith : |R| ≤ |R|+1)))
      simp [H]
  let S := tsupport (φ : E → ℝ)
  have hSc : IsCompact S := φ.hasCompactSupport
  have hSm : MeasurableSet S := hSc.measurableSet
  let δ := ε / (μ.real S + 1)
  have hμ : 0 ≤ μ.real S := measureReal_nonneg
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨q, hq, hpq⟩ := (hpc.uniformContinuous_of_continuous hp).exists_contDiff_dist_le hδ
  refine ⟨fun x => φ x * q x, φ.contDiff.mul (hq.of_le (by simp)), φ.hasCompactSupport.mul_right, ?_⟩
  have hPI : Integrable p μ := hp.integrable_of_hasCompactSupport hpc
  have hQI : Integrable (fun x => φ x * q x) μ :=
    (φ.continuous.mul hq.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hAI : Integrable (S.indicator (fun _ : E => δ)) μ :=
    (integrable_indicator_iff hSm).2 (continuous_const.continuousOn.integrableOn_compact hSc)
  have hbd : ∀ x, ‖p x - φ x * q x‖ ≤ S.indicator (fun _ => δ) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      calc ‖p x - φ x * q x‖ = ‖φ x * (p x-q x)‖ := by rw [mul_sub, hpφ]
        _ ≤ ‖p x-q x‖ := by
          rw [norm_mul, Real.norm_of_nonneg φ.nonneg]
          exact mul_le_of_le_one_left (norm_nonneg _) φ.le_one
        _ ≤ δ := by simpa [dist_eq_norm, norm_sub_rev] using (hpq x).le
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hpx : p x = 0 := by simpa [hφx] using (hpφ x).symm
      simp [hx, hφx, hpx]
  calc (∫ x, ‖p x - φ x * q x‖ ∂μ) ≤ ∫ x, S.indicator (fun _ : E => δ) x ∂μ :=
      integral_mono_ae (hPI.sub hQI).norm hAI (Eventually.of_forall hbd)
    _ = μ.real S * δ := by rw [integral_indicator hSm]; simp [measureReal_def]
    _ ≤ ε := by
      dsimp [δ]
      rw [← mul_div_assoc, div_le_iff₀ (by linarith : 0 < μ.real S + 1)]
      nlinarith

end CAT0Fillings
end

end OAI
