import Mathlib
import OAI.Geometry.CAT0Fillings.BV.JointPoincare
import OAI.Geometry.CAT0Fillings.Compactness.Translation

namespace OAI

section
open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV
lemma scalar_precompR {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (lsmul ℝ ℝ).precompR E = (lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) := by
  ext scalar linearMap
  simp only [precompR,coe_comp,Function.comp_apply,compL_apply,lsmul_apply,_root_.smul_apply]

lemma convolution_bump_deriv_norm_integrable {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin k))} [μ.IsAddHaarMeasure]
    (hf : Integrable f μ) (η : ContDiffBump (0:EuclideanSpace ℝ (Fin k))) :
    Integrable (fun x => ‖(f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), μ]
      fderiv ℝ (η.normed μ)) x‖) μ := by
  have hc := η.hasCompactSupport_normed (μ := μ)
  have hd := (η.contDiff_normed (μ := μ) (n := (⊤ : ℕ∞))).continuous_fderiv (by simp)
  rw [scalar_precompR]
  exact (hf.integrable_convolution (lsmul ℝ ℝ : ℝ →L[ℝ] (EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ))
    (hd.integrable_of_hasCompactSupport (hc.fderiv ℝ))).norm
end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology ENNReal NNReal Convolution

namespace CAT0Fillings.JointBV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

lemma convolution_bump_hasFDerivAt {f : E → ℝ} (hf : Integrable f μ)
    (η : ContDiffBump (0:E)) (x : E) :
    HasFDerivAt (f ⋆[lsmul ℝ ℝ, μ] η.normed μ)
      ((f ⋆[(lsmul ℝ ℝ).precompR E, μ] fderiv ℝ (η.normed μ)) x) x :=
  η.hasCompactSupport_normed.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf.locallyIntegrable η.contDiff_normed x

lemma convolution_bump_deriv_continuous {f : E → ℝ} (hf : Integrable f μ)
    (η : ContDiffBump (0:E)) :
    Continuous (f ⋆[(lsmul ℝ ℝ).precompR E, μ] fderiv ℝ (η.normed μ)) :=
  (η.hasCompactSupport_normed.fderiv ℝ).continuous_convolution_right
    ((lsmul ℝ ℝ).precompR E) hf.locallyIntegrable
    ((η.contDiff_normed (n := (⊤ : ℕ∞))).continuous_fderiv (by simp))

lemma convolution_bump_integrable {f : E → ℝ} (hf : Integrable f μ)
    (η : ContDiffBump (0:E)) : Integrable (f ⋆[lsmul ℝ ℝ, μ] η.normed μ) μ :=
  hf.integrable_convolution (lsmul ℝ ℝ)
    (η.continuous_normed.integrable_of_hasCompactSupport η.hasCompactSupport_normed)

lemma mollified_gradient_total_bound {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin k))} [μ.IsAddHaarMeasure]
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ν]
    (hf : Integrable f μ)
    (hv : ∀ i, DirectionalVariation f (EuclideanSpace.basisFun (Fin k) ℝ i) μ ν)
    (η : ContDiffBump (0 : EuclideanSpace ℝ (Fin k))) :
    (∫ z, ‖(f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), μ]
      fderiv ℝ (η.normed μ)) z‖ ∂μ) ≤ k*ν.real univ := by
  apply integral_le_of_closedBall_bound
    (convolution_bump_deriv_norm_integrable hf η)
  intro r
  exact (mollified_gradient_integral_bound hf.locallyIntegrable hv η 0 r).trans
    (mul_le_mul_of_nonneg_left (measureReal_mono (subset_univ _)) (Nat.cast_nonneg k))

theorem translation_integral_bound {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin k))} [μ.IsAddHaarMeasure]
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ν]
    (hf : Integrable f μ)
    (hv : ∀ i, DirectionalVariation f (EuclideanSpace.basisFun (Fin k) ℝ i) μ ν)
    (w : EuclideanSpace ℝ (Fin k)) :
    (∫ x, |f (x+w)-f x| ∂μ) ≤ ‖w‖*(k*ν.real univ) := by
  let η (j : ℕ) := shrinkingBump (E := EuclideanSpace ℝ (Fin k)) j
  let F (j : ℕ) := f ⋆[lsmul ℝ ℝ, μ] (η j).normed μ
  let F' (j : ℕ) := f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), μ]
    fderiv ℝ ((η j).normed μ)
  have hF (j : ℕ) (x : EuclideanSpace ℝ (Fin k)) : HasFDerivAt (F j) (F' j x) x :=
    convolution_bump_hasFDerivAt hf (η j) x
  have hF' (j : ℕ) : Continuous (F' j) := convolution_bump_deriv_continuous hf (η j)
  have hFi (j : ℕ) : Integrable (F j) μ := convolution_bump_integrable hf (η j)
  have hGi (j : ℕ) : Integrable (fun x => ‖F' j x‖) μ :=
    convolution_bump_deriv_norm_integrable hf (η j)
  have hl : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x)) := by
    have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := η) shrinkingBump_tendsto (K := 2) (Eventually.of_forall (fun j => le_rfl)) hf.locallyIntegrable
    filter_upwards [hh] with x hx
    simpa only [F,scalar_convolution_comm f] using hx
  have hlw := (measurePreserving_add_right μ w).quasiMeasurePreserving.ae hl
  apply integral_abs_le_of_ae_tendsto ((hf.comp_add_right w).sub hf)
    (fun j => ((hFi j).comp_add_right w).sub (hFi j)) ?_ (by positivity)
  · exact Eventually.of_forall fun j =>
      (smooth_translation_integral_bound (hF j) (hF' j) (hFi j) (hGi j) w).trans
        (mul_le_mul_of_nonneg_left (mollified_gradient_total_bound hf hv (η j)) (norm_nonneg w))
  · filter_upwards [hlw,hl] with x hx hw
    exact hx.sub hw

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV

lemma DirectionalVariation.congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {μ ν : Measure E} {f g : E → ℝ} {v : E}
    (h : DirectionalVariation f v μ ν) (he : f =ᵐ[μ] g) :
    DirectionalVariation g v μ ν := by
  intro φ hφ hc
  have hh := h φ hφ hc
  convert hh using 2
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

theorem totallyBounded_L1_of_directional_variation {k : ℕ} {ι : Type*}
    (f : ι → EuclideanSpace ℝ (Fin k) → ℝ) (hf : ∀ i, Integrable (f i))
    (ν : ι → Measure (EuclideanSpace ℝ (Fin k))) [∀ i, IsFiniteMeasure (ν i)]
    (hv : ∀ i l, DirectionalVariation (f i) (EuclideanSpace.basisFun (Fin k) ℝ l) volume (ν i))
    (B : ℝ≥0) (hB : ∀ i, (∫ x, |f i x|) ≤ B)
    (M : ℝ≥0) (hM : ∀ i, (ν i).real univ ≤ M)
    (R : ℝ) (hs : ∀ i, ∀ᵐ x, x ∉ closedBall 0 R → f i x = 0) :
    TotallyBounded (range fun i => (hf i).toL1 (f i)) := by
  let g (i) := (closedBall 0 R).indicator (f i)
  have he (i) : f i =ᵐ[volume] g i := by
    filter_upwards [hs i] with x hx
    by_cases hxR : x ∈ closedBall 0 R
    · simp only [g,indicator_of_mem hxR]
    · simp only [g,indicator_of_notMem hxR,hx hxR]
  have hg (i) : Integrable (g i) := (hf i).congr (he i)
  have hge (i) : (hf i).toL1 (f i) = (hg i).toL1 (g i) :=
    (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (he i)
  simp only [hge]
  apply totallyBounded_L1_of_translation g hg B ?_ R ?_ (C := k*(M:ℝ)) (by positivity)
  · intro i w
    have hh := translation_integral_bound (hg i) (fun l => (hv i l).congr (he i)) w
    apply hh.trans
    calc ‖w‖*((k:ℝ)*(ν i).real univ) ≤ ‖w‖*((k:ℝ)*M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hM i) (Nat.cast_nonneg k)) (norm_nonneg w)
      _ = _ := mul_comm _ _
  · intro i
    have hi : (∫ x, |g i x|) = ∫ x, |f i x| := integral_congr_ae ((he i).symm.fun_comp abs)
    rw [hi]
    exact hB i
  · intro i x hx
    by_contra hn
    exact hx (indicator_of_notMem hn _)

end CAT0Fillings.JointBV
end

end OAI
