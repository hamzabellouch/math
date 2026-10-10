import OAI.Geometry.Perimeter.Regularity.PlaneHeightLimit
import OAI.Geometry.Perimeter.Regularity.HarmonicHeightLimit
import OAI.Geometry.Perimeter.Regularity.FiberQuadraticLimit
import OAI.Geometry.Perimeter.Regularity.SupportImprovement
import OAI.Geometry.Perimeter.Regularity.HarmonicLimitBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n m : ℕ}

theorem minimizing_plane_limit_integral_bound
    (E : ℕ → Set (Euc n)) (hmin : ∀ i, IsLocallyPerimeterMinimizing (E i))
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {η : Euc n → ℝ} (hη : Continuous η) (hcη : HasCompactSupport η)
    (hηs : Function.support η ⊆ Metric.ball 0 4) (hηb : ∀ x, ‖η x‖≤1)
    (a : ℕ → ℝ) (ha : ∀ i, 0<a i)
    (hphase : ∀ i, ∀ᵐ x ∂volume, x∈Metric.ball 0 4 → a i < |inner ℝ v x| →
      (x∈E i ↔ inner ℝ v x<0))
    {g : Euc m → ℝ} (hg : Integrable g volume)
    (hL : Tendsto (fun i ↦ ∫⁻ y, ‖chartFiber v e (a i) (cutoffPhaseError (E i) v η) y-g y‖ₑ)
      atTop (𝓝 0)) :
    (∫ y, ‖g y‖)≤volume.real (Metric.ball (0:Euc n) 8)/4 := by
  let V := volume.real (Metric.ball (0:Euc n) 8)/4
  have hV : 0≤V := by dsimp [V]; positivity
  have hi (i) := chartFiber_integrable (cutoffPhaseError_integrable (hmin i).1 v hη hcη) hv e (a i)
  apply integral_norm_le_of_L1_limit _ hi hg _ hL
  intro i
  have hb := chartFiber_normalized_mass (cutoffPhaseError_measurable (hmin i).1 v hη.measurable)
    hv e (ha i) (cutoffPhaseError_lintegral_height_le (hmin i).1 hv hη.measurable hηb
      (by norm_num : (0:ℝ)<4) (ha i).le hηs (hphase i))
  rw [← ofReal_integral_norm_eq_lintegral_enorm (hi i)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hV).mp (by simpa only [V, show (2:ℝ)*4=8 by norm_num] using hb)

theorem normalPlane_chart_linear {v : Euc n} (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    (L : Euc m →L[ℝ] ℝ) :
    let ℓ := L.comp (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (normalProjection v))
    ℓ v=0 ∧ ‖ℓ‖≤‖L‖ := by
  let ℓ := L.comp (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (normalProjection v))
  change ℓ v = 0 ∧ ‖ℓ‖ ≤ ‖L‖
  have hv : normalProjection v v=0 :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
      ((ℝ ∙ v).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self v))
  constructor
  · change L (e.symm (normalProjection v v)) = 0
    rw [hv, map_zero, map_zero]
  · refine ContinuousLinearMap.opNorm_le_bound (f := ℓ) (norm_nonneg L) ?_
    intro x
    change ‖L (e.symm (normalProjection v x))‖ ≤ ‖L‖ * ‖x‖
    calc
      _ ≤ ‖L‖ * ‖e.symm (normalProjection v x)‖ := L.le_opNorm _
      _ = ‖L‖ * ‖normalProjection v x‖ := by rw [e.symm.norm_map]
      _ ≤ ‖L‖ * ‖x‖ := mul_le_mul_of_nonneg_left
        ((normalPlane v).norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg L)

theorem exists_sequential_flatness_constants (n m : ℕ) (hn : 1<n) (hm : 0 < m) :
    ∃ K B : ℝ, 0<K ∧ 0≤B ∧ ∀ (E : ℕ → Set (Euc n)),
      (∀ i, IsLocallyPerimeterMinimizing (E i)) →
      (∀ i, (0:Euc n)∈perimeterSupport (E i)) →
      ∀ (v : Euc n), ‖v‖=1 → (Euc m ≃ₗᵢ[ℝ] normalPlane v) →
      ∀ (a : ℕ → ℝ), (∀ i, 0<a i) → Tendsto a atTop (𝓝 0) →
      (∀ i x, x∈perimeterSupport (E i) ∩ Metric.ball 0 4 → |inner ℝ v x|≤a i) →
      (∀ i, ∀ᵐ x ∂volume, x∈Metric.ball 0 4 → a i < |inner ℝ v x| →
        (x∈E i ↔ inner ℝ v x<0)) →
      Tendsto (fun i ↦ orientedTilt (E i) v (Metric.ball 0 4)) atTop (𝓝 0) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ ℓ : Euc n →L[ℝ] ℝ,
        ℓ v=0 ∧ ‖ℓ‖≤B ∧ ∀ r : ℝ, 0<r → r<1/8 → ∀ᶠ i in atTop,
          ∀ p∈perimeterSupport (E (σ i)) ∩ Metric.ball 0 r,
            |inner ℝ v p/a (σ i)-ℓ p|≤K*r^2 := by
  obtain ⟨C,hC,hTaylor⟩ := harmonicRegularization_uniform_taylor m
  have hcK : HasCompactSupport (scaledHarmonicKernel (n := m) 4) :=
    (isCompact_closedBall 0 (1/(4:ℝ))).of_isClosed_subset (isClosed_tsupport _)
      (scaledHarmonicKernel_tsupport (by norm_num))
  obtain ⟨M,hM,hLin⟩ := kernelLinear_uniform_bound (scaledHarmonicKernel_contDiff 4) hcK
  let V := volume.real (Metric.ball (0:Euc n) 8)/4
  have hV : 0≤V := by dsimp [V]; positivity
  let D := C*V
  have hD : 0≤D := mul_nonneg hC hV
  obtain ⟨K,hK,himp⟩ := exists_full_support_improvement_constant n hn D hD
  refine ⟨K,M*V,hK,mul_nonneg hM hV,fun E hmin hzero v hv e a ha hat hh hphase htilt ↦ ?_⟩
  let η : ContDiffBump (0:Euc n) := ⟨3,7/2,by norm_num,by norm_num⟩
  have hηs : tsupport (η:Euc n → ℝ) ⊆ Metric.ball 0 4 := by
    rw [η.tsupport_eq]; exact Metric.closedBall_subset_ball (by norm_num : (7:ℝ)/2<4)
  have hηone : ∀ x∈Metric.ball (0:Euc n) 3, η x=1 := fun x hx ↦
    η.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  have hηb : ∀ x, ‖η x‖≤1 := fun x ↦ by rw [Real.norm_of_nonneg η.nonneg]; exact η.le_one
  obtain ⟨L₀,hL₀⟩ := (isCompact_closedBall (0:Euc n) 4).exists_bound_of_continuousOn
    (gradient_contDiff η.contDiff).continuous.continuousOn
  let L := max L₀ 0
  have hLg : ∀ x∈Metric.ball (0:Euc n) 4, ‖gradient η x‖≤L :=
    fun x hx ↦ (hL₀ x (Metric.ball_subset_closedBall hx)).trans (le_max_left _ _)
  obtain ⟨G,hG,hgrowth⟩ := exists_locallyMinimizing_perimeter_growth_constant n (by omega)
  have hper (i) : (perimeter (E i) (Metric.ball 0 4)).toReal≤G*4^(n-1) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgrowth (E i) (hmin i) 0 4 (by norm_num))
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    exact h
  obtain ⟨g,hg,hgs,σ,hσ,hL1⟩ := minimizing_plane_height_subsequence hn E hmin hv e
    η.contDiff η.hasCompactSupport hηb (by norm_num : (0:ℝ)<4) (le_max_right _ _)
    hηs hLg a ha hh hper hphase
  have has := hat.comp hσ.tendsto_atTop
  have ht := htilt.comp hσ.tendsto_atTop
  have hgv : (∫ y, ‖g y‖)≤V := minimizing_plane_limit_integral_bound
    (fun i ↦ E (σ i)) (fun i ↦ hmin (σ i)) hv e η.continuous η.hasCompactSupport
    (subset_closure.trans hηs) hηb (fun i ↦ a (σ i)) (fun i ↦ ha (σ i))
    (fun i ↦ hphase (σ i)) hg hL1
  have hgh : WeakHarmonicOn g (Metric.ball 0 1) := minimizing_plane_height_weakHarmonic hn
    (fun i ↦ E (σ i)) (fun i ↦ hmin (σ i)) hv e η.continuous hηb η.hasCompactSupport
    (subset_closure.trans hηs) hηone (fun i ↦ a (σ i)) (fun i ↦ ha (σ i)) has
    (fun i ↦ hh (σ i)) (fun i ↦ hphase (σ i)) (fun i ↦ hper (σ i)) ht hg hL1
  let f := harmonicRegularization g 4
  have hf : ContDiff ℝ ∞ f := harmonicRegularization_contDiff hg.locallyIntegrable (by norm_num)
  have hgf : g =ᵐ[volume.restrict (Metric.ball 0 (1/2))] f := by
    filter_upwards [ae_restrict_of_ae (weakHarmonic_ae_eq_regularization hg.locallyIntegrable hgh hm),
      ae_restrict_mem measurableSet_ball] with y hy hyB
    apply hy (1/2) (by norm_num) _ 4 (by norm_num)
    intro z hz
    have hd := dist_triangle z y 0
    rw [Metric.mem_ball] at hz hyB ⊢
    linarith
  let Lh := kernelLinear g (scaledHarmonicKernel 4)
  let ℓ := Lh.comp (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (normalProjection v))
  have hℓ := normalPlane_chart_linear e Lh
  let w : normalPlane v → ℝ := fun y ↦ f (e.symm y)
  have hw : Continuous w := hf.continuous.comp e.symm.continuous
  let φ : ContDiffBump (0:normalPlane v) := ⟨1/4,1/3,by norm_num,by norm_num⟩
  have hφs : tsupport (φ:normalPlane v → ℝ) ⊆ Metric.ball 0 1 := by
    rw [φ.tsupport_eq]; exact Metric.closedBall_subset_ball (by norm_num : (1:ℝ)/3<1)
  have hwg : ∀ᵐ y : Euc m ∂volume, φ (e y)≠0 → w (e y)=g y := by
    have hgf' := (ae_restrict_iff' measurableSet_ball).mp hgf
    filter_upwards [hgf'] with y hy
    intro hφy
    have hyb : y∈Metric.ball (0:Euc m) (1/2) := by
      have hyB : e y∈Metric.ball 0 (1/3) := by rwa [← φ.support_eq]
      rw [Metric.mem_ball,dist_zero_right,e.norm_map] at hyB
      rw [Metric.mem_ball,dist_zero_right]; linarith
    simpa only [w,e.symm_apply_apply] using (hy hyb).symm
  have htrace := minimizing_quadratic_height_trace_tendsto_zero hn (fun i ↦ E (σ i))
    (fun i ↦ hmin (σ i)) hv e η.continuous η.hasCompactSupport (subset_closure.trans hηs)
    hηone (fun i ↦ a (σ i)) (fun i ↦ ha (σ i)) has (fun i ↦ hh (σ i))
    (fun i ↦ hphase (σ i)) ht hg hL1 φ.continuous φ.hasCompactSupport (fun _ ↦ φ.nonneg)
    hφs hw hwg
  have htaylor : ∀ x∈Metric.ball (0:Euc n) (1/4),
      |w (normalProjection v x)-f 0-ℓ x|≤D*‖x‖^2 := by
    intro x _
    have h := hTaylor g hg (e.symm (normalProjection v x))
    change ‖w (normalProjection v x)-f 0-ℓ x‖≤C*(∫ y, ‖g y‖)*‖e.symm (normalProjection v x)‖^2 at h
    rw [Real.norm_eq_abs,e.symm.norm_map] at h
    apply h.trans
    dsimp only [D]
    gcongr
    exact (normalPlane v).norm_orthogonalProjectionOnto_apply_le x
  obtain ⟨hb,hflat⟩ := himp (fun i ↦ E (σ i)) (fun i ↦ hmin (σ i)) (fun i ↦ hzero (σ i))
    v φ w φ.continuous φ.hasCompactSupport (fun _ ↦ φ.nonneg)
    (fun y hy ↦ φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)) hw
    (fun i ↦ a (σ i)) (fun i ↦ ha (σ i)) (fun i ↦ hh (σ i)) ℓ (f 0) htaylor htrace
  refine ⟨σ,hσ,ℓ,hℓ.1,?_,hflat⟩
  exact hℓ.2.trans ((hLin g hg).trans (mul_le_mul_of_nonneg_left hgv hM))

end RPISingularHarnack

end

end OAI
