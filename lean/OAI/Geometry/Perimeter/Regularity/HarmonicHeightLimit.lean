import OAI.Geometry.Perimeter.Regularity.PlaneHeightResidual

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace ContDiff
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n m : ℕ}

theorem l1_test_pairing_tendsto {f : ℕ → Euc m → ℝ} {g φ : Euc m → ℝ}
    (hf : ∀ i, Integrable (f i) volume) (hg : Integrable g volume)
    (hφ : AEStronglyMeasurable φ volume) {M : ℝ} (hb : ∀ x, ‖φ x‖≤M)
    (hL : Tendsto (fun i ↦ ∫⁻ x, ‖f i x-g x‖ₑ) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, f i x*φ x) atTop (𝓝 (∫ x, g x*φ x)) := by
  apply tendsto_integral_of_L1 _ (hg.aestronglyMeasurable.mul hφ)
    (Eventually.of_forall (fun i ↦ (hf i).mul_bdd hφ (ae_of_all _ hb)))
  have ht : Tendsto (fun i ↦ ENNReal.ofReal M * ∫⁻ x, ‖f i x-g x‖ₑ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hL (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ ↦ zero_le) (fun i ↦ ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  dsimp only [Pi.mul_apply]
  rw [← sub_mul,enorm_mul,mul_comm]
  exact mul_le_mul
    (by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hb x)) le_rfl zero_le zero_le

theorem chartLaplacianTest_tsupport {v : Euc n} (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    (ψ : Euc m → ℝ) : tsupport (chartLaplacianTest e ψ) ⊆ e '' tsupport ψ := by
  intro y hy
  refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
  have hs : tsupport (divergence (gradient ψ)) ⊆ tsupport ψ :=
    (tsupport_divergence_subset _).trans (tsupport_gradient_subset ψ)
  apply hs
  change y ∈ tsupport ((divergence (gradient ψ)) ∘ (e.symm.toHomeomorph : _ → _)) at hy
  rw [tsupport_comp_eq_preimage _ e.symm.toHomeomorph] at hy
  exact hy

theorem minimizing_plane_height_weakHarmonic (hn : 1<n)
    (E : ℕ → Set (Euc n)) (hmin : ∀ i, IsLocallyPerimeterMinimizing (E i))
    {v : Euc n} (hv : ‖v‖=1) (e : Euc m ≃ₗᵢ[ℝ] normalPlane v)
    {η : Euc n → ℝ} (hη : Continuous η) (hbη : ∀ x, ‖η x‖≤1)
    (hsη : HasCompactSupport η) (hηs : Function.support η ⊆ Metric.ball 0 4)
    (hηone : ∀ x ∈ Metric.ball (0:Euc n) 3, η x=1)
    (a : ℕ → ℝ) (ha : ∀ i, 0<a i) (hat : Tendsto a atTop (𝓝 0))
    (hh : ∀ i x, x ∈ perimeterSupport (E i) ∩ Metric.ball 0 4 → |inner ℝ v x|≤a i)
    (hphase : ∀ i, ∀ᵐ x ∂volume, x ∈ Metric.ball 0 4 → a i < |inner ℝ v x| →
      (x ∈ E i ↔ inner ℝ v x<0))
    {P : ℝ} (hper : ∀ i, (perimeter (E i) (Metric.ball 0 4)).toReal≤P)
    (htilt : Tendsto (fun i ↦ orientedTilt (E i) v (Metric.ball 0 4)) atTop (𝓝 0))
    {g : Euc m → ℝ} (hg : Integrable g volume)
    (hL : Tendsto (fun i ↦ ∫⁻ y, ‖chartFiber v e (a i) (cutoffPhaseError (E i) v η) y-g y‖ₑ)
      atTop (𝓝 0)) : WeakHarmonicOn g (Metric.ball 0 1) := by
  intro ψ hψ hcψ hsψ
  let χ : ContDiffBump (0:ℝ) := ⟨1/2,1,by norm_num,by norm_num⟩
  have hχone : ∀ s : ℝ, |s|<1/2 → χ s=1 := by
    intro s hs
    exact χ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] using hs.le)
  have hcΔ : HasCompactSupport (divergence (gradient ψ)) :=
    hcψ.of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_divergence_subset _).trans (tsupport_gradient_subset ψ))
  obtain ⟨M,hM⟩ := hcΔ.exists_bound_of_continuous (continuous_divergence (gradient_contDiff hψ))
  have hM0 : 0≤M := (norm_nonneg (divergence (gradient ψ) 0)).trans (hM 0)
  have hsm := planeWindowLift_contDiff e hψ χ.contDiff
  obtain ⟨K₀,hK₀⟩ := (isCompact_closedBall (0:Euc n) 4).exists_bound_of_continuousOn
    ((gradient_contDiff hsm).continuous_fderiv (by simp)).continuousOn
  let K := max K₀ 0
  have hK : 0≤K := le_max_right _ _
  have hd : ∀ x ∈ Metric.ball (0:Euc n) 4,
      ‖fderiv ℝ (gradient (planeWindowLift e ψ χ)) x‖≤K := by
    intro x hx
    exact (hK₀ x (Metric.ball_subset_closedBall hx)).trans (le_max_left _ _)
  have hs : tsupport (planeWindowLift e ψ χ) ⊆ Metric.ball 0 4 := by
    apply (planeWindowLift_tsupport hv e ψ χ
      ((subset_closure.trans hsψ).trans Metric.ball_subset_closedBall) ?_).trans
      (Metric.closedBall_subset_ball (by norm_num : (1:ℝ)+1<4))
    simpa only [χ.support_eq] using (Metric.ball_subset_closedBall : Metric.ball (0:ℝ) 1 ⊆ Metric.closedBall 0 1)
  have hsmall : ∀ᶠ i in atTop, a i<1/8 := hat.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8))
  have hr : ∀ᶠ i in atTop,
      |∫ y, chartFiber v e (a i) (cutoffPhaseError (E i) v η) y * divergence (gradient ψ) y| ≤
        2*K*(Real.sqrt (orientedTilt (E i) v (Metric.ball 0 4))*Real.sqrt P)+
        M*orientedTilt (E i) v (Metric.ball 0 4) := by
    filter_upwards [hsmall] with i hi
    have hai := ha i
    have hri := minimizing_chart_height_residual hn (hmin i) hv e (ha i)
      (b := 2*a i) (δ := a i/2) (b₀ := 1/2) (by positivity) (by linarith [ha i])
      (by linarith) (by norm_num) hηs hψ hcψ χ.contDiff χ.hasCompactSupport hχone
      (fun y hy s hs ↦ hηone _ (by
        have hy' := chartLaplacianTest_tsupport e ψ hy
        obtain ⟨z,hz,rfl⟩ := hy'
        have hz' := hsψ hz
        rw [Metric.mem_ball,dist_zero_right] at hz' ⊢
        have ht := norm_add_le (e z:Euc n) (s•v)
        rw [norm_smul,hv,mul_one] at ht
        change ‖(e z:Euc n)+s•v‖≤‖e z‖+‖s‖ at ht
        rw [e.norm_map,Real.norm_eq_abs] at ht
        linarith))
      (fun y hy ↦ by
        obtain ⟨z,hz,rfl⟩ := chartLaplacianTest_tsupport e ψ hy
        have hz' := hsψ hz
        rw [Metric.mem_ball,dist_zero_right] at hz'
        rw [e.norm_map]
        linarith) hs hM hK hd (hh i) (hphase i)
    have hdiv : M*(2*a i)/(2*a i)=M := by field_simp [ne_of_gt hai]
    rw [hdiv] at hri
    apply hri.trans
    gcongr
    exact hper i
  have ht : Tendsto (fun i ↦ 2*K*(Real.sqrt (orientedTilt (E i) v (Metric.ball 0 4))*Real.sqrt P)+
      M*orientedTilt (E i) v (Metric.ball 0 4)) atTop (𝓝 0) := by
    simpa using (((Real.continuous_sqrt.tendsto 0).comp htilt).mul_const (Real.sqrt P)).const_mul
      (2*K) |>.add (htilt.const_mul M)
  have hz : Tendsto (fun i ↦ ∫ y, chartFiber v e (a i) (cutoffPhaseError (E i) v η) y *
      divergence (gradient ψ) y) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) hr ht
  have hf (i) : Integrable (cutoffPhaseError (E i) v η) volume := by
    apply (integrableOn_iff_integrable_of_support_subset
      ((cutoffPhaseError_support (E i) v η).trans (subset_tsupport η))).mp
    have : Fact (volume (tsupport η) < (∞ : ℝ≥0∞)) := ⟨hsη.measure_lt_top⟩
    refine ⟨(cutoffPhaseError_measurable (hmin i).1 v hη.measurable).aestronglyMeasurable.restrict, ?_⟩
    apply HasFiniteIntegral.of_bounded (C := 1)
    apply ae_of_all
    intro x
    dsimp only [cutoffPhaseError]
    rw [norm_mul]
    have hb : ‖(E i).indicator (fun _ ↦ (1:ℝ)) x - {z | inner ℝ v z<0}.indicator (fun _ ↦ (1:ℝ)) x‖≤1 := by
      by_cases he : x∈E i <;> by_cases hh : inner ℝ v x<0 <;> simp [he,hh]
    exact (mul_le_mul (hbη x) hb (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have htpair := l1_test_pairing_tendsto (fun i ↦ chartFiber_integrable (hf i) hv e (a i)) hg
    (continuous_divergence (gradient_contDiff hψ)).aestronglyMeasurable hM hL
  exact tendsto_nhds_unique htpair hz

end RPISingularHarnack

end

end OAI
