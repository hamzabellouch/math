import Mathlib
import OAI.Geometry.CubicTorus.Regularity.TorusC1Boundary

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma exists_plane_test_cutoff {R : ℝ} (hR : 0<R) {ψ : Plane → ℝ}
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    ∃ b : ContDiffBump (0 : Plane), b.rOut<R ∧ ∀ y, b y*ψ y=ψ y := by
  obtain ⟨s,hsR,hsb⟩ := exists_lt_subset_ball isClosed_closure hs
  let t := max (R/2) s
  have ht : 0<t := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have htR : t<R := max_lt (by linarith) hsR
  let b : ContDiffBump (0 : Plane) := ⟨t,(t+R)/2,ht,by linarith⟩
  refine ⟨b,by change (t+R)/2<R; linarith,fun y ↦ ?_⟩
  by_cases hy : ψ y=0
  · rw [hy,mul_zero]
  · have hym : y∈Metric.closedBall (0 : Plane) b.rIn :=
      Metric.ball_subset_closedBall ((Metric.ball_subset_ball (le_max_right _ _))
        (hsb (subset_tsupport ψ hy)))
    rw [b.one_of_mem_closedBall hym,one_mul]

theorem exists_C1_test_approximants {R : ℝ} (hR : 0<R) {ψ : Plane → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    ∃ (f : ℕ → Plane → ℝ) (K : Set Plane) (M : ℝ), IsCompact K ∧
      K⊆Metric.ball 0 R ∧ 0≤M ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i) ∧ tsupport (f i)⊆K) ∧
      (∀ i y, ‖f i y‖≤M ∧ ‖fderiv ℝ (f i) y‖≤M) ∧
      (∀ y, Tendsto (fun i ↦ f i y) atTop (𝓝 (ψ y))) ∧
      (∀ y, Tendsto (fun i ↦ fderiv ℝ (f i) y) atTop (𝓝 (fderiv ℝ ψ y))) := by
  obtain ⟨b,hbR,hbψ⟩ := exists_plane_test_cutoff hR hs
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hbc : ContDiff ℝ (⊤ : ℕ∞) b := b.contDiff
  obtain ⟨Lb,hLb⟩ := hbc.lipschitzWith_of_hasCompactSupport b.hasCompactSupport (by simp)
  obtain ⟨C,hC⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hCb (y : Plane) : ‖ψ y‖≤C := hC (mem_range_self y)
  have hC0 : 0≤C := (norm_nonneg (ψ 0)).trans (hCb 0)
  let f (i : ℕ) : Plane → ℝ := fun y ↦ b y*graphSmooth (graphMollifier i) ψ y
  have hfs (i : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f i) := b.contDiff.mul (graphSmooth_contDiff _ hL)
  have hsm (i : ℕ) (y : Plane) : ‖graphSmooth (graphMollifier i) ψ y‖≤C := by
    simpa only [zero_add,one_mul,Real.norm_eq_abs] using
      graphSmooth_affine_abs_le (graphMollifier i) hL 0 1 C (by simpa only [zero_add,one_mul,Real.norm_eq_abs] using hCb) y
  have hb1 (y : Plane) : ‖b y‖≤1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg b.nonneg] using b.le_one (x := y)
  have hdf (i : ℕ) (y : Plane) : fderiv ℝ (f i) y =
      b y • fderiv ℝ (graphSmooth (graphMollifier i) ψ) y +
      graphSmooth (graphMollifier i) ψ y • fderiv ℝ b y := by
    exact fderiv_fun_mul (hbc.differentiable (by simp)).differentiableAt
      ((graphSmooth_contDiff _ hL).differentiable (by simp)).differentiableAt
  refine ⟨f,tsupport b,C+(L:ℝ)+C*(Lb:ℝ),b.hasCompactSupport,?_,by positivity,
    fun i ↦ ⟨hfs i,tsupport_mul_subset_left⟩,?_,?_,?_⟩
  · rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball hbR
  · intro i y
    constructor
    · have hh : ‖f i y‖≤C := by
        change ‖b y*graphSmooth (graphMollifier i) ψ y‖≤C
        rw [norm_mul]
        exact (mul_le_mul (hb1 y) (hsm i y) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      nlinarith [Lb.coe_nonneg,L.coe_nonneg]
    · rw [hdf]
      calc
        _ ≤ ‖b y • fderiv ℝ (graphSmooth (graphMollifier i) ψ) y‖+
            ‖graphSmooth (graphMollifier i) ψ y • fderiv ℝ b y‖ := norm_add_le _ _
        _ ≤ (L:ℝ)+C*(Lb:ℝ) := by
          simp only [norm_smul]
          apply add_le_add
          · exact (mul_le_mul (hb1 y) (norm_fderiv_le_of_lipschitz ℝ (graphSmooth_lipschitz _ hL))
              (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
          · exact mul_le_mul (hsm i y) (norm_fderiv_le_of_lipschitz ℝ hLb) (norm_nonneg _) hC0
        _ ≤ _ := by linarith
  · intro y
    simpa only [hbψ y] using (graphSmooth_tendsto hL y).const_mul (b y)
  · intro y
    have he : (fun y ↦ b y*ψ y)=ψ := funext hbψ
    have hdp : fderiv ℝ ψ y=b y • fderiv ℝ ψ y+ψ y • fderiv ℝ b y := by
      conv_lhs => rw [← he]
      exact fderiv_fun_mul (hbc.differentiable (by simp)).differentiableAt
        (hψ.differentiable (by simp)).differentiableAt
    rw [hdp]
    simpa only [hdf] using
      ((graphSmooth_fderiv_tendsto hL (hψ.continuous_fderiv (by simp)).continuousAt).const_smul (b y)).add
        ((graphSmooth_tendsto hL y).smul_const (fderiv ℝ b y))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcFlux_norm_le (p : Plane) : ‖cmcFlux p‖≤‖p‖ := by
  change ‖(cmcWeight p)⁻¹ • p‖≤‖p‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (cmcWeight_pos p).le)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ (cmcWeight_pos p)).mpr (cmcWeight_ge_one p))

lemma cmcFlux_difference_bound {p q : Plane} (hp : ‖p‖≤1) (hq : ‖q‖≤1) :
    ‖cmcFlux q-cmcFlux p‖≤2*‖q-p‖ := by
  apply (convex_closedBall (0 : Plane) (1 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ ↦ (cmcFlux_hasFDerivAt x).differentiableAt) ?_
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hq)
  intro x hx
  rw [(cmcFlux_hasFDerivAt x).fderiv]
  exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (cmcJacobian_norm_le (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx))

lemma cmcFlux_line_deriv (p q : Plane) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ⟪q-p,cmcFlux (p+s • (q-p))⟫)
      ⟪q-p,cmcJacobian (p+t • (q-p)) (q-p)⟫ t := by
  have hl : HasDerivAt (fun s : ℝ ↦ p+s • (q-p)) (q-p) t := by
    simpa using ((hasDerivAt_id t).smul_const (q-p)).const_add p
  have hh := (hasDerivAt_const t (q-p)).inner ℝ ((cmcFlux_hasFDerivAt _).comp_hasDerivAt t hl)
  simpa [Function.comp_def] using hh

lemma cmcFlux_strong_monotone {p q : Plane} (hp : ‖p‖≤1) (hq : ‖q‖≤1) :
    (1/8)*‖q-p‖^2≤⟪q-p,cmcFlux q-cmcFlux p⟫ := by
  let f : ℝ → ℝ := fun t ↦ ⟪q-p,cmcFlux (p+t • (q-p))⟫
  have hf : Differentiable ℝ f := fun t ↦ (cmcFlux_line_deriv p q t).differentiableAt
  have hb (t : ℝ) (ht : t∈interior (Icc (0:ℝ) 1)) :
      (1/8)*‖q-p‖^2≤deriv f t := by
    rw [(cmcFlux_line_deriv p q t).deriv]
    apply cmcJacobian_coercive
    have htt := interior_subset ht
    have he : p+(q-p)=q := by abel
    have hh := (convex_closedBall (0 : Plane) (1 : ℝ)).add_smul_mem (x := p) (y := q-p)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)
      (by simpa only [he,Metric.mem_closedBall,dist_zero_right] using hq) htt
    simpa only [Metric.mem_closedBall,dist_zero_right] using hh
  have hh := (convex_Icc (0:ℝ) 1).mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn
    hf.differentiableOn hb 0 (by norm_num) 1 (by norm_num) (by norm_num)
  have he : p+(q-p)=q := by abel
  simpa only [f,sub_zero,mul_one,one_smul,zero_smul,add_zero,he,inner_sub_right] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_cmc_gradient (g : Plane → ℝ) : Measurable (fun y ↦ cmcFlux (gradient g y)) :=
  cmcFlux_contDiff.continuous.measurable.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g))

lemma measurable_differential_apply {F : Plane → Plane} (hF : Measurable F) (ψ : Plane → ℝ) :
    Measurable (fun y ↦ fderiv ℝ ψ y (F y)) :=
  (continuous_fst.clm_apply continuous_snd).measurable.comp
    ((measurable_fderiv ℝ ψ).prodMk hF)

theorem weak_flux_C1_test {R : ℝ} (hR : 0<R) {F : Plane → Plane}
    (hF : Measurable F) {N : ℝ} (hN : ∀ y, ‖F y‖≤N) (A : ℝ)
    (hw : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ⊆Metric.ball 0 R → (∫ y, fderiv ℝ φ y (F y))=A*(∫ y, φ y))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    (∫ y, fderiv ℝ ψ y (F y))=A*(∫ y, ψ y) := by
  obtain ⟨f,K,M,hK,hKR,hM,hf,hb,ht,hdt⟩ := exists_C1_test_approximants hR hψ hc hs
  have hN0 : 0≤N := (norm_nonneg (F 0)).trans (hN 0)
  let B : Plane → ℝ := K.indicator (fun _ ↦ M*N)
  let C : Plane → ℝ := K.indicator (fun _ ↦ M)
  have hBi : Integrable B := (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have hCi : Integrable C := (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have htd : Tendsto (fun i ↦ ∫ y, fderiv ℝ (f i) y (F y)) atTop
      (𝓝 (∫ y, fderiv ℝ ψ y (F y))) := by
    apply tendsto_integral_of_dominated_convergence B
      (fun _ ↦ (measurable_differential_apply hF _).aestronglyMeasurable) hBi
    · intro i
      filter_upwards [] with y
      by_cases hy : y∈K
      · rw [show B y=M*N from indicator_of_mem hy _]
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hb i y).2 (hN y) (norm_nonneg _) hM)
      · have hz := fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy ((hf i).2 hy'))
        rw [hz,zero_apply,norm_zero,show B y=0 from indicator_of_notMem hy _]
    · apply Eventually.of_forall
      intro y
      exact ((show Continuous (fun L : Plane →L[ℝ] ℝ ↦ L (F y)) from
        continuous_id.clm_apply continuous_const).tendsto _).comp (hdt y)
  have htv : Tendsto (fun i ↦ ∫ y, f i y) atTop (𝓝 (∫ y, ψ y)) := by
    apply tendsto_integral_of_dominated_convergence C
      (fun i ↦ (hf i).1.continuous.aestronglyMeasurable) hCi
    · intro i
      filter_upwards [] with y
      by_cases hy : y∈K
      · rw [show C y=M from indicator_of_mem hy _]
        exact (hb i y).1
      · have hz : f i y=0 := image_eq_zero_of_notMem_tsupport (fun hy' ↦ hy ((hf i).2 hy'))
        rw [hz,norm_zero,show C y=0 from indicator_of_notMem hy _]
    · exact Eventually.of_forall ht
  have he (i : ℕ) : (∫ y, fderiv ℝ (f i) y (F y))=A*(∫ y, f i y) :=
    hw (f i) (hf i).1 (hK.of_isClosed_subset isClosed_closure (hf i).2) ((hf i).2.trans hKR)
  exact tendsto_nhds_unique htd (by simpa only [he] using htv.const_mul A)

theorem WeakCMCGraph.test_C1 {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {H R : ℝ} (hR : 0<R) (hw : WeakCMCGraph g H (Metric.ball 0 R))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    (∫ y, fderiv ℝ ψ y (cmcFlux (gradient g y)))=H*(∫ y, ψ y) := by
  apply weak_flux_C1_test hR (measurable_cmc_gradient g)
    (N := K) (fun y ↦ ?_) H hw hψ hc hs
  exact (cmcFlux_norm_le _).trans (by rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_differential_apply_of_bounded {F : Plane → Plane} (hF : Measurable F)
    {N : ℝ} (hN : ∀ y, ‖F y‖≤N) {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) : Integrable (fun y ↦ fderiv ℝ ψ y (F y)) := by
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hi := (integrableOn_const (μ := (volume : Measure Plane)) (C := (L:ℝ)*N) hc.measure_lt_top.ne).integrable_indicator
    isClosed_closure.measurableSet
  apply hi.mono' (measurable_differential_apply hF ψ).aestronglyMeasurable
  filter_upwards [] with y
  by_cases hy : y∈tsupport ψ
  · rw [indicator_of_mem hy]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) (hN y) (norm_nonneg _) L.coe_nonneg)
  · rw [indicator_of_notMem hy,fderiv_of_notMem_tsupport ℝ hy,zero_apply,norm_zero]

lemma translated_test_support {R r : ℝ} {ψ : Plane → ℝ} {a : Plane}
    (hs : tsupport ψ⊆Metric.ball 0 r) (ha : r+‖a‖≤R) :
    tsupport (fun y ↦ ψ (y-a))⊆Metric.ball 0 R := by
  intro y hy
  have hys := hs (tsupport_comp_subset_preimage ψ (by fun_prop : Continuous (fun y : Plane ↦ y-a)) hy)
  have hh : ‖y-a‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hys
  rw [Metric.mem_ball,dist_zero_right]
  calc
    ‖y‖ = ‖(y-a)+a‖ := by rw [sub_add_cancel]
    _ ≤ ‖y-a‖+‖a‖ := norm_add_le _ _
    _ < r+‖a‖ := by linarith
    _ ≤ R := ha

lemma WeakCMCGraph.translated_test {g : Plane → ℝ} {H R r : ℝ}
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y, fderiv ℝ ψ y (cmcFlux (gradient g (y+a))))=H*(∫ y, ψ y) := by
  let φ : Plane → ℝ := fun y ↦ ψ (y-a)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_id.sub contDiff_const)
  have hφs := translated_test_support hs ha
  have hφc : HasCompactSupport φ := (isCompact_closedBall (0 : Plane) R).of_isClosed_subset
    isClosed_closure (hφs.trans Metric.ball_subset_closedBall)
  have he := hw φ hφ hφc hφs
  have hd := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ fderiv ℝ φ y (cmcFlux (gradient g y))) a
  have hv := integral_add_right_eq_self (μ := (volume : Measure Plane)) φ a
  simp only [φ,fderiv_comp_sub,add_sub_cancel_right] at hd hv
  simp only [φ,fderiv_comp_sub] at he
  rw [hd,he,← hv]

theorem WeakCMCGraph.difference_test {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {H R r : ℝ} (hr : 0<r)
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y, fderiv ℝ ψ y (cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)))=0 := by
  have hF := measurable_cmc_gradient g
  have hb (y : Plane) : ‖cmcFlux (gradient g y)‖≤(K:ℝ) := by
    exact (cmcFlux_norm_le _).trans (by rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg)
  have hFm : Measurable (fun y ↦ cmcFlux (gradient g (y+a))) :=
    hF.comp (measurable_id.add_const a)
  have hDb (y : Plane) : ‖cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)‖≤2*(K:ℝ) :=
    (norm_sub_le _ _).trans (by linarith [hb (y+a),hb y])
  apply weak_flux_C1_test hr (hFm.sub hF) hDb 0 ?_ hψ hc hs |>.trans (by simp)
  intro φ hφ hφc hφs
  change (∫ y, fderiv ℝ φ y (cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)))=0*(∫ y, φ y)
  simp_rw [map_sub]
  rw [integral_sub
    (integrable_differential_apply_of_bounded hFm (fun y ↦ hb (y+a)) (hφ.of_le (by simp)) hφc)
    (integrable_differential_apply_of_bounded hF hb (hφ.of_le (by simp)) hφc)]
  rw [hw.translated_test ha hφ hφs,hw φ hφ hφc (hφs.trans (Metric.ball_subset_ball ?_))]
  · simp
  · linarith [norm_nonneg a]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_C1_cutoff_product {U : Set Plane} (hU : IsOpen U)
    {η w : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hw : ContDiffOn ℝ 1 w U)
    (hs : tsupport η⊆U) : ContDiff ℝ 1 (fun y ↦ η y^2*w y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact (hη.contDiffAt.pow 2).mul ((hw y (hs hy)).contDiffAt (hU.mem_nhds (hs hy)))
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

lemma energyTest_tsupport {η w : Plane → ℝ} : tsupport (fun y ↦ η y^2*w y)⊆tsupport η := by
  apply closure_mono
  intro y hy
  contrapose! hy
  simp only [Function.mem_support,not_not] at hy ⊢
  simp [hy]

lemma integrable_bounded_compact {f : Plane → ℝ} (hf : Measurable f)
    {K : Set Plane} (hK : IsCompact K) {M : ℝ} (hb : ∀ y, ‖f y‖≤M)
    (hz : ∀ y, y∉K → f y=0) : Integrable f := by
  have hi : Integrable (K.indicator (fun _ : Plane ↦ M)) :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  apply hi.mono' hf.aestronglyMeasurable
  filter_upwards [] with y
  by_cases hy : y∈K
  · rw [indicator_of_mem hy]; exact hb y
  · rw [indicator_of_notMem hy,hz y hy,norm_zero]

lemma cmc_energy_absorption {p q : Plane} (hp : ‖p‖≤1) (hq : ‖q‖≤1)
    (a w : ℝ) (L : Plane →L[ℝ] ℝ) :
    (1/16)*a^2*‖q-p‖^2-64*w^2*‖L‖^2 ≤
      a^2*⟪q-p,cmcFlux q-cmcFlux p⟫+2*a*w*L (cmcFlux q-cmcFlux p) := by
  let d := ‖q-p‖
  let F := cmcFlux q-cmcFlux p
  have hc : (1/8)*d^2 ≤ ⟪q-p,F⟫ := cmcFlux_strong_monotone hp hq
  have hF : ‖F‖≤2*d := cmcFlux_difference_bound hp hq
  have hL : |L F|≤2*‖L‖*d := by
    exact (ContinuousLinearMap.le_opNorm L F).trans (by nlinarith [norm_nonneg L])
  have he : |2*a*w*L F|≤4*|a| *|w| *‖L‖*d := by
    rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := mul_le_mul_of_nonneg_left hL (show 0≤2*|a| *|w| by positivity)
    nlinarith
  have hn : -(4*|a| *|w| *‖L‖*d)≤2*a*w*L F := (neg_le_neg he).trans (neg_abs_le _)
  have hca := mul_le_mul_of_nonneg_left hc (sq_nonneg a)
  have hs := sq_nonneg (|a| *d/4-8*|w| *‖L‖)
  have ha2 := sq_abs a
  have hw2 := sq_abs w
  change (1/16)*a^2*d^2-64*w^2*‖L‖^2 ≤ a^2*⟪q-p,F⟫+2*a*w*L F
  nlinarith

lemma translated_difference_contDiffOn {g : Plane → ℝ} {R r : ℝ} {a : Plane}
    (hg : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (ha : r+‖a‖≤R) :
    ContDiffOn ℝ 1 (fun y ↦ g (y+a)-g y) (Metric.ball 0 r) := by
  apply (hg.comp (contDiff_id.add contDiff_const).contDiffOn ?_).sub
    (hg.mono (Metric.ball_subset_ball (by linarith [norm_nonneg a])))
  intro y hy
  rw [Metric.mem_ball,dist_zero_right]
  have hy' : ‖y‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
  change ‖y+a‖<R
  exact (norm_add_le _ _).trans_lt (by linarith)

lemma translated_difference_fderiv {g : Plane → ℝ} {R r : ℝ} {a y : Plane}
    (hg : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (ha : r+‖a‖≤R)
    (hy : y∈Metric.ball 0 r) (v : Plane) :
    fderiv ℝ (fun y ↦ g (y+a)-g y) y v=⟪gradient g (y+a)-gradient g y,v⟫ := by
  have hy0 : y∈Metric.ball (0 : Plane) R := Metric.ball_subset_ball (by linarith [norm_nonneg a]) hy
  have hya : y+a∈Metric.ball (0 : Plane) R := by
    rw [Metric.mem_ball,dist_zero_right]
    have hh : ‖y‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hd := ((hg y hy0).contDiffAt (Metric.isOpen_ball.mem_nhds hy0)).differentiableAt (by simp)
  have hda := ((hg (y+a) hya).contDiffAt (Metric.isOpen_ball.mem_nhds hya)).differentiableAt (by simp)
  have hdc : DifferentiableAt ℝ (fun y ↦ g (y+a)) y :=
    hda.comp y (differentiableAt_id.add_const a)
  change fderiv ℝ ((fun y ↦ g (y+a))-g) y v=_
  rw [fderiv_sub hdc hd,fderiv_comp_add_right,
    sub_apply,inner_sub_left,inner_gradient_left,inner_gradient_left]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmc_linear_energy_absorption {p : Plane} (hp : ‖p‖≤1)
    (q D : Plane) (a w : ℝ) (L : Plane →L[ℝ] ℝ) :
    (1/16)*a^2*‖q‖^2-256*w^2*‖L‖^2-16*a^2*‖D‖^2 ≤
      a^2*⟪q,cmcJacobian p q-D⟫+2*a*w*L (cmcJacobian p q-D) := by
  let F := cmcJacobian p q-D
  have hc : (1/8)*‖q‖^2-‖q‖*‖D‖≤⟪q,F⟫ := by
    dsimp only [F]
    rw [inner_sub_right]
    linarith [cmcJacobian_coercive hp q,real_inner_le_norm q D]
  have hF : ‖F‖≤2*‖q‖+‖D‖ := (norm_sub_le _ _).trans
    (add_le_add (cmcJacobian_norm_le hp q) le_rfl)
  have hL : |L F|≤‖L‖*(2*‖q‖+‖D‖) :=
    (ContinuousLinearMap.le_opNorm L F).trans (mul_le_mul_of_nonneg_left hF (norm_nonneg L))
  have he : |2*a*w*L F|≤2*|a| *|w| *‖L‖*(2*‖q‖+‖D‖) := by
    rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := mul_le_mul_of_nonneg_left hL (show 0≤2*|a| *|w| by positivity)
    nlinarith
  have hn := (neg_le_neg he).trans (neg_abs_le (2*a*w*L F))
  have hca := mul_le_mul_of_nonneg_left hc (sq_nonneg a)
  have hs₁ := sq_nonneg (|a| *‖q‖/4-4*|a| *‖D‖)
  have hs₂ := sq_nonneg (|a| *‖q‖/4-16*|w| *‖L‖)
  have hs₃ := sq_nonneg (|a| *‖D‖-|w| *‖L‖)
  simp only [sub_sq,mul_pow,div_pow,sq_abs] at hs₁ hs₂ hs₃
  ring_nf at hs₁
  simp only [sq_abs] at hs₁
  change (1/16)*a^2*‖q‖^2-256*w^2*‖L‖^2-16*a^2*‖D‖^2 ≤ a^2*⟪q,F⟫+2*a*w*L F
  nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg ‖D‖),mul_nonneg (sq_nonneg w) (sq_nonneg ‖L‖)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma gradient_difference_norm_le {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (y a : Plane) :
    ‖gradient g (y+a)-gradient g y‖≤2*(K:ℝ) := by
  have hb (x : Plane) : ‖gradient g x‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  exact (norm_sub_le _ _).trans (by linarith [hb (y+a),hb y])

lemma height_difference_norm_le {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (y a : Plane) : ‖g (y+a)-g y‖≤(K:ℝ)*‖a‖ := by
  simpa only [dist_eq_norm,add_sub_cancel_left] using hg.dist_le_mul (y+a) y

lemma measurable_plane_gradient (g : Plane → ℝ) : Measurable (gradient g) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)

lemma cmc_cutoff_energies_integrable {g η : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (a : Plane) :
    Integrable (fun y ↦ η y^2*‖gradient g (y+a)-gradient g y‖^2) ∧
    Integrable (fun y ↦ (g (y+a)-g y)^2*‖fderiv ℝ η y‖^2) := by
  obtain ⟨M,hMb⟩ := hη.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hM (y : Plane) : ‖η y‖≤M := hMb (mem_range_self y)
  have hM0 : 0≤M := (norm_nonneg (η 0)).trans (hM 0)
  obtain ⟨D,hD⟩ := hη.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hDη (y : Plane) := norm_fderiv_le_of_lipschitz ℝ hD (x₀ := y)
  have hgrad := measurable_plane_gradient g
  have hgrad' : Measurable (fun y ↦ gradient g (y+a)-gradient g y) :=
    (hgrad.comp (measurable_id.add_const a)).sub hgrad
  constructor
  · apply integrable_bounded_compact (hη.continuous.measurable.pow_const 2 |>.mul (hgrad'.norm.pow_const 2)) hc
      (M := M^2*(2*(K:ℝ))^2)
    · intro y
      dsimp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh : η y^2≤M^2 := by
        simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_pow_left₀ (norm_nonneg _) (hM y) 2)
      exact mul_le_mul hh (pow_le_pow_left₀ (norm_nonneg _) (gradient_difference_norm_le hg y a) 2)
        (sq_nonneg _) (sq_nonneg M)
    · intro y hy
      dsimp only [Pi.mul_apply]
      rw [image_eq_zero_of_notMem_tsupport hy,zero_pow (by norm_num : 2≠0),zero_mul]
  · have hm : Measurable (fun y ↦ g (y+a)-g y) :=
      (hg.continuous.measurable.comp (measurable_id.add_const a)).sub hg.continuous.measurable
    apply integrable_bounded_compact ((hm.pow_const 2).mul ((measurable_fderiv ℝ η).norm.pow_const 2)) hc
      (M := ((K:ℝ)*‖a‖)^2*(D:ℝ)^2)
    · intro y
      dsimp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh : (g (y+a)-g y)^2≤((K:ℝ)*‖a‖)^2 := by
        simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_pow_left₀ (norm_nonneg _) (height_difference_norm_le hg y a) 2)
      exact mul_le_mul hh (pow_le_pow_left₀ (norm_nonneg _) (hDη y) 2)
        (sq_nonneg _) (sq_nonneg _)
    · intro y hy
      dsimp only [Pi.mul_apply]
      rw [fderiv_of_notMem_tsupport ℝ hy,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero]

theorem WeakCMCGraph.caccioppoli {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R r : ℝ}
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (hr : 0<r)
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {η : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hs : tsupport η⊆Metric.ball 0 r) :
    (∫ y, η y^2*‖gradient g (y+a)-gradient g y‖^2) ≤
      1024*(∫ y, (g (y+a)-g y)^2*‖fderiv ℝ η y‖^2) := by
  let w : Plane → ℝ := fun y ↦ g (y+a)-g y
  let F : Plane → Plane := fun y ↦ cmcFlux (gradient g (y+a))-cmcFlux (gradient g y)
  let ψ : Plane → ℝ := fun y ↦ η y^2*w y
  have hwc := translated_difference_contDiffOn hgc ha
  have hψ : ContDiff ℝ 1 ψ := local_C1_cutoff_product Metric.isOpen_ball hη hwc hs
  have hψs : tsupport ψ⊆tsupport η := energyTest_tsupport
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset isClosed_closure hψs
  have heq : (∫ y, fderiv ℝ ψ y (F y))=0 := hw.difference_test hg hr ha hψ hψc (hψs.trans hs)
  have hb (y : Plane) : ‖gradient g y‖≤1 := by
    rw [plane_gradient_norm]; exact (norm_fderiv_le_of_lipschitz ℝ hg).trans hK
  have hFm : Measurable F :=
    ((measurable_cmc_gradient g).comp (measurable_id.add_const a)).sub (measurable_cmc_gradient g)
  have hFb (y : Plane) : ‖F y‖≤4 := by
    exact (cmcFlux_difference_bound (hb y) (hb (y+a))).trans
      (by nlinarith [gradient_difference_norm_le hg y a])
  have hFi := integrable_differential_apply_of_bounded hFm hFb hψ hψc
  obtain ⟨hAi,hBi⟩ := cmc_cutoff_energies_integrable hg hη hc a
  have hpoint (y : Plane) :
      (1/16)*(η y^2*‖gradient g (y+a)-gradient g y‖^2)-
        64*((g (y+a)-g y)^2*‖fderiv ℝ η y‖^2) ≤ fderiv ℝ ψ y (F y) := by
    by_cases hy : y∈tsupport η
    · have hdη := hη.differentiable (by simp) y
      have hdw := ((hwc y (hs hy)).contDiffAt (Metric.isOpen_ball.mem_nhds (hs hy))).differentiableAt (by simp)
      have hd : fderiv ℝ ψ y (F y) =
          η y^2*⟪gradient g (y+a)-gradient g y,F y⟫+2*η y*w y*fderiv ℝ η y (F y) := by
        change fderiv ℝ (fun z ↦ (η^2) z*(g (z+a)-g z)) y (F y)=_
        rw [fderiv_fun_mul (hdη.pow 2) hdw,fderiv_pow 2 hdη]
        change (η y^2 • fderiv ℝ (fun z ↦ g (z+a)-g z) y + (g (y+a)-g y) •
          ((2 • η y^(2-1)) • fderiv ℝ η y)) (F y)=_
        simp only [add_apply,smul_apply,smul_eq_mul,Nat.reduceSub,pow_one,two_smul]
        rw [translated_difference_fderiv hgc ha (hs hy)]
        ring
      rw [hd]
      convert cmc_energy_absorption (hb y) (hb (y+a)) (η y) (w y) (fderiv ℝ η y) using 1
      dsimp only [w,F]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hy,fderiv_of_notMem_tsupport ℝ hy,
        fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hψs h)),zero_apply,norm_zero]
      norm_num
  have hInt := integral_mono ((hAi.const_mul (1/16)).sub (hBi.const_mul 64)) hFi hpoint
  simp only [Pi.sub_apply] at hInt
  rw [integral_sub (hAi.const_mul (1/16)) (hBi.const_mul 64),integral_const_mul,
    integral_const_mul,heq] at hInt
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcJacobian_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcJacobian := by
  have he : cmcJacobian=fderiv ℝ cmcFlux := funext (fun p ↦ (cmcFlux_hasFDerivAt p).fderiv.symm)
  rw [he]
  exact cmcFlux_contDiff.fderiv_right (by simp)

lemma cmcJacobian_symmetric (p v w : Plane) :
    ⟪v,cmcJacobian p w⟫=⟪cmcJacobian p v,w⟫ := by
  simp only [cmcJacobian_apply,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    RCLike.conj_to_real]
  rw [real_inner_comm v p]
  ring

lemma cmcFlux_quadratic_remainder : ∃ L : ℝ, 0≤L ∧ ∀ p q : Plane,
    ‖p‖≤1 → ‖q‖≤1 →
    ‖cmcFlux q-cmcFlux p-cmcJacobian p (q-p)‖≤L*‖q-p‖^2 := by
  obtain ⟨L,hL⟩ := cmcJacobian_contDiff.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : Plane) (1 : ℝ)) (isCompact_closedBall (0 : Plane) (1 : ℝ))
  refine ⟨L,L.coe_nonneg,fun p q hp hq ↦ ?_⟩
  have hp' : p∈Metric.closedBall (0 : Plane) (1 : ℝ) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hp
  have hq' : q∈Metric.closedBall (0 : Plane) (1 : ℝ) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hq
  have hs := (convex_closedBall (0 : Plane) (1 : ℝ)).segment_subset hp' hq'
  let F : Plane → Plane := fun x ↦ cmcFlux x-cmcFlux p-cmcJacobian p (x-p)
  have hd (x : Plane) : HasFDerivAt F (cmcJacobian x-cmcJacobian p) x := by
    exact ((cmcFlux_hasFDerivAt x).sub_const (cmcFlux p)).sub
      ((cmcJacobian p).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p)) |>.congr_fderiv
        (by simp)
  have hb (x : Plane) (hx : x∈segment ℝ p q) :
      ‖cmcJacobian x-cmcJacobian p‖≤(L:ℝ)*‖q-p‖ := by
    exact (hL.norm_sub_le (hs hx) hp').trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hx) L.coe_nonneg)
  have hh := (convex_segment p q).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ ↦ (hd x).hasFDerivWithinAt) hb (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  simpa only [F,sub_self,map_zero,sub_zero,mul_assoc,← pow_two] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def LinearCMCEquation (g : Plane → ℝ) (p B : Plane → Plane) (U : Set Plane) : Prop :=
  ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ⊆U →
    (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (gradient g y)-B y))=0

lemma measurable_plane_clm_apply {A : Plane → Plane →L[ℝ] Plane} {v : Plane → Plane}
    (hA : Measurable A) (hv : Measurable v) : Measurable (fun y ↦ A y (v y)) := by
  have hc : Continuous (fun z : (Plane →L[ℝ] Plane) × Plane ↦ z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  exact hc.measurable.comp (hA.prodMk hv)

lemma linear_cmc_flux_measurable (g : Plane → ℝ) {p B : Plane → Plane}
    (hp : Continuous p) (hB : Continuous B) :
    Measurable (fun y ↦ cmcJacobian (p y) (gradient g y)-B y) :=
  (measurable_plane_clm_apply (cmcJacobian_contDiff.continuous.comp hp).measurable (measurable_plane_gradient g)).sub hB.measurable

lemma linear_cmc_flux_bound {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {p B : Plane → Plane} (hp : ∀ y,‖p y‖≤1) {M : ℝ} (hB : ∀ y,‖B y‖≤M) (y : Plane) :
    ‖cmcJacobian (p y) (gradient g y)-B y‖≤2*(K:ℝ)+M := by
  have hh : ‖gradient g y‖≤(K:ℝ) := by rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  exact (norm_sub_le _ _).trans (add_le_add
    ((cmcJacobian_norm_le (hp y) _).trans (by linarith)) (hB y))

lemma LinearCMCEquation.difference_test {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    (hB : Continuous B) {M : ℝ} (hBb : ∀ y,‖B y‖≤M) {R r : ℝ} (hr : 0<r)
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y,fderiv ℝ ψ y ((cmcJacobian (p (y+a)) (gradient g (y+a))-B (y+a))-
      (cmcJacobian (p y) (gradient g y)-B y)))=0 := by
  let F : Plane → Plane := fun y ↦ cmcJacobian (p y) (gradient g y)-B y
  have hFm : Measurable F := linear_cmc_flux_measurable g hp hB
  have hFb : ∀ y,‖F y‖≤2*(K:ℝ)+M := linear_cmc_flux_bound hg hpb hBb
  have hFt : Measurable (fun y ↦ F (y+a)) := hFm.comp (measurable_id.add_const a)
  have hFdb : ∀ y,‖F (y+a)-F y‖≤2*(2*(K:ℝ)+M) := fun y ↦
    (norm_sub_le _ _).trans (by linarith [hFb (y+a),hFb y])
  apply weak_flux_C1_test hr (hFt.sub hFm) hFdb 0 ?_ hψ hc hs |>.trans (by simp)
  intro φ hφ hφc hφs
  let χ : Plane → ℝ := fun y ↦ φ (y-a)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := hφ.comp (contDiff_id.sub contDiff_const)
  have hχs := translated_test_support hφs ha
  have hχc : HasCompactSupport χ := hφc.comp_homeomorph (Homeomorph.addRight (-a))
  have hχe := hw χ hχ hχc hχs
  have hi := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ fderiv ℝ χ y (F y)) a
  simp only [χ,fderiv_comp_sub,add_sub_cancel_right] at hi
  simp only [χ,fderiv_comp_sub] at hχe
  have ht : (∫ y,fderiv ℝ φ y (F (y+a)))=0 := hi.trans hχe
  have hz := hw φ hφ hφc (hφs.trans (Metric.ball_subset_ball (by linarith [norm_nonneg a])))
  change (∫ y,fderiv ℝ φ y (F (y+a)-F y))=0*(∫ y,φ y)
  simp_rw [map_sub]
  rw [integral_sub
    (integrable_differential_apply_of_bounded hFt (fun y ↦ hFb (y+a)) (hφ.of_le (by simp)) hφc)
    (integrable_differential_apply_of_bounded hFm hFb (hφ.of_le (by simp)) hφc),ht,hz]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma compact_weighted_energy_integrable {η : Plane → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) {D : Plane → Plane} (hD : Measurable D)
    {M : ℝ} (hDb : ∀ y,‖D y‖≤M) : Integrable (fun y ↦ η y^2*‖D y‖^2) := by
  obtain ⟨N,hN⟩ := hη.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hb (y : Plane) : ‖η y‖≤N := hN (mem_range_self y)
  apply integrable_bounded_compact ((hη.measurable.pow_const 2).mul (hD.norm.pow_const 2)) hc
    (M := N^2*M^2)
  · intro y
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hηb : η y^2≤N^2 := by
      simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_pow_left₀ (norm_nonneg _) (hb y) 2)
    exact mul_le_mul hηb (pow_le_pow_left₀ (norm_nonneg _) (hDb y) 2) (sq_nonneg _) (sq_nonneg N)
  · intro y hy
    dsimp only [Pi.mul_apply]
    rw [image_eq_zero_of_notMem_tsupport hy,zero_pow (by norm_num : 2≠0),zero_mul]

theorem LinearCMCEquation.caccioppoli {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    (hB : Continuous B) {M : ℝ} (hBb : ∀ y,‖B y‖≤M) {R r : ℝ}
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (hr : 0<r)
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {η : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hs : tsupport η⊆Metric.ball 0 r) :
    (∫ y,η y^2*‖gradient g (y+a)-gradient g y‖^2) ≤
      4096*(∫ y,(g (y+a)-g y)^2*‖fderiv ℝ η y‖^2)+
      256*(∫ y,η y^2*‖B (y+a)-B y-(cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)‖^2) := by
  let w : Plane → ℝ := fun y ↦ g (y+a)-g y
  let F : Plane → Plane := fun y ↦ (cmcJacobian (p (y+a)) (gradient g (y+a))-B (y+a))-
    (cmcJacobian (p y) (gradient g y)-B y)
  let D : Plane → Plane := fun y ↦ B (y+a)-B y-(cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)
  let ψ : Plane → ℝ := fun y ↦ η y^2*w y
  have hwc := translated_difference_contDiffOn hgc ha
  have hψ : ContDiff ℝ 1 ψ := local_C1_cutoff_product Metric.isOpen_ball hη hwc hs
  have hψs : tsupport ψ⊆tsupport η := energyTest_tsupport
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset isClosed_closure hψs
  have heq : (∫ y,fderiv ℝ ψ y (F y))=0 := hw.difference_test hg hp hpb hB hBb hr ha hψ hψc (hψs.trans hs)
  have hgB (y : Plane) : ‖gradient g y‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hFm₀ := linear_cmc_flux_measurable g hp hB
  have hFm : Measurable F := (hFm₀.comp (measurable_id.add_const a)).sub hFm₀
  have hFb (y : Plane) : ‖F y‖≤2*(2*(K:ℝ)+M) := (norm_sub_le _ _).trans
    (by linarith [linear_cmc_flux_bound hg hpb hBb (y+a),linear_cmc_flux_bound hg hpb hBb y])
  have hFi := integrable_differential_apply_of_bounded hFm hFb hψ hψc
  have hAm := (cmcJacobian_contDiff.continuous.comp hp).measurable
  have hDm : Measurable D := ((hB.measurable.comp (measurable_id.add_const a)).sub hB.measurable).sub
    (measurable_plane_clm_apply ((hAm.comp (measurable_id.add_const a)).sub hAm) (measurable_plane_gradient g))
  have hDb (y : Plane) : ‖D y‖≤2*M+4*(K:ℝ) := by
    dsimp only [D]
    rw [sub_apply]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (by linarith [hBb (y+a),hBb y])) ?_)
    exact (norm_sub_le _ _).trans (by
      linarith [cmcJacobian_norm_le (hpb (y+a)) (gradient g y), cmcJacobian_norm_le (hpb y) (gradient g y), hgB y])
  obtain ⟨hAi,hBi⟩ := cmc_cutoff_energies_integrable hg hη hc a
  have hDi := compact_weighted_energy_integrable hη.continuous hc hDm hDb
  have hFe (y : Plane) : F y=cmcJacobian (p (y+a)) (gradient g (y+a)-gradient g y)-D y := by
    dsimp only [F,D]
    rw [map_sub,sub_apply]
    abel
  have hpoint (y : Plane) :
      (1/16)*(η y^2*‖gradient g (y+a)-gradient g y‖^2)-
        256*((g (y+a)-g y)^2*‖fderiv ℝ η y‖^2)-16*(η y^2*‖D y‖^2) ≤ fderiv ℝ ψ y (F y) := by
    by_cases hy : y∈tsupport η
    · have hdη := hη.differentiable (by simp) y
      have hdw := ((hwc y (hs hy)).contDiffAt (Metric.isOpen_ball.mem_nhds (hs hy))).differentiableAt (by simp)
      have hd : fderiv ℝ ψ y (F y) =
          η y^2*⟪gradient g (y+a)-gradient g y,F y⟫+2*η y*w y*fderiv ℝ η y (F y) := by
        change fderiv ℝ (fun z ↦ (η^2) z*(g (z+a)-g z)) y (F y)=_
        rw [fderiv_fun_mul (hdη.pow 2) hdw,fderiv_pow 2 hdη]
        change (η y^2 • fderiv ℝ (fun z ↦ g (z+a)-g z) y + (g (y+a)-g y) •
          ((2 • η y^(2-1)) • fderiv ℝ η y)) (F y)=_
        simp only [add_apply,smul_apply,smul_eq_mul,Nat.reduceSub,pow_one,two_smul]
        rw [translated_difference_fderiv hgc ha (hs hy)]
        ring
      rw [hd,hFe]
      convert cmc_linear_energy_absorption (hpb (y+a)) (gradient g (y+a)-gradient g y) (D y)
        (η y) (w y) (fderiv ℝ η y) using 1; dsimp only [w]; ring
    · rw [image_eq_zero_of_notMem_tsupport hy,fderiv_of_notMem_tsupport ℝ hy,
        fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hψs h)),zero_apply,norm_zero]
      norm_num
  have hInt := integral_mono (((hAi.const_mul (1/16)).sub (hBi.const_mul 256)).sub (hDi.const_mul 16)) hFi hpoint
  simp only [Pi.sub_apply] at hInt
  have hAB : Integrable (fun y ↦ (1/16)*(η y^2*‖gradient g (y+a)-gradient g y‖^2)-
      256*((g (y+a)-g y)^2*‖fderiv ℝ η y‖^2)) := (hAi.const_mul (1/16)).sub (hBi.const_mul 256)
  rw [integral_sub hAB (hDi.const_mul 16),
    integral_sub (hAi.const_mul (1/16)) (hBi.const_mul 256),integral_const_mul,
    integral_const_mul,integral_const_mul,heq] at hInt
  change _ ≤ 4096*(∫ y,(g (y+a)-g y)^2*‖fderiv ℝ η y‖^2)+256*(∫ y,η y^2*‖D y‖^2)
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma compact_derivative_square_integrable {η : Plane → ℝ}
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    Integrable (fun y ↦ ‖fderiv ℝ η y‖^2) := by
  have hd : Continuous (fderiv ℝ η) := hη.continuous_fderiv (by simp)
  have hdc : HasCompactSupport (fderiv ℝ η) := hc.fderiv ℝ
  have hsc : HasCompactSupport (fun y ↦ ‖fderiv ℝ η y‖^2) := by
    apply hdc.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro y hy
    contrapose! hy
    simp only [Function.mem_support,not_not] at hy ⊢
    simp [hy]
  exact (hd.norm.pow 2).integrable_of_hasCompactSupport hsc

theorem WeakCMCGraph.local_gradient_energy {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : (K:ℝ)≤1) {H R r s : ℝ}
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (hs : 0<s) (hsr : s<r)
    (hw : WeakCMCGraph g H (Metric.ball 0 R)) :
    ∃ C : ℝ, 0≤C ∧ ∀ a : Plane, r+‖a‖≤R →
      (∫ y in Metric.ball 0 s, ‖gradient g (y+a)-gradient g y‖^2)≤C*‖a‖^2 := by
  let b : ContDiffBump (0 : Plane) := ⟨s,(s+r)/2,hs,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 r := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hi := compact_derivative_square_integrable (b.contDiff (n := 1)) b.hasCompactSupport
  let C : ℝ := 1024*(K:ℝ)^2*(∫ y, ‖fderiv ℝ b y‖^2)
  have hC : 0≤C := by
    dsimp only [C]
    exact mul_nonneg (by positivity) (integral_nonneg (fun _ ↦ sq_nonneg _))
  refine ⟨C,hC,fun a ha ↦ ?_⟩
  obtain ⟨hAi,hBi⟩ := cmc_cutoff_energies_integrable hg (b.contDiff (n := 1)) b.hasCompactSupport a
  have hbound : (∫ y, (g (y+a)-g y)^2*‖fderiv ℝ b y‖^2)≤
      ((K:ℝ)*‖a‖)^2*(∫ y, ‖fderiv ℝ b y‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono hBi (hi.const_mul _)
    intro y
    have hh : (g (y+a)-g y)^2≤((K:ℝ)*‖a‖)^2 := by
      simpa only [Real.norm_eq_abs,sq_abs] using
        (pow_le_pow_left₀ (norm_nonneg _) (height_difference_norm_le hg y a) 2)
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖fderiv ℝ b y‖)]
  calc
    (∫ y in Metric.ball 0 s, ‖gradient g (y+a)-gradient g y‖^2) =
        ∫ y in Metric.ball 0 s, b y^2*‖gradient g (y+a)-gradient g y‖^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      dsimp only
      rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
      simp
    _ ≤ ∫ y, b y^2*‖gradient g (y+a)-gradient g y‖^2 :=
      setIntegral_le_integral hAi (ae_of_all _ (fun _ ↦ by positivity))
    _ ≤ 1024*(∫ y, (g (y+a)-g y)^2*‖fderiv ℝ b y‖^2) :=
      hw.caccioppoli hg hK hgc (by linarith) ha b.contDiff b.hasCompactSupport hbs
    _ ≤ 1024*(((K:ℝ)*‖a‖)^2*(∫ y, ‖fderiv ℝ b y‖^2)) := by linarith
    _ = C*‖a‖^2 := by dsimp only [C]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma linear_cmc_difference_source_bound {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} {LA LB : ℝ≥0}
    (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (y a : Plane) :
    ‖B (y+a)-B y-(cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)‖≤
      ((LB:ℝ)+(LA:ℝ)*(K:ℝ))*‖a‖ := by
  have hBA : ‖B (y+a)-B y‖≤(LB:ℝ)*‖a‖ := by
    simpa only [dist_eq_norm,add_sub_cancel_left] using hB.dist_le_mul (y+a) y
  have hAA : ‖cmcJacobian (p (y+a))-cmcJacobian (p y)‖≤(LA:ℝ)*‖a‖ := by
    simpa only [dist_eq_norm,add_sub_cancel_left] using hA.dist_le_mul (y+a) y
  have hgB : ‖gradient g y‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hop := (ContinuousLinearMap.le_opNorm (cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)).trans
    (mul_le_mul hAA hgB (norm_nonneg _) (by positivity))
  exact (norm_sub_le _ _).trans (by nlinarith)

end CubicTorus
end
end
end

end OAI
