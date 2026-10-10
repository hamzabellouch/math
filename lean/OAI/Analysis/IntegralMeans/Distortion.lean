import OAI.Analysis.IntegralMeans.UnivalentArea

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma polar_symm_eq_circleMap (r θ : ℝ) :
    Complex.polarCoord.symm (r,θ) = circleMap 0 r θ := by
  rw [Complex.polarCoord_symm_apply, circleMap, zero_add]
  congr 1
  rw [Complex.exp_mul_I]
  simp

lemma circleAverage_eq_integral_neg_pi (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Real.circleAverage f c r =
      (2*Real.pi)⁻¹ • ∫ θ in -Real.pi..Real.pi, f (circleMap c r θ) := by
  rw [Real.circleAverage_eq_integral_add (-Real.pi)]
  rw [intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c r θ))]
  congr 2 <;> ring

lemma integral_ball_polar {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (Metric.closedBall 0 R)) :
    ∫ z in Metric.ball (0 : ℂ) R, f z =
      ∫ r in (0 : ℝ)..R, (2*Real.pi*r) • Real.circleAverage f 0 r := by
  let g : ℝ × ℝ → ℂ := fun p => p.1 • f (Complex.polarCoord.symm p)
  have hg : IntegrableOn g (Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi) := by
    refine (show IntegrableOn g (Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi) from ?_).mono_set ?_
    · apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hpolar : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
        simp only [Complex.polarCoord_symm_apply]
        fun_prop
      apply continuousOn_fst.smul (hf.comp hpolar.continuousOn ?_)
      intro p hp
      simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm]
      exact (abs_of_nonneg hp.1.1).trans_le hp.1.2
    · exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  calc
    _ = ∫ p in polarCoord.target,
        p.1 • (Metric.ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p) := by
      rw [Complex.integral_comp_polarCoord_symm,
        integral_indicator Metric.isOpen_ball.measurableSet]
    _ = ∫ p in Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi, g p := by
      rw [polarCoord_target]
      have heq : (fun p : ℝ × ℝ => p.1 •
          (Metric.ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p)) =ᶠ[
          ae (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi))]
        (Iio R ×ˢ (univ : Set ℝ)).indicator g := by
        filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
        have hp0 : 0 < p.1 := hp.1
        have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm,abs_of_pos hp0]
        by_cases hr : p.1 < R
        · rw [indicator_of_mem (by simpa [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos hp0] using hr),
            indicator_of_mem (show p ∈ Iio R ×ˢ (univ : Set ℝ) from ⟨hr,mem_univ _⟩)]
        · rw [indicator_of_notMem (by simpa [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos hp0] using hr),
            indicator_of_notMem (show p ∉ Iio R ×ˢ (univ : Set ℝ) from fun h => hr h.1),smul_zero]
      rw [integral_congr_ae heq,
        integral_indicator (measurableSet_Iio.prod MeasurableSet.univ)]
      rw [Measure.restrict_restrict (measurableSet_Iio.prod MeasurableSet.univ)]
      congr 2
      ext p
      simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Iio, mem_Ioo, mem_univ, and_true]
      tauto
    _ = ∫ r in Ioo (0 : ℝ) R, ∫ θ in Ioo (-Real.pi) Real.pi, g (r,θ) := by
      exact setIntegral_prod _ (by simpa only [← Measure.volume_eq_prod] using hg)
    _ = ∫ r in (0 : ℝ)..R, (2*Real.pi*r) • Real.circleAverage f 0 r := by
      rw [intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp only
      rw [circleAverage_eq_integral_neg_pi,
        intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
        integral_Ioc_eq_integral_Ioo, ← smul_assoc]
      have he : (2*Real.pi*r) * (2*Real.pi)⁻¹ = r := by
        field_simp
      rw [smul_eq_mul, he, ← integral_smul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ hθ
      simp only [g, polar_symm_eq_circleMap]

lemma ball_closedBall_ae_eq (r : ℝ) :
    Metric.ball (0 : ℂ) r =ᵐ[volume] Metric.closedBall 0 r := by
  apply ae_eq_set.mpr
  constructor
  · rw [sdiff_eq_empty.mpr Metric.ball_subset_closedBall,measure_empty]
  · rw [Metric.closedBall_sdiff_ball]
    exact Measure.addHaar_sphere volume 0 r

lemma integral_ball_holomorphic {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (hr : 0 < r) (hrR : r < R) :
    ∫ z in Metric.ball (0 : ℂ) r, f z = volume.real (Metric.ball (0 : ℂ) r) • f 0 := by
  have hfc : ContinuousOn f (Metric.closedBall 0 r) :=
    hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  rw [integral_ball_polar hr hfc]
  have hm (t : ℝ) (ht : t ∈ Ioo 0 r) : Real.circleAverage f 0 t = f 0 := by
    apply DiffContOnCl.circleAverage
    rw [abs_of_pos ht.1]
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 ht.1.ne']
    exact hf.mono (Metric.closedBall_subset_ball (ht.2.trans hrR))
  have hc := integral_ball_polar (f := fun _ : ℂ => f 0) hr continuousOn_const
  rw [setIntegral_const] at hc
  rw [hc]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hr.le] at ht
  by_cases ht0 : t = 0
  · simp [ht0]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have ht' : t ∈ Ioo 0 r ∨ t = r := by
    exact (lt_or_eq_of_le ht.2).elim (fun h => Or.inl ⟨htpos,h⟩) Or.inr
  have hmf : Real.circleAverage f 0 t = f 0 := by
    rcases ht' with ht' | rfl
    · exact hm t ht'
    · apply DiffContOnCl.circleAverage
      rw [abs_of_pos hr]
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball 0 hr.ne']
      exact hf.mono (Metric.closedBall_subset_ball hrR)
  simp only [hmf,Real.circleAverage_const]

lemma integral_closedBall_holomorphic {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (hr : 0 < r) (hrR : r < R) :
    ∫ z in Metric.closedBall (0 : ℂ) r, f z =
      volume.real (Metric.closedBall (0 : ℂ) r) • f 0 := by
  rw [← setIntegral_congr_set (ball_closedBall_ae_eq r),
    integral_ball_holomorphic hf hr hrR]
  congr 1
  exact congrArg ENNReal.toReal (measure_congr (ball_closedBall_ae_eq r))

lemma holomorphic_sq_submean {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (hr : 0 < r) (hrR : r < R) :
    volume.real (Metric.closedBall (0 : ℂ) r) * ‖f 0‖^2 ≤
      ∫ z in Metric.closedBall (0 : ℂ) r, ‖f z‖^2 := by
  let K : Set ℂ := Metric.closedBall 0 r
  have hfc : ContinuousOn f K := hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  have hfi : IntegrableOn f K := hfc.integrableOn_compact (isCompact_closedBall 0 r)
  have hf2i : IntegrableOn (fun z => ‖f z‖^2) K :=
    (hfc.norm.pow 2).integrableOn_compact (isCompact_closedBall 0 r)
  have hconst : IntegrableOn (fun _ : ℂ => ‖f 0‖^2) K :=
    integrableOn_const (isCompact_closedBall 0 r).measure_ne_top
  have hnonneg : 0 ≤ ∫ z in K, ‖f z-f 0‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have he : (fun z => ‖f z-f 0‖^2) =
      (fun z => ‖f z‖^2-2*inner ℝ (f 0) (f z)+‖f 0‖^2) := by
    funext z
    rw [norm_sub_sq_real,real_inner_comm]
  have hsub : IntegrableOn (fun z => ‖f z‖^2-2*inner ℝ (f 0) (f z)) K :=
    hf2i.sub ((hfi.const_inner (f 0)).const_mul 2)
  have hinner : IntegrableOn (fun z => 2*inner ℝ (f 0) (f z)) K :=
    (hfi.const_inner (f 0)).const_mul 2
  rw [he,integral_add hsub hconst,
    integral_sub hf2i hinner,
    integral_const_mul,integral_inner hfi,setIntegral_const,
    integral_closedBall_holomorphic hf hr hrR,real_inner_smul_right,
    real_inner_self_eq_norm_sq,smul_eq_mul] at hnonneg
  dsimp only [K] at hnonneg ⊢
  linarith

lemma meromorphic_univalent_coefficient {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹+h z)
    (hHd : ∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0}, deriv H z ≠ 0)
    (hHi : InjOn H (Metric.ball 0 1 \ {0})) : ‖deriv h 0‖ ≤ 1 := by
  have hb (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : ‖deriv h 0‖^2 ≤ (r^2)⁻¹^2 := by
    have hM : 0 < volume.real (Metric.closedBall (0 : ℂ) r) := by
      rw [measureReal_def,Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hr.le,ENNReal.coe_toReal]
      exact mul_pos (sq_pos_of_pos hr) Real.pi_pos
    have hle := (holomorphic_sq_submean (hh.deriv Metric.isOpen_ball) hr hr1).trans
      (meromorphic_univalent_area hh hH hdef hHd hHi hr hr1)
    nlinarith
  have ht : Tendsto (fun r : ℝ => (r^2)⁻¹^2) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun r : ℝ => (r^2)⁻¹^2) 1 :=
      ((continuousAt_id.pow 2).inv₀ (by norm_num)).pow 2
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsq : ‖deriv h 0‖^2 ≤ 1 := by
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r from
        nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ)<1)))] with r hr1 hr
    exact hb r hr hr1
  nlinarith [norm_nonneg (deriv h 0)]

lemma nonconstant_germ_of_injOn {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : Set.InjOn f U) {a : ℂ} (ha : a ∈ U) :
    ¬ ∀ᶠ z in 𝓝 a, f z = f a := by
  intro hc
  have heq : ∀ᶠ z in 𝓝 a, z = a := by
    filter_upwards [hc, hU.mem_nhds ha] with z hz hzU
    exact hf hzU ha hz
  have heq' : ∀ᶠ z in 𝓝[≠] a, z = a := heq.filter_mono nhdsWithin_le_nhds
  have hne' : ∀ᶠ z in 𝓝[≠] a, z ≠ a := self_mem_nhdsWithin
  obtain ⟨z, hz, hne⟩ := (heq'.and hne').exists
  exact hne hz

lemma univalent_inverse_continuousAt {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    ContinuousAt (Function.invFunOn f U) (f a) := by
  have haan : AnalyticAt ℂ f a := (hf.1.analyticOnNhd hU) a ha
  have hopen : 𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    haan.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (nonconstant_germ_of_injOn hU hf.2 ha)
  have hl : ∀ᶠ z in 𝓝 a, Function.invFunOn f U (f z) = z := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hf.2.leftInvOn_invFunOn hz
  have ht : Tendsto (Function.invFunOn f U ∘ f) (𝓝 a) (𝓝 a) :=
    tendsto_id.congr' (Filter.EventuallyEq.symm hl)
  rw [ContinuousAt, hf.2.leftInvOn_invFunOn ha]
  exact (tendsto_map'_iff.mpr ht).mono_left hopen

lemma univalent_deriv_ne_zero {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  have han : AnalyticAt ℂ f a := hf.1.analyticOnNhd hU a ha
  have hd_nonconst : ¬ ∀ᶠ z in 𝓝 a, deriv f z = 0 := by
    intro hc
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hc.and (hU.mem_nhds ha))
    have hfball : DifferentiableOn ℂ f (Metric.ball a r) :=
      hf.1.mono (fun z hz => (hball hz).2)
    have hcball : ∀ z ∈ Metric.ball a r, f z = f a := by
      intro z hz
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball a r).isPreconnected
        hfball (fun w hw => (hball hw).1) hz (Metric.mem_ball_self hr)
    apply nonconstant_germ_of_injOn hU hf.2 ha
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz
    exact hcball z hz
  have hd : ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 :=
    han.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left hd_nonconst
  let g := Function.invFunOn f U
  have hgc : ContinuousAt g (f a) := univalent_inverse_continuousAt hU hf ha
  have hga : g (f a) = a := hf.2.leftInvOn_invFunOn ha
  have hopen : 𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    han.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (nonconstant_germ_of_injOn hU hf.2 ha)
  have hright : ∀ᶠ w in 𝓝 (f a), g w ∈ U ∧ f (g w) = w := by
    apply (hopen (Filter.mem_map.mpr ?_))
    filter_upwards [hU.mem_nhds ha] with z hz
    exact ⟨Function.invFunOn_apply_mem hz, Function.invFunOn_apply_eq hz⟩
  have hgne : ∀ᶠ w in 𝓝[≠] (f a), g w ≠ a := by
    filter_upwards [hright.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with w hw hwne
    intro heq
    exact hwne (hw.2.symm.trans (congrArg f heq))
  have hgt : Tendsto g (𝓝[≠] (f a)) (𝓝[≠] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hgne⟩
    simpa only [hga] using (hgc.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto g (𝓝[≠] (f a)) (𝓝 (g (f a))))
  have hgd : ∀ᶠ w in 𝓝[≠] (f a), DifferentiableAt ℂ g w := by
    filter_upwards [hgt.eventually hd, hright.filter_mono nhdsWithin_le_nhds]
      with w hwder hw
    have hwan : AnalyticAt ℂ f (g w) := hf.1.analyticOnNhd hU (g w) hw.1
    have hws : HasStrictDerivAt f (deriv f (g w)) (g w) :=
      (hwan.contDiffAt (n := 1)).hasStrictDerivAt (by norm_num)
    have hl : ∀ᶠ z in 𝓝 (g w), g (f z) = z := by
      filter_upwards [hU.mem_nhds hw.1] with z hz
      exact hf.2.leftInvOn_invFunOn hz
    simpa [hw.2] using (hws.to_local_left_inverse hwder hl).hasDerivAt.differentiableAt
  have hgan := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hgd hgc
  have hcomp := hgan.differentiableAt.hasDerivAt.comp a han.differentiableAt.hasDerivAt
  have hid : (fun z => g (f z)) =ᶠ[𝓝 a] id := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hf.2.leftInvOn_invFunOn hz
  have hprod : deriv g (f a) * deriv f a = 1 := by
    simpa using (hcomp.congr_of_eventuallyEq hid.symm).unique (hasDerivAt_id a)
  intro hzero
  simp [hzero] at hprod

lemma differentiableAt_of_continuous_root {q F : ℂ → ℂ} {z : ℂ}
    (hq : ContinuousAt q z) (hF : DifferentiableAt ℂ F z)
    (hroot : (fun w => q w^2) =ᶠ[𝓝 z] F) (hq0 : q z ≠ 0) :
    DifferentiableAt ℂ q z := by
  have hp : HasStrictDerivAt (fun w : ℂ => w^2) (2*q z) (q z) := by
    have hp := (hasStrictDerivAt_id (q z)).pow 2
    change HasStrictDerivAt (fun w : ℂ => w^2) _ (q z) at hp
    simpa only [id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one] using hp
  have hn : 2*q z ≠ 0 := mul_ne_zero (by norm_num) hq0
  let p := hp.localInverse _ _ _ hn
  have hpD : DifferentiableAt ℂ p (F z) := by
    rw [← hroot.self_of_nhds]
    exact (hp.to_localInverse hn).hasDerivAt.differentiableAt
  have he : q =ᶠ[𝓝 z] fun w => p (F w) := by
    filter_upwards [hq.tendsto.eventually (hp.eventually_left_inverse hn),hroot] with w hw hwF
    exact (hwF ▸ hw).symm
  exact (hpD.comp z hF).congr_of_eventuallyEq he

lemma exists_holomorphic_sqrt_disk {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F disk) (hF0 : ∀ z ∈ disk, F z ≠ 0)
    (hFone : F 0 = 1) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q disk ∧ q 0 = 1 ∧
      (∀ z ∈ disk, q z^2 = F z) ∧ ∀ z ∈ disk, q z ≠ 0 := by
  have hdz : (0 : ℂ) ∈ disk := by simp [disk]
  have hsim : IsSimplyConnected disk := by
    have : ContractibleSpace disk := (convex_ball (0 : ℂ) (1 : ℝ)).contractibleSpace ⟨0,hdz⟩
    change SimplyConnectedSpace disk
    exact inferInstance
  obtain ⟨q,hqc,hq⟩ := Complex.exists_continuousOn_pow_eq hsim Metric.isOpen_ball hF.continuousOn
    (by rintro ⟨z,hz,he⟩;exact hF0 z hz he) (n := 2) (by norm_num)
  have hqn (z) (hz : z ∈ disk) : q z ≠ 0 := by
    intro he
    have := hq z
    rw [he,zero_pow (by norm_num)] at this
    exact hF0 z hz this.symm
  have hqd : DifferentiableOn ℂ q disk := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_of_continuous_root
      (hqc.continuousAt (Metric.isOpen_ball.mem_nhds hz))
      ((hF z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz))
      (Filter.Eventually.of_forall hq) (hqn z hz)
  let Q : ℂ → ℂ := fun z => q z / q 0
  refine ⟨Q,hqd.div_const _,by simp [Q,hqn 0 hdz],?_,?_⟩
  · intro z hz
    simp only [Q,div_pow,hq,hFone,div_one]
  · intro z hz
    exact div_ne_zero (hqn z hz) (hqn 0 hdz)

lemma dslope_factor (f : ℂ → ℂ) (z : ℂ) :
    z * dslope f 0 z = f z-f 0 := by
  simpa only [sub_zero,smul_eq_mul] using sub_smul_dslope f 0 z

lemma sq_mem_disk {z : ℂ} (hz : z ∈ disk) : z^2 ∈ disk := by
  have hn : ‖z‖ < 1 := by simpa [disk] using hz
  simpa [disk] using pow_lt_one₀ (norm_nonneg z) hn (by norm_num : 2 ≠ 0)

lemma exists_odd_transform {f : ℂ → ℂ} (hf : Schlicht f) :
    ∃ q g h H : ℂ → ℂ,
      DifferentiableOn ℂ q disk ∧ q 0 = 1 ∧
      (∀ z ∈ disk, q z ≠ 0) ∧
      (∀ z ∈ disk, q z^2 = dslope f 0 z) ∧
      (∀ z, g z = z*q (z^2)) ∧
      UnivalentOn g disk ∧ g 0 = 0 ∧
      DifferentiableOn ℂ h disk ∧ deriv h 0 = -deriv q 0 ∧
      (∀ z ∈ disk, z ≠ 0 → H z = z⁻¹+h z) ∧
      UnivalentOn H (disk \ {0}) ∧
      deriv (deriv f) 0 = 4*deriv q 0 := by
  have hdz : (0 : ℂ) ∈ disk := by simp [disk]
  let F := dslope f 0
  have hFd : DifferentiableOn ℂ F disk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hdz)).mpr hf.1.1
  have hFn (z) (hz : z ∈ disk) : F z ≠ 0 := by
    by_cases hz0 : z = 0
    · simpa [F,hz0] using (show deriv f 0 ≠ 0 by rw [hf.2.2];norm_num)
    · intro he
      have hfact := dslope_factor f z
      change z*F z = f z-f 0 at hfact
      rw [he,mul_zero] at hfact
      exact hz0 (hf.1.2 hz hdz (sub_eq_zero.mp hfact.symm))
  obtain ⟨q,hqd,hq0,hqs,hqn⟩ := exists_holomorphic_sqrt_disk hFd hFn (by simpa [F] using hf.2.2)
  let Q := dslope q 0
  have hQd : DifferentiableOn ℂ Q disk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hdz)).mpr hqd
  let g : ℂ → ℂ := fun z => z*q (z^2)
  let h : ℂ → ℂ := fun z => -z*Q (z^2)/q (z^2)
  let H : ℂ → ℂ := fun z => (g z)⁻¹
  have hgd : DifferentiableOn ℂ g disk := by
    exact differentiableOn_id.mul (hqd.comp (differentiableOn_id.pow 2) (fun z hz => sq_mem_disk hz))
  have hgs (z) (hz : z ∈ disk) : g z^2 = f (z^2) := by
    dsimp only [g]
    rw [mul_pow,hqs _ (sq_mem_disk hz)]
    simpa [F,hf.2.1] using dslope_factor f (z^2)
  have hgn (z) (hz : z ∈ disk) (hz0 : z ≠ 0) : g z ≠ 0 :=
    mul_ne_zero hz0 (hqn _ (sq_mem_disk hz))
  have hgi : InjOn g disk := by
    intro z hz w hw he
    have hsq : z^2 = w^2 := hf.1.2 (sq_mem_disk hz) (sq_mem_disk hw)
      ((hgs z hz).symm.trans ((congrArg (fun t => t^2) he).trans (hgs w hw)))
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
    · exact heq
    · have hgneg : g z = -g w := by simp [g,heq]
      have hw0 : w = 0 := by
        by_contra hn
        exact hgn w hw hn (by linear_combination (he.symm+hgneg)/2)
      simpa [hw0] using heq
  have hhd : DifferentiableOn ℂ h disk := by
    exact (differentiableOn_id.neg.mul
      (hQd.comp (differentiableOn_id.pow 2) (fun z hz => sq_mem_disk hz))).div
      (hqd.comp (differentiableOn_id.pow 2) (fun z hz => sq_mem_disk hz))
      (fun z hz => hqn _ (sq_mem_disk hz))
  have hderh : deriv h 0 = -deriv q 0 := by
    have hqd0 := ((hqd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt
    have hQd0 := ((hQd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt
    have hp : HasDerivAt (fun z : ℂ => z^2) 0 0 := by
      have hp := (hasDerivAt_id (0 : ℂ)).pow 2
      change HasDerivAt (fun z : ℂ => z^2) _ 0 at hp
      simpa only [id_eq,Nat.reduceSub,pow_one,Nat.cast_ofNat,mul_one,mul_zero] using hp
    have hQcomp : HasDerivAt (fun z : ℂ => Q (z^2)) 0 0 := by
      have hQd0' : HasDerivAt Q (deriv Q 0) ((0 : ℂ)^2) := by simpa using hQd0
      convert hQd0'.comp (h := fun z : ℂ => z^2) 0 hp using 1 <;> first | rfl | simp
    have hqcomp : HasDerivAt (fun z : ℂ => q (z^2)) 0 0 := by
      have hqd0' : HasDerivAt q (deriv q 0) ((0 : ℂ)^2) := by simpa using hqd0
      convert hqd0'.comp (h := fun z : ℂ => z^2) 0 hp using 1 <;> first | rfl | simp
    have hD := ((hasDerivAt_id (0 : ℂ)).neg.mul hQcomp).div hqcomp
      (by simpa using hqn 0 hdz)
    change HasDerivAt h _ 0 at hD
    simpa [Q,hq0] using hD.deriv
  have hdef (z) (hz : z ∈ disk) (hz0 : z ≠ 0) : H z = z⁻¹+h z := by
    have hfact := dslope_factor q (z^2)
    rw [hq0] at hfact
    change z^2 * Q (z^2) = q (z^2)-1 at hfact
    dsimp only [H,g,h]
    field_simp [hz0,hqn _ (sq_mem_disk hz)]
    linear_combination hfact
  have hHu : UnivalentOn H (disk \ {0}) := by
    refine ⟨(hgd.mono sdiff_subset).inv (fun z hz => hgn z hz.1 hz.2),?_⟩
    intro z hz w hw he
    exact hgi hz.1 hw.1 (inv_inj.mp he)
  have hFq : deriv F 0 = 2*deriv q 0 := by
    have hD := (((hqd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt).pow 2
    have he : (fun z => q z^2) =ᶠ[𝓝 (0 : ℂ)] F := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hdz] with z hz
      exact hqs z hz
    have := (hD.congr_of_eventuallyEq he.symm).deriv
    simpa [hq0] using this
  have hff : deriv (deriv f) 0 = 2*deriv F 0 := by
    have hidentity : f = fun z => z*F z := by
      funext z
      simpa [hf.2.1,F] using (dslope_factor f z).symm
    have he : deriv f =ᶠ[𝓝 (0 : ℂ)] fun z => F z+z*deriv F z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hdz] with z hz
      have hD := (hasDerivAt_id z).mul
        (((hFd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt)
      rw [hidentity]
      change HasDerivAt (fun w => w*F w) _ z at hD
      simpa using hD.deriv
    have hD := (((hFd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt).add
      ((hasDerivAt_id (0 : ℂ)).mul
        (((hFd.deriv Metric.isOpen_ball 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt))
    have := (hD.congr_of_eventuallyEq he).deriv
    simpa [two_mul] using this
  refine ⟨q,g,h,H,hqd,hq0,hqn,hqs,fun _ => rfl,⟨hgd,hgi⟩,by simp [g],hhd,hderh,hdef,hHu,?_⟩
  rw [hff,hFq]
  ring

lemma schlicht_second_deriv_bound {f : ℂ → ℂ} (hf : Schlicht f) :
    ‖deriv (deriv f) 0‖ ≤ 4 := by
  obtain ⟨q,g,h,H,hqd,hq0,hqn,hqs,hgd,hgu,hg0,hhd,hderh,hdef,hHu,hff⟩ :=
    exists_odd_transform hf
  have hbound : ‖deriv h 0‖ ≤ 1 :=
    meromorphic_univalent_coefficient hhd hHu.1 hdef
      (fun z hz => univalent_deriv_ne_zero
        (Metric.isOpen_ball.sdiff isClosed_singleton) hHu hz) hHu.2
  rw [hderh,norm_neg] at hbound
  rw [hff,norm_mul]
  norm_num
  linarith

def diskAutomorphism (a z : ℂ) : ℂ := (z+a)/(1+starRingEnd ℂ a*z)

lemma diskAutomorphism_den_ne_zero {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    1+starRingEnd ℂ a*z ≠ 0 := by
  have hna : ‖a‖ < 1 := by simpa [disk] using ha
  have hnz : ‖z‖ < 1 := by simpa [disk] using hz
  intro he
  have hb : ‖starRingEnd ℂ a*z‖ < 1 := by
    rw [norm_mul,Complex.norm_conj]
    nlinarith [norm_nonneg a,norm_nonneg z]
  have he' : starRingEnd ℂ a*z = -1 := by linear_combination he
  rw [he'] at hb
  norm_num at hb

lemma diskAutomorphism_normSq_identity (a z : ℂ) :
    Complex.normSq (1+starRingEnd ℂ a*z)-Complex.normSq (z+a) =
      (1-Complex.normSq a)*(1-Complex.normSq z) := by
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring

lemma diskAutomorphism_mem {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    diskAutomorphism a z ∈ disk := by
  have hna : ‖a‖ < 1 := by simpa [disk] using ha
  have hnz : ‖z‖ < 1 := by simpa [disk] using hz
  have hpos : 0 < (1-Complex.normSq a)*(1-Complex.normSq z) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm]
    apply mul_pos <;> nlinarith [norm_nonneg a,norm_nonneg z]
  have hineq := diskAutomorphism_normSq_identity a z
  have hd := diskAutomorphism_den_ne_zero ha hz
  rw [disk,Metric.mem_ball,dist_zero_right,diskAutomorphism,norm_div,div_lt_one (norm_pos_iff.mpr hd)]
  rw [← Complex.sq_norm,← Complex.sq_norm] at hineq
  nlinarith [norm_nonneg (z+a),norm_nonneg (1+starRingEnd ℂ a*z)]

lemma diskAutomorphism_deriv {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    HasDerivAt (diskAutomorphism a)
      ((1-(‖a‖^2 : ℝ))/(1+starRingEnd ℂ a*z)^2) z := by
  have hd := ((hasDerivAt_id z).add_const a).div
    (((hasDerivAt_id z).const_mul (starRingEnd ℂ a)).const_add 1)
    (diskAutomorphism_den_ne_zero ha hz)
  convert hd using 1 <;> try rfl
  rw [Complex.sq_norm]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [id_eq]
  ring

lemma diskAutomorphism_injOn {a : ℂ} (ha : a ∈ disk) : InjOn (diskAutomorphism a) disk := by
  intro z hz w hw he
  have he' := (div_eq_div_iff (diskAutomorphism_den_ne_zero ha hz)
    (diskAutomorphism_den_ne_zero ha hw)).mp he
  have hna : ‖a‖ < 1 := by simpa [disk] using ha
  have hd : (1-starRingEnd ℂ a*a) ≠ 0 := by
    rw [← Complex.normSq_eq_conj_mul_self,← Complex.ofReal_one,← Complex.ofReal_sub]
    apply Complex.ofReal_ne_zero.mpr
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg a]
  apply (mul_left_cancel₀ hd)
  linear_combination he'

lemma diskAutomorphism_zero (a : ℂ) : diskAutomorphism a 0 = a := by simp [diskAutomorphism]

lemma diskAutomorphism_differentiableOn {a : ℂ} (ha : a ∈ disk) :
    DifferentiableOn ℂ (diskAutomorphism a) disk :=
  fun _ hz => (diskAutomorphism_deriv ha hz).differentiableAt.differentiableWithinAt

lemma diskAutomorphism_second_deriv {a : ℂ} (ha : a ∈ disk) :
    deriv (deriv (diskAutomorphism a)) 0 =
      -2*starRingEnd ℂ a*(1-(‖a‖^2 : ℝ)) := by
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have he : deriv (diskAutomorphism a) =ᶠ[𝓝 (0 : ℂ)]
      fun z => (1-(‖a‖^2 : ℝ))/(1+starRingEnd ℂ a*z)^2 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with z hz
    exact (diskAutomorphism_deriv ha hz).deriv
  have hd := (hasDerivAt_const (0 : ℂ) (1-((‖a‖^2 : ℝ) : ℂ))).div
    ((((hasDerivAt_id (0 : ℂ)).const_mul (starRingEnd ℂ a)).const_add 1).pow 2)
    (by simp)
  have hd' := hd.congr_of_eventuallyEq he
  rw [hd'.deriv]
  simp
  ring

def diskKoebe (f : ℂ → ℂ) (a z : ℂ) : ℂ :=
  (f (diskAutomorphism a z)-f a)/((1-((‖a‖^2 : ℝ) : ℂ))*deriv f a)

lemma disk_coeff_ne_zero {a : ℂ} (ha : a ∈ disk) : 1-((‖a‖^2 : ℝ) : ℂ) ≠ 0 := by
  have hn : ‖a‖ < 1 := by simpa [disk] using ha
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.ofReal_ne_zero]
  nlinarith [norm_nonneg a]

lemma diskKoebe_univalent {f : ℂ → ℂ} {a : ℂ} (hf : UnivalentOn f disk)
    (ha : a ∈ disk) (hfd : deriv f a ≠ 0) : UnivalentOn (diskKoebe f a) disk := by
  refine ⟨?_,?_⟩
  · exact ((hf.1.comp (diskAutomorphism_differentiableOn ha)
      (fun _ hz => diskAutomorphism_mem ha hz)).sub_const (f a)).div_const _
  · intro z hz w hw he
    have he' := (div_left_inj' (mul_ne_zero (disk_coeff_ne_zero ha) hfd)).mp he
    exact diskAutomorphism_injOn ha hz hw
      (hf.2 (diskAutomorphism_mem ha hz) (diskAutomorphism_mem ha hw) (sub_left_inj.mp he'))

lemma diskKoebe_deriv {f : ℂ → ℂ} {a z : ℂ} (hf : DifferentiableOn ℂ f disk)
    (ha : a ∈ disk) (hz : z ∈ disk) :
    HasDerivAt (diskKoebe f a)
      ((deriv f (diskAutomorphism a z)*((1-((‖a‖^2 : ℝ) : ℂ))/(1+starRingEnd ℂ a*z)^2))/
        ((1-((‖a‖^2 : ℝ) : ℂ))*deriv f a)) z := by
  exact ((((hf _ (diskAutomorphism_mem ha hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (diskAutomorphism_mem ha hz))).hasDerivAt.comp z
    (diskAutomorphism_deriv ha hz)).sub_const (f a)).div_const _

lemma diskKoebe_schlicht {f : ℂ → ℂ} {a : ℂ} (hf : UnivalentOn f disk)
    (ha : a ∈ disk) (hfd : deriv f a ≠ 0) : Schlicht (diskKoebe f a) := by
  refine ⟨diskKoebe_univalent hf ha hfd, ?_, ?_⟩
  · simp [diskKoebe,diskAutomorphism_zero]
  · have hd := (diskKoebe_deriv hf.1 ha (by simp [disk] : (0 : ℂ) ∈ disk)).deriv
    rw [hd]
    simp only [diskAutomorphism_zero,mul_zero,add_zero,one_pow,div_one]
    rw [mul_comm (deriv f a),div_self (mul_ne_zero (disk_coeff_ne_zero ha) hfd)]

lemma diskKoebe_second_deriv {f : ℂ → ℂ} {a : ℂ} (hf : DifferentiableOn ℂ f disk)
    (ha : a ∈ disk) (hfd : deriv f a ≠ 0) :
    deriv (deriv (diskKoebe f a)) 0 =
      (1-((‖a‖^2 : ℝ) : ℂ))*deriv (deriv f) a/deriv f a-2*starRingEnd ℂ a := by
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have he : deriv (diskKoebe f a) =ᶠ[𝓝 (0 : ℂ)]
      fun z => (deriv f (diskAutomorphism a z)*
        ((1-((‖a‖^2 : ℝ) : ℂ))/(1+starRingEnd ℂ a*z)^2))/
        ((1-((‖a‖^2 : ℝ) : ℂ))*deriv f a) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with z hz
    exact (diskKoebe_deriv hf ha hz).deriv
  have hda := ((hf.deriv Metric.isOpen_ball a ha).differentiableAt
    (Metric.isOpen_ball.mem_nhds ha)).hasDerivAt
  have hda' : HasDerivAt (deriv f) (deriv (deriv f) a) (diskAutomorphism a 0) := by
    simpa [diskAutomorphism_zero] using hda
  have hcomp := hda'.comp 0 (diskAutomorphism_deriv ha hzero)
  have hrat := (hasDerivAt_const (0 : ℂ) (1-((‖a‖^2 : ℝ) : ℂ))).div
    ((((hasDerivAt_id (0 : ℂ)).const_mul (starRingEnd ℂ a)).const_add 1).pow 2)
    (by simp)
  have hd := ((hcomp.mul hrat).div_const
    ((1-((‖a‖^2 : ℝ) : ℂ))*deriv f a)).congr_of_eventuallyEq he
  rw [hd.deriv]
  simp only [Pi.div_apply,Pi.pow_apply,Function.comp_apply,diskAutomorphism_zero,
    mul_zero,add_zero,one_pow,div_one,zero_sub,id_eq,mul_one]
  have halg (A B C D : ℂ) (hB : B ≠ 0) (hC : C ≠ 0) :
      (A*C*C+B*(-(C*(2*D))))/(C*B) = C*A/B-2*D := by
    field_simp
    ring
  exact halg (deriv (deriv f) a) (deriv f a)
    (1-((‖a‖^2 : ℝ) : ℂ)) (starRingEnd ℂ a) hfd (disk_coeff_ne_zero ha)

def omittedTransform (f : ℂ → ℂ) (w z : ℂ) : ℂ := w*f z/(w-f z)

lemma omittedTransform_univalent {f : ℂ → ℂ} {w : ℂ}
    (hf : UnivalentOn f disk) (hw : w ∉ f '' disk) (hw0 : w ≠ 0) :
    UnivalentOn (omittedTransform f w) disk := by
  have hn (z) (hz : z ∈ disk) : w-f z ≠ 0 := by
    intro he
    exact hw ⟨z,hz,(sub_eq_zero.mp he).symm⟩
  refine ⟨(hf.1.const_mul w).div (hf.1.const_sub w) hn,?_⟩
  intro z hz v hv he
  apply hf.2 hz hv
  apply mul_left_cancel₀ (pow_ne_zero 2 hw0)
  have he' := (div_eq_div_iff (hn z hz) (hn v hv)).mp he
  linear_combination he'

lemma omittedTransform_deriv {f : ℂ → ℂ} {w z : ℂ}
    (hf : DifferentiableOn ℂ f disk) (hw : w ∉ f '' disk) (hz : z ∈ disk) :
    HasDerivAt (omittedTransform f w) (w^2*deriv f z/(w-f z)^2) z := by
  have hn : w-f z ≠ 0 := fun he => hw ⟨z,hz,(sub_eq_zero.mp he).symm⟩
  have hd := ((hf z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
  convert (hd.const_mul w).div (hd.const_sub w) hn using 1 <;> try rfl
  ring

lemma omittedTransform_schlicht {f : ℂ → ℂ} {w : ℂ}
    (hf : Schlicht f) (hw : w ∉ f '' disk) : Schlicht (omittedTransform f w) := by
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have hw0 : w ≠ 0 := fun h => hw ⟨0,hzero,hf.2.1.trans h.symm⟩
  refine ⟨omittedTransform_univalent hf.1 hw hw0,?_,?_⟩
  · simp [omittedTransform,hf.2.1]
  · rw [(omittedTransform_deriv hf.1.1 hw hzero).deriv,hf.2.1,hf.2.2]
    simp [hw0]

lemma omittedTransform_second_deriv {f : ℂ → ℂ} {w : ℂ}
    (hf : Schlicht f) (hw : w ∉ f '' disk) :
    deriv (deriv (omittedTransform f w)) 0 = deriv (deriv f) 0+2/w := by
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have hw0 : w ≠ 0 := fun h => hw ⟨0,hzero,hf.2.1.trans h.symm⟩
  have he : deriv (omittedTransform f w) =ᶠ[𝓝 (0 : ℂ)]
      fun z => w^2*deriv f z/(w-f z)^2 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with z hz
    exact (omittedTransform_deriv hf.1.1 hw hz).deriv
  have hfd := ((hf.1.1 0 hzero).differentiableAt (Metric.isOpen_ball.mem_nhds hzero)).hasDerivAt
  have hfdd := ((hf.1.1.deriv Metric.isOpen_ball 0 hzero).differentiableAt
    (Metric.isOpen_ball.mem_nhds hzero)).hasDerivAt
  have hd := ((hfdd.const_mul (w^2)).div ((hfd.const_sub w).pow 2)
    (by simpa [hf.2.1] using pow_ne_zero 2 hw0)).congr_of_eventuallyEq he
  rw [hd.deriv]
  simp only [Pi.pow_apply,hf.2.1,hf.2.2,sub_zero,mul_one]
  field_simp [hw0]
  ring

lemma schlicht_preSchwarzian_bound {f : ℂ → ℂ} (hf : Schlicht f) {a : ℂ} (ha : a ∈ disk) :
    ‖(1-((‖a‖^2 : ℝ) : ℂ))*deriv (deriv f) a/deriv f a-2*starRingEnd ℂ a‖ ≤ 4 := by
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf.1 ha
  have hb := schlicht_second_deriv_bound (diskKoebe_schlicht hf.1 ha hn)
  rwa [diskKoebe_second_deriv hf.1.1 ha hn] at hb

lemma schlicht_quarter {f : ℂ → ℂ} (hf : Schlicht f) :
    Metric.ball (0 : ℂ) (1/4) ⊆ f '' disk := by
  intro w hw
  by_contra hnot
  have hz : (0 : ℂ) ∈ disk := by simp [disk]
  have hw0 : w ≠ 0 := fun h => hnot ⟨0,hz,hf.2.1.trans h.symm⟩
  have hb := schlicht_second_deriv_bound (omittedTransform_schlicht hf hnot)
  rw [omittedTransform_second_deriv hf hnot] at hb
  have hdiff : ‖(2 : ℂ)/w‖ ≤ 8 := by
    have ht := norm_sub_le (deriv (deriv f) 0+2/w) (deriv (deriv f) 0)
    have hf2 := schlicht_second_deriv_bound hf
    simp only [add_sub_cancel_left] at ht
    linarith
  rw [norm_div] at hdiff
  norm_num at hdiff
  have hle := (div_le_iff₀ (norm_pos_iff.mpr hw0)).mp hdiff
  have hw' : ‖w‖ < 1/4 := by simpa using hw
  linarith

lemma hasDerivAt_log_norm_real {g : ℝ → ℂ} {d : ℂ} {x : ℝ}
    (hg : HasDerivAt g d x) (hn : g x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖g t‖) (d/g x).re x := by
  have heq : (fun t => Real.log ‖g t‖) =
      (fun t => (1/2 : ℝ)*Real.log (‖g t‖^2)) := by
    funext t
    rw [Real.log_pow]
    ring
  have hd := ((hg.norm_sq).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).const_mul (1/2 : ℝ)
  rw [heq]
  convert hd using 1
  simp only [Complex.inner,Complex.conj_re,Complex.conj_im,Complex.mul_re,
    Complex.div_re,Complex.normSq_eq_norm_sq]
  ring

lemma logarithmic_distortion {L D : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hL : ∀ x ∈ Icc 0 r, HasDerivAt L (D x) x) (hL0 : L 0 = 0)
    (hbound : ∀ x ∈ Icc 0 r,
      (2*x-4)/(1-x^2) ≤ D x ∧ D x ≤ (2*x+4)/(1-x^2)) :
    Real.log (1-r)-3*Real.log (1+r) ≤ L r ∧
      L r ≤ Real.log (1+r)-3*Real.log (1-r) := by
  have hp (x : ℝ) (hx : x ∈ Icc 0 r) : 0 < 1-x ∧ 0 < 1+x ∧ 0 < 1-x^2 := by
    constructor
    · linarith [hx.2]
    constructor
    · linarith [hx.1]
    · have := hx.1
      nlinarith [hx.2]
  let U := fun x => L x-Real.log (1+x)+3*Real.log (1-x)
  let V := fun x => L x-Real.log (1-x)+3*Real.log (1+x)
  have hU (x) (hx : x ∈ Icc 0 r) : HasDerivAt U
      (D x-1/(1+x)-3/(1-x)) x := by
    have hlogp := ((hasDerivAt_id x).const_add 1).log (ne_of_gt (hp x hx).2.1)
    have hlogm := ((hasDerivAt_id x).const_sub 1).log (ne_of_gt (hp x hx).1)
    convert ((hL x hx).sub hlogp).add (hlogm.const_mul 3) using 1 <;> try rfl
    simp
    ring
  have hV (x) (hx : x ∈ Icc 0 r) : HasDerivAt V
      (D x+1/(1-x)+3/(1+x)) x := by
    have hlogp := ((hasDerivAt_id x).const_add 1).log (ne_of_gt (hp x hx).2.1)
    have hlogm := ((hasDerivAt_id x).const_sub 1).log (ne_of_gt (hp x hx).1)
    convert ((hL x hx).sub hlogm).add (hlogp.const_mul 3) using 1 <;> try rfl
    simp
    ring
  have halg (x) (hx : x ∈ Icc 0 r) :
      1/(1+x)+3/(1-x) = (2*x+4)/(1-x^2) ∧
      -(1/(1-x)+3/(1+x)) = (2*x-4)/(1-x^2) := by
    constructor <;> field_simp [(hp x hx).1.ne', (hp x hx).2.1.ne', (hp x hx).2.2.ne'] <;> ring
  have hUa : AntitoneOn U (Icc 0 r) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 r)
      (fun x hx => (hU x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hU x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hU x (interior_subset hx)).deriv]
    have hb := (hbound x (interior_subset hx)).2
    rw [← (halg x (interior_subset hx)).1] at hb
    linarith
  have hVm : MonotoneOn V (Icc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
      (fun x hx => (hV x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hV x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hV x (interior_subset hx)).deriv]
    have hb := (hbound x (interior_subset hx)).1
    rw [← (halg x (interior_subset hx)).2] at hb
    linarith
  have hu := hUa (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  have hv := hVm (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  dsimp [U,V] at hu hv
  simp only [hL0,add_zero,sub_zero,Real.log_one,mul_zero] at hu hv
  constructor <;> linarith

lemma radialDistortion_of_preSchwarzian {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f disk) (hf0 : deriv f 0 = 1)
    (hfn : ∀ a ∈ disk, deriv f a ≠ 0)
    (hps : ∀ a ∈ disk,
      ‖(1-((‖a‖^2 : ℝ) : ℂ))*deriv (deriv f) a/deriv f a-2*starRingEnd ℂ a‖ ≤ 4)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (1-r)/(1+r)^3 ≤ ‖deriv f ((r : ℂ)*ζ)‖ ∧
      ‖deriv f ((r : ℂ)*ζ)‖ ≤ (1+r)/(1-r)^3 := by
  let L : ℝ → ℝ := fun x => Real.log ‖deriv f ((x : ℂ)*ζ)‖
  let D : ℝ → ℝ := fun x => (deriv (deriv f) ((x : ℂ)*ζ)*ζ/deriv f ((x : ℂ)*ζ)).re
  have hn (x) (hx : x ∈ Icc 0 r) : ‖(x : ℂ)*ζ‖ = x := by
    rw [norm_mul,hζ,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1]
  have hm (x) (hx : x ∈ Icc 0 r) : (x : ℂ)*ζ ∈ disk := by
    simp only [disk,Metric.mem_ball,dist_zero_right,hn x hx]
    exact hx.2.trans_lt hr1
  have hD (x) (hx : x ∈ Icc 0 r) : HasDerivAt L (D x) x := by
    have hd := ((hf.deriv Metric.isOpen_ball _ (hm x hx)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hm x hx))).hasDerivAt
    have hx' : HasDerivAt (fun t : ℝ => (t : ℂ)*ζ) ζ x := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const ζ :
        HasDerivAt (fun t : ℝ => Complex.ofRealCLM t*ζ) ((Complex.ofRealCLM (1 : ℝ))*ζ) x)
    have hdc : HasDerivAt (fun t : ℝ => deriv f ((t : ℂ)*ζ))
        (deriv (deriv f) ((x : ℂ)*ζ)*ζ) x := by
      convert HasDerivAt.comp (𝕜 := ℝ) x hd hx' using 1
      rfl
    exact hasDerivAt_log_norm_real hdc (hfn _ (hm x hx))
  have hb (x) (hx : x ∈ Icc 0 r) :
      (2*x-4)/(1-x^2) ≤ D x ∧ D x ≤ (2*x+4)/(1-x^2) := by
    let A : ℂ := (1-((x^2 : ℝ) : ℂ))*deriv (deriv f) ((x : ℂ)*ζ)/deriv f ((x : ℂ)*ζ)
      -2*starRingEnd ℂ ((x : ℂ)*ζ)
    have hA : ‖A*ζ‖ ≤ 4 := by
      rw [norm_mul,hζ,mul_one]
      simpa only [A,hn x hx] using hps _ (hm x hx)
    have he : (A*ζ).re = (1-x^2)*D x-2*x := by
      have hzz : starRingEnd ℂ ζ*ζ = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self,← Complex.sq_norm,hζ]
        norm_num
      have heq : A*ζ = ((1-x^2 : ℝ) : ℂ)*
          (deriv (deriv f) ((x : ℂ)*ζ)*ζ/deriv f ((x : ℂ)*ζ))-2*(x : ℂ) := by
        dsimp only [A]
        rw [map_mul,Complex.conj_ofReal]
        rw [Complex.ofReal_sub,Complex.ofReal_one]
        linear_combination -2*(x : ℂ)*hzz
      rw [heq]
      simp only [D,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero]
      norm_num
    have hreal := (Complex.abs_re_le_norm (A*ζ)).trans hA
    rw [he,abs_le] at hreal
    have hpos : 0 < 1-x^2 := by nlinarith [hx.1,hx.2]
    constructor
    · rw [div_le_iff₀ hpos]
      nlinarith [hreal.1]
    · rw [le_div_iff₀ hpos]
      nlinarith [hreal.2]
  have hbnd := logarithmic_distortion hr hr1 hD (by simp [L,hf0]) hb
  have hposm : 0 < 1-r := sub_pos.mpr hr1
  have hposp : 0 < 1+r := by linarith
  have hnorm : 0 < ‖deriv f ((r : ℂ)*ζ)‖ := norm_pos_iff.mpr (hfn _ (hm r (right_mem_Icc.mpr hr)))
  constructor
  · apply (Real.log_le_log_iff (div_pos hposm (pow_pos hposp 3)) hnorm).mp
    simpa only [Real.log_div hposm.ne' (pow_ne_zero 3 hposp.ne'),Real.log_pow,Nat.cast_ofNat] using hbnd.1
  · apply (Real.log_le_log_iff hnorm (div_pos hposp (pow_pos hposm 3))).mp
    simpa only [Real.log_div hposp.ne' (pow_ne_zero 3 hposm.ne'),Real.log_pow,Nat.cast_ofNat] using hbnd.2

lemma schlicht_deriv_bounds {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ} (hz : z ∈ disk) :
    (1-‖z‖)/(1+‖z‖)^3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1+‖z‖)/(1-‖z‖)^3 := by
  by_cases hzero : z = 0
  · simp [hzero,hf.2.2]
  have hn := norm_pos_iff.mpr hzero
  have hζ : ‖z/(‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg z),div_self hn.ne']
  have heq : (‖z‖ : ℂ)*(z/(‖z‖ : ℂ)) = z := by
    field_simp [show (‖z‖ : ℂ) ≠ 0 by exact_mod_cast hn.ne']
  have hb := radialDistortion_of_preSchwarzian hf.1.1 hf.2.2
    (fun _ ha => univalent_deriv_ne_zero Metric.isOpen_ball hf.1 ha)
    (fun _ ha => schlicht_preSchwarzian_bound hf ha) (norm_nonneg z)
    (show ‖z‖ < 1 by simpa [disk] using hz) hζ
  rwa [heq] at hb

lemma schlicht_deriv_compact_bound {f : ℂ → ℂ} (hf : Schlicht f)
    {R : ℝ} (hR : R < 1) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖deriv f z‖ ≤ 2/(1-R)^3 := by
  have hzm : z ∈ disk := by simpa [disk] using hz.trans_lt hR
  apply (schlicht_deriv_bounds hf hzm).2.trans
  have hd : 0 < 1-R := sub_pos.mpr hR
  apply div_le_div₀ (by positivity) (by linarith [norm_nonneg z]) (by positivity)
  exact pow_le_pow_left₀ hd.le (by linarith) 3

lemma schlicht_lipschitz_bound {f : ℂ → ℂ} (hf : Schlicht f)
    {R : ℝ} (hR : R < 1) {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖f z-f w‖ ≤ (2/(1-R)^3)*‖z-w‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Metric.closedBall 0 R)
    (𝕜 := ℂ) _ _ (convex_closedBall 0 R)
    (by simpa using hw) (by simpa using hz)
  · intro x hx
    apply (hf.1.1 x _).differentiableAt
      (Metric.isOpen_ball.mem_nhds (show x ∈ disk from ?_))
    all_goals simpa [disk] using (show ‖x‖ ≤ R by simpa using hx).trans_lt hR
  · intro x hx
    exact schlicht_deriv_compact_bound hf hR (by simpa using hx)

lemma schlicht_local_bound {f : ℂ → ℂ} (hf : Schlicht f)
    {R : ℝ} (hR : R < 1) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖f z‖ ≤ (2/(1-R)^3)*R := by
  have h := schlicht_lipschitz_bound hf hR hz
    (show ‖(0 : ℂ)‖ ≤ R by simpa using (norm_nonneg z).trans hz)
  simp only [hf.2.1,sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left hz (by positivity))

def ballNormalize (f : ℂ → ℂ) (a : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (f (a+(R : ℂ)*z)-f a)/((R : ℂ)*deriv f a)

lemma affine_disk_maps_ball (a : ℂ) {R : ℝ} (hR : 0 < R) :
    MapsTo (fun z : ℂ => a+(R : ℂ)*z) disk (Metric.ball a R) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  simp only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  nlinarith

lemma ballNormalize_deriv {f : ℂ → ℂ} {a z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball a R)) (hz : z ∈ disk) :
    HasDerivAt (ballNormalize f a R)
      (deriv f (a+(R : ℂ)*z)/deriv f a) z := by
  have hmap := affine_disk_maps_ball a hR hz
  have hd := ((hf _ hmap).differentiableAt (Metric.isOpen_ball.mem_nhds hmap)).hasDerivAt
  have hdz := (((hd.comp z (((hasDerivAt_id z).const_mul (R : ℂ)).const_add a)).sub_const (f a)).div_const
    ((R : ℂ)*deriv f a))
  convert hdz using 1 <;> try rfl
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  simp only [mul_one]
  field_simp

lemma ballNormalize_schlicht {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : UnivalentOn f (Metric.ball a R)) (hn : deriv f a ≠ 0) :
    Schlicht (ballNormalize f a R) := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hmap := affine_disk_maps_ball a hR
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro z hz
    exact (ballNormalize_deriv hR hf.1 hz).differentiableAt.differentiableWithinAt
  · intro z hz w hw he
    apply mul_left_cancel₀ hRc
    apply add_left_cancel (a := a)
    apply hf.2 (hmap hz) (hmap hw)
    have he' := (div_left_inj' (mul_ne_zero hRc hn)).mp he
    exact sub_left_inj.mp he'
  · simp [ballNormalize]
  · rw [(ballNormalize_deriv hR hf.1 (show (0 : ℂ) ∈ disk by simp [disk])).deriv]
    simp [hn]

lemma univalent_ball_quarter {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : UnivalentOn f (Metric.ball a R)) :
    Metric.ball (f a) (R*‖deriv f a‖/4) ⊆ f '' Metric.ball a R := by
  have ha : a ∈ Metric.ball a R := Metric.mem_ball_self hR
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf ha
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hden := mul_ne_zero hRc hn
  intro w hw
  have hu : (w-f a)/((R : ℂ)*deriv f a) ∈ Metric.ball (0 : ℂ) (1/4) := by
    simp only [Metric.mem_ball,dist_zero_right,norm_div,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
    rw [div_lt_iff₀ (mul_pos hR (norm_pos_iff.mpr hn))]
    have hw' : ‖w-f a‖ < R*‖deriv f a‖/4 := by simpa [dist_eq_norm] using hw
    linarith
  obtain ⟨z,hz,he⟩ := schlicht_quarter (ballNormalize_schlicht hR hf hn) hu
  refine ⟨a+(R : ℂ)*z,affine_disk_maps_ball a hR hz,?_⟩
  have hes := (div_left_inj' hden).mp he
  exact sub_left_inj.mp hes

lemma schlicht_separation {f : ℂ → ℂ} (hf : Schlicht f)
    {z w : ℂ} (_hz : z ∈ disk) (hw : w ∈ disk) {R : ℝ} (hR : 0 < R)
    (hsub : Metric.ball z R ⊆ disk) (hdist : R ≤ ‖w-z‖) :
    R*‖deriv f z‖/4 ≤ ‖f w-f z‖ := by
  by_contra! hlt
  have hm : f w ∈ Metric.ball (f z) (R*‖deriv f z‖/4) := by
    simpa [dist_eq_norm] using hlt
  obtain ⟨v,hv,he⟩ := univalent_ball_quarter hR ⟨hf.1.1.mono hsub,hf.1.2.mono hsub⟩ hm
  have hvw := hf.1.2 (hsub hv) hw he
  subst v
  have : ‖w-z‖ < R := by simpa [dist_eq_norm] using hv
  exact (not_lt_of_ge hdist) this

lemma schlicht_lower_growth {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ} (hz : z ∈ disk) :
    ‖z‖/4 ≤ ‖f z‖ := by
  by_cases hzero : z = 0
  · simp [hzero,hf.2.1]
  have h := schlicht_separation hf (show (0 : ℂ) ∈ disk by simp [disk]) hz
    (norm_pos_iff.mpr hzero)
    (Metric.ball_subset_ball (show ‖z‖ ≤ 1 by exact le_of_lt (by simpa [disk] using hz)))
    (show ‖z‖ ≤ ‖z-(0 : ℂ)‖ by simp)
  simpa [hf.2.1,hf.2.2] using h

lemma schlicht_uniform_separation {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk)
    (hne : z ≠ w) : ∃ c : ℝ, 0 < c ∧ ∀ f : ℂ → ℂ, Schlicht f → c ≤ ‖f w-f z‖ := by
  have hz1 : ‖z‖ < 1 := by simpa [disk] using hz
  let R := min ((1-‖z‖)/2) (‖w-z‖/2)
  have hR : 0 < R := lt_min (by linarith)
    (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)) (by norm_num))
  have hR1 : R ≤ (1-‖z‖)/2 := min_le_left _ _
  have hR2 : R ≤ ‖w-z‖/2 := min_le_right _ _
  have hsub : Metric.ball z R ⊆ disk := by
    intro v hv
    have hvR : ‖v-z‖ < R := by simpa [dist_eq_norm] using hv
    have ht := norm_add_le (v-z) z
    rw [sub_add_cancel] at ht
    simp only [disk,Metric.mem_ball,dist_zero_right]
    linarith
  refine ⟨R*((1-‖z‖)/(1+‖z‖)^3)/4,by positivity,?_⟩
  intro f hf
  have h := schlicht_separation hf hz hw hR hsub (by linarith [norm_nonneg (w-z)])
  apply le_trans _ h
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (schlicht_deriv_bounds hf hz).1 hR.le)
    (by norm_num)

end Brennan

end

end OAI
