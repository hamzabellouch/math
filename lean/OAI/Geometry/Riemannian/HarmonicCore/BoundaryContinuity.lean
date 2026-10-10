import OAI.Geometry.Riemannian.HarmonicCore.BoundaryBarrier
import OAI.Geometry.Riemannian.HarmonicCore.WeakMaximum

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution

namespace HarmonicCounterexample.Main.SmoothMetric3

lemma sobolevValue_supported (R : ℝ) (u : ZeroSobolev R) :
    ∀ᵐ x ∂(volume : Measure E3), x ∉ Metric.closedBall (0:E3) R → (sobolevValue R u) x=0 := by
  obtain ⟨z,hz,hzt⟩ := mem_closure_iff_seq_limit.mp u.property
  choose φ hφ using hz
  have hv : Tendsto (fun n ↦ testValueLinear R (φ n)) atTop (𝓝 (sobolevValue R u)) := by
    have h := (WithLp.fstL 2 ℝ ValueL2 DerivativeL2).continuous.continuousAt.tendsto.comp hzt
    convert h using 1
    · funext n
      dsimp only [Function.comp_apply]
      rw [←hφ n]
      rfl
    · rfl
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have he : ∀ᵐ x ∂volume, ∀ n : ℕ, (testValueLinear R (φ (ns n))) x=((φ (ns n)):E3 → ℝ) x :=
    ae_all_iff.mpr (fun n ↦ (φ (ns n)).value_memLp.coeFn_toLp)
  filter_upwards [hae,he] with x hx he
  intro hout
  have hvz (n : ℕ) : (testValueLinear R (φ (ns n))) x=0 := by
    rw [he n]
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    exact hout (Metric.ball_subset_closedBall ((φ (ns n)).property.2.2 hs))
  have htzero : Tendsto (fun n : ℕ ↦ (testValueLinear R (φ (ns n))) x) atTop (𝓝 (0:ℝ)) := by
    simpa only [hvz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hx htzero

lemma metricFlux_compact (g : SmoothMetric3) {f : E3 → ℝ}
    (hf : HasCompactSupport f) (i : Fin 3) : HasCompactSupport (fun x ↦ g.metricFlux f x i) := by
  apply hf.mono'
  intro x hx
  by_contra hn
  apply hx
  simp [metricFlux,coordDeriv,fderiv_of_notMem_tsupport ℝ hn]

lemma laplacian_green_sobolev (g : SmoothMetric3) (R : ℝ) (v : ZeroSobolev R)
    {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (∫ x, (sobolevValue R v) x*(Real.sqrt (g.coeff x).det*g.laplacian f x)) =
      -(∫ x, ⟪g.energyOperator x (gradient f x),(sobolevDerivative R v) x⟫_ℝ) := by
  have hleft (i : Fin 3) : Integrable (fun x ↦ (sobolevValue R v) x *
      coordDeriv (fun y ↦ g.metricFlux f y i) i x) (volume : Measure E3) :=
    (Lp.memLp (sobolevValue R v)).integrable_mul
      (smooth_direction_memLp (g.metricFlux_contDiff hf i) (g.metricFlux_compact hfc i) (coordinateVector i))
  have hright (i : Fin 3) : Integrable (fun x ↦ g.metricFlux f x i *
      ⟪(sobolevDerivative R v) x,coordinateVector i⟫_ℝ) (volume : Measure E3) :=
    (smooth_memLp (g.metricFlux_contDiff hf i) (g.metricFlux_compact hfc i)).integrable_mul
      ((Lp.memLp (sobolevDerivative R v)).inner_const (𝕜:=ℝ) (coordinateVector i))
  have hparts (i : Fin 3) := sobolev_weak_derivative R v
    (g.metricFlux_contDiff hf i) (g.metricFlux_compact hfc i) (coordinateVector i)
  have he (x : E3) : (∑ i,g.metricFlux f x i*⟪(sobolevDerivative R v) x,coordinateVector i⟫_ℝ) =
      ⟪g.energyOperator x (gradient f x),(sobolevDerivative R v) x⟫_ℝ := by
    have hg (i : Fin 3) : gradient f x i=coordDeriv f i x := by
      change _ = fderiv ℝ f x (coordinateVector i)
      have hh := inner_gradient_left (𝕜:=ℝ) (f:=f) (x:=x) (y:=coordinateVector i)
      simpa only [coordinateVector,EuclideanSpace.inner_single_right,RCLike.inner_apply,
        starRingEnd_apply,star_trivial,mul_one,one_mul,conj_trivial] using hh
    have hi (i : Fin 3) : ⟪(sobolevDerivative R v) x,coordinateVector i⟫_ℝ = (sobolevDerivative R v) x i := by
      simp only [coordinateVector,EuclideanSpace.inner_single_right,one_mul,conj_trivial]
    simp only [hi]
    change _ = ⟪WithLp.toLp 2 (g.energyMatrix x *ᵥ (gradient f x).ofLp),(sobolevDerivative R v) x⟫_ℝ
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    have hflux : g.metricFlux f x i = (g.energyMatrix x *ᵥ (gradient f x).ofLp) i := by
      unfold metricFlux Matrix.mulVec dotProduct
      apply Finset.sum_congr rfl
      intro j _
      rw [hg]
    rw [hflux]
    simp [RCLike.inner_apply,mul_comm]
  simp_rw [← g.laplacian_divergence hf,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hleft i)]
  have hh : (∑ i,∫ x,(sobolevValue R v) x*coordDeriv (fun y ↦ g.metricFlux f y i) i x) =
      -(∫ x,∑ i,g.metricFlux f x i*⟪(sobolevDerivative R v) x,coordinateVector i⟫_ℝ) := by
    rw [integral_finsetSum _ (fun i _ ↦ hright i)]
    simp only [coordDeriv,hparts,Finset.sum_neg_distrib]
  rw [hh]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall he

lemma smooth_energy_nonneg_of_superharmonic (g : SmoothMetric3) (R : ℝ) (v : ZeroSobolev R)
    {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hLap : ∀ x ∈ Metric.closedBall (0:E3) R, g.laplacian f x ≤ 0)
    (hv : ∀ᵐ x ∂volume, 0 ≤ (sobolevValue R v) x) :
    0 ≤ ∫ x, ⟪g.energyOperator x (gradient f x),(sobolevDerivative R v) x⟫_ℝ := by
  have hh := g.laplacian_green_sobolev R v hf hfc
  have hi : (∫ x, (sobolevValue R v) x*(Real.sqrt (g.coeff x).det*g.laplacian f x)) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [hv,sobolevValue_supported R v] with x hx hs
    by_cases hb : x ∈ Metric.closedBall (0:E3) R
    · exact mul_nonpos_of_nonneg_of_nonpos hx
        (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (hLap x hb))
    · simp only [hs hb,zero_mul,Pi.zero_apply,le_refl]
  linarith



lemma gradient_sub_smooth {H f : E3 → ℝ} (hH : ContDiff ℝ ∞ H) (hf : ContDiff ℝ ∞ f) :
    gradient (H-f)=gradient H-gradient f := by
  funext x
  unfold gradient
  rw [fderiv_sub (hH.differentiable (by simp) x) (hf.differentiable (by simp) x),map_sub]
  rfl

lemma gradient_eqOn_closedBall (R : ℝ) (hR : 0<R) {f h : E3 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (he : EqOn f h (Metric.closedBall 0 R)) :
    EqOn (gradient f) (gradient h) (Metric.closedBall 0 R) := by
  have hi : EqOn (gradient f) (gradient h) (Metric.ball 0 R) := by
    intro x hx
    have he' : f =ᶠ[𝓝 x] h := (he.mono Metric.ball_subset_closedBall).eventuallyEq_of_mem
      (Metric.isOpen_ball.mem_nhds hx)
    unfold gradient
    rw [he'.fderiv_eq]
  simpa only [closure_ball (0:E3) (ne_of_gt hR)] using hi.closure (gradient_continuous hf) (gradient_continuous hh)

lemma clipped_energy_representation (g : SmoothMetric3) (R C : ℝ)
    (hC : ∀ x, ‖g.clippedEnergyOperator R x‖ ≤ C)
    (D : DerivativeL2) (F : E3 → E3) (hD : (D:E3 → E3) =ᵐ[volume] F)
    (v : ZeroSobolev R) :
    ⟪coefficientCLM (g.clippedEnergyOperator R) C
      (g.clippedEnergyOperator_measurable R) hC D,sobolevDerivative R v⟫_ℝ =
      ∫ x,⟪g.energyOperator x (F x),(sobolevDerivative R v) x⟫_ℝ := by
  rw [coefficient_inner_integral,g.clippedEnergy_integral_eq]
  apply integral_congr_ae
  filter_upwards [hD] with x hx
  rw [hx]

lemma clipped_affine_energy_eq (g : SmoothMetric3) (R S C : ℝ)
    (hC : ∀ x, ‖g.clippedEnergyOperator R x‖ ≤ C)
    (G : DirichletTest S) (H f : E3 → ℝ)
    (hD : EqOn (gradient (G:E3 → ℝ)) (gradient H-gradient f) (Metric.closedBall 0 R))
    (DH Df : DerivativeL2) (hDH : (DH:E3 → E3) =ᵐ[volume] gradient H)
    (hDf : (Df:E3 → E3) =ᵐ[volume] gradient f) (u v : ZeroSobolev R) :
    ⟪coefficientCLM (g.clippedEnergyOperator R) C
      (g.clippedEnergyOperator_measurable R) hC
      (testDerivativeLinear S G+sobolevDerivative R u),sobolevDerivative R v⟫_ℝ =
    ⟪coefficientCLM (g.clippedEnergyOperator R) C
      (g.clippedEnergyOperator_measurable R) hC
      (DH+sobolevDerivative R u-Df),sobolevDerivative R v⟫_ℝ := by
  rw [coefficient_inner_integral,coefficient_inner_integral]
  apply integral_congr_ae
  filter_upwards [G.derivative_memLp.coeFn_toLp,hDH,hDf,
    Lp.coeFn_add (testDerivativeLinear S G) (sobolevDerivative R u),
    Lp.coeFn_add DH (sobolevDerivative R u),
    Lp.coeFn_sub (DH+sobolevDerivative R u) Df,sobolevDerivative_supported R v] with x h1 h2 h3 h4 h5 h6 h7
  change (testDerivativeLinear S G) x = gradient (G:E3 → ℝ) x at h1
  by_cases hx : x ∈ Metric.closedBall (0:E3) R
  · rw [h4,h6]
    simp only [Pi.add_apply,Pi.sub_apply]
    rw [h5]
    simp only [Pi.add_apply]
    rw [h1,h2,h3,hD hx]
    simp only [Pi.sub_apply]
    congr 2
    abel
  · simp only [h7 hx,inner_zero_right]

theorem affine_weak_le_superharmonic (g : SmoothMetric3) (R : ℝ) (hR : 0<R)
    {H f : E3 → ℝ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖x‖=R → H x<f x)
    (hLap : ∀ x ∈ Metric.closedBall (0:E3) R, g.laplacian f x ≤ 0)
    (u : ZeroSobolev R)
    (hu : ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.energyOperator x (gradient H x+(sobolevDerivative R u) x),
        (sobolevDerivative R v) x⟫_ℝ)=0) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0:E3) R), H x+(sobolevValue R u) x ≤ f x := by
  obtain ⟨S,G,hG,hGs⟩ := strict_boundary_test_extension R hR (hH.sub hf)
    (fun x hx ↦ sub_neg.mpr (hb x hx))
  have hD := gradient_eqOn_closedBall R hR G.property.1 (hH.sub hf) hG
  change EqOn (gradient (G:E3 → ℝ)) (gradient (H-f)) (Metric.closedBall 0 R) at hD
  rw [gradient_sub_smooth hH hf] at hD
  obtain ⟨c,C,hc,hC,hpos⟩ := g.clippedEnergyOperator_uniform R hR.le
  let A := coefficientCLM (g.clippedEnergyOperator R) C (g.clippedEnergyOperator_measurable R) hC
  let DH : DerivativeL2 := (smooth_gradient_memLp hH hHc).toLp (gradient H)
  let Df : DerivativeL2 := (smooth_gradient_memLp hf hfc).toLp (gradient f)
  have hDH : (DH:E3 → E3) =ᵐ[volume] gradient H := (smooth_gradient_memLp hH hHc).coeFn_toLp
  have hDf : (Df:E3 → E3) =ᵐ[volume] gradient f := (smooth_gradient_memLp hf hfc).coeFn_toLp
  have hw (v : ZeroSobolev R) (hv : ∀ᵐ x ∂volume, 0 ≤ (sobolevValue R v) x) :
      ⟪A (testDerivativeLinear S G+sobolevDerivative R u),sobolevDerivative R v⟫_ℝ ≤ 0 := by
    have heq := g.clipped_affine_energy_eq R S C hC G H f hD DH Df hDH hDf u v
    have hsum : ((DH+sobolevDerivative R u:DerivativeL2):E3 → E3) =ᵐ[volume]
        fun x ↦ gradient H x+(sobolevDerivative R u) x := by
      filter_upwards [hDH,Lp.coeFn_add DH (sobolevDerivative R u)] with x h1 h2
      simp only [h2,Pi.add_apply,h1]
    have hzero : ⟪A (DH+sobolevDerivative R u),sobolevDerivative R v⟫_ℝ=0 :=
      (g.clipped_energy_representation R C hC _ _ hsum v).trans (hu v)
    have hnonneg : 0 ≤ ⟪A Df,sobolevDerivative R v⟫_ℝ := by
      rw [g.clipped_energy_representation R C hC Df (gradient f) hDf v]
      exact g.smooth_energy_nonneg_of_superharmonic R v hf hfc hLap hv
    rw [heq,map_sub,inner_sub_left,hzero]
    linarith
  have hm := affine_weak_maximum R S G u hGs (g.clippedEnergyOperator R) C c hc
    (g.clippedEnergyOperator_measurable R) hC hpos hw
  apply (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr
  filter_upwards [hm,G.value_memLp.coeFn_toLp,
    Lp.coeFn_add (testValueLinear S G) (sobolevValue R u)] with x h1 h2 h3
  intro hx
  change (testValueLinear S G) x = (G:E3 → ℝ) x at h2
  rw [h3] at h1
  simp only [Pi.add_apply,h2,hG (Metric.ball_subset_closedBall hx)] at h1
  linarith

theorem classical_weak_le_superharmonic (g : SmoothMetric3) (R : ℝ) (hR : 0<R)
    {H f F : E3 → ℝ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖x‖=R → H x<f x)
    (hLap : ∀ x ∈ Metric.closedBall (0:E3) R, g.laplacian f x ≤ 0)
    (u : ZeroSobolev R)
    (hu : ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.energyOperator x (gradient H x+(sobolevDerivative R u) x),
        (sobolevDerivative R v) x⟫_ℝ)=0)
    (hF : ContinuousOn F (Metric.ball 0 R))
    (hFa : F =ᵐ[volume.restrict (Metric.ball 0 R)] (fun x ↦ H x+(sobolevValue R u) x)) :
    ∀ x ∈ Metric.ball (0:E3) R, F x ≤ f x := by
  have hae := g.affine_weak_le_superharmonic R hR hH hHc hf hfc hb hLap u hu
  have he : (fun x ↦ max (F x) (f x)) =ᵐ[volume.restrict (Metric.ball 0 R)] f := by
    filter_upwards [hFa,hae] with x h1 h2
    exact max_eq_right (h1 ▸ h2)
  have hc := volume.eqOn_open_of_ae_eq he Metric.isOpen_ball
    (hF.sup hf.continuous.continuousOn) hf.continuous.continuousOn
  intro x hx
  exact max_eq_right_iff.mp (hc hx)



lemma barrier_boundary_domination (R : ℝ) (p : E3) (_hp : ‖p‖=R)
    {H b : E3 → ℝ} (hH : Continuous H) (hb : Continuous b)
    (hbpos : ∀ x ∈ Metric.closedBall (0:E3) R, x≠p → 0<b x) (hbp : b p=0)
    (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖x‖=R → H x < H p+ε+M*b x := by
  let K := Metric.sphere (0:E3) R ∩ {x | ε/2 ≤ H x-H p}
  have hK : IsCompact K := (isCompact_sphere (0:E3) R).inter_right
    (isClosed_le continuous_const (hH.sub continuous_const))
  have hn (x : E3) (hx : ‖x‖=R) : 0 ≤ b x := by
    by_cases he : x=p
    · simp only [he,hbp,le_refl]
    · exact (hbpos x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx.le) he).le
  by_cases he : K.Nonempty
  · obtain ⟨y,hy,hmin⟩ := hK.exists_isMinOn he hb.continuousOn
    have hyp : y ≠ p := by
      intro hh
      have ht : ε/2 ≤ H y-H p := hy.2
      simp only [hh,sub_self] at ht
      linarith
    have hym : ‖y‖=R := by simpa only [Metric.mem_sphere,dist_zero_right] using hy.1
    have hby : 0<b y := hbpos y
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hym.le) hyp
    obtain ⟨C,hC⟩ := (isCompact_sphere (0:E3) R).exists_bound_of_continuousOn
      (hH.sub continuous_const).continuousOn
    let M := (|C|+1)/b y
    have hM : 0<M := div_pos (by positivity) hby
    refine ⟨M,hM.le,fun x hx ↦ ?_⟩
    have hxc : x ∈ Metric.sphere (0:E3) R := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
    by_cases hxK : x ∈ K
    · have hbxy : b y ≤ b x := hmin hxK
      have hbd : H x-H p ≤ |C| := (le_abs_self _).trans ((hC x hxc).trans (le_abs_self _))
      have hMb : M*b y=|C|+1 := div_mul_cancel₀ _ hby.ne'
      have hMul := mul_le_mul_of_nonneg_left hbxy hM.le
      linarith
    · have hdiff : H x-H p < ε/2 := by
        apply lt_of_not_ge
        intro hd
        exact hxK ⟨hxc,hd⟩
      have hMul := mul_nonneg hM.le (hn x hx)
      linarith
  · refine ⟨0,le_refl _,fun x hx ↦ ?_⟩
    have hdiff : H x-H p < ε/2 := by
      apply lt_of_not_ge
      intro hd
      apply he
      exact ⟨x,by simpa only [Metric.mem_sphere,dist_zero_right] using hx,hd⟩
    simp only [zero_mul,add_zero]
    linarith

theorem exists_boundary_majorant (g : SmoothMetric3) (R : ℝ) (hR : 0<R)
    (p : E3) (hp : ‖p‖=R) {H : E3 → ℝ} (hH : Continuous H)
    (ε : ℝ) (hε : 0<ε) :
    ∃ f : E3 → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ f p=H p+ε ∧
      (∀ x, ‖x‖=R → H x<f x) ∧
      (∀ x ∈ Metric.closedBall (0:E3) R, g.laplacian f x ≤ 0) := by
  obtain ⟨b,hbs,hbp,hbpos,hbLap⟩ := g.exists_boundary_barrier R hR p hp
  obtain ⟨M,hM,hdom⟩ := barrier_boundary_domination R p hp hH hbs.continuous hbpos hbp ε hε
  let f0 : E3 → ℝ := fun x ↦ H p+ε+M*b x
  have hf0 : ContDiff ℝ ∞ f0 := contDiff_const.add (contDiff_const.mul hbs)
  let χ : ContDiffBump (0:E3) := ⟨R+1,R+2,by linarith,by linarith⟩
  let f : E3 → ℝ := fun x ↦ χ x*f0 x
  have he (x : E3) (hx : x ∈ Metric.closedBall (0:E3) R) : f =ᶠ[𝓝 x] f0 := by
    have hc := χ.eventuallyEq_one_of_mem_ball (Metric.closedBall_subset_ball
      (show R<χ.rIn by dsimp [χ]; linarith) hx)
    filter_upwards [hc] with y hy
    simp only [f,hy,Pi.one_apply,one_mul]
  have hpR : p ∈ Metric.closedBall (0:E3) R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.le
  refine ⟨f,χ.contDiff.mul hf0,χ.hasCompactSupport.mul_right,?_,?_,?_⟩
  · rw [(he p hpR).eq_of_nhds]
    simp only [f0,hbp,mul_zero,add_zero]
  · intro x hx
    rw [(he x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx.le)).eq_of_nhds]
    exact hdom x hx
  · intro x hx
    have hfl : g.laplacian f0 x=M*g.laplacian b x := by
      change g.laplacian ((fun _ : E3 ↦ H p+ε)+M • b) x=_
      have hm : ContDiff ℝ ∞ (M • b) := hbs.const_smul M
      rw [g.laplacian_add contDiff_const hm,g.laplacian_const,
        g.laplacian_smul hbs M,zero_add]
    have hfe : g.laplacian f x=g.laplacian f0 x := by
      unfold laplacian coordDeriv
      rw [((he x hx).iteratedFDeriv ℝ 2).eq_of_nhds,(he x hx).fderiv_eq]
    rw [hfe,hfl]
    exact mul_nonpos_of_nonneg_of_nonpos hM (hbLap x hx).le



lemma gradient_neg_smooth {H : E3 → ℝ} (_hH : ContDiff ℝ ∞ H) :
    gradient (-H)= -gradient H := by
  funext x
  unfold gradient
  rw [fderiv_neg, map_neg]
  rfl

lemma affine_weak_neg (g : SmoothMetric3) (R : ℝ) {H : E3 → ℝ} (u : ZeroSobolev R)
    (hH : ContDiff ℝ ∞ H)
    (hu : ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.energyOperator x (gradient H x+(sobolevDerivative R u) x),
        (sobolevDerivative R v) x⟫_ℝ)=0) :
    ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.energyOperator x (gradient (-H) x+(sobolevDerivative R (-u)) x),
        (sobolevDerivative R v) x⟫_ℝ)=0 := by
  intro v
  have he : (fun x ↦ ⟪g.energyOperator x (gradient (-H) x+(sobolevDerivative R (-u)) x),
        (sobolevDerivative R v) x⟫_ℝ) =ᵐ[volume]
      (fun x ↦ -⟪g.energyOperator x (gradient H x+(sobolevDerivative R u) x),
        (sobolevDerivative R v) x⟫_ℝ) := by
    rw [map_neg,gradient_neg_smooth hH]
    filter_upwards [Lp.coeFn_neg (sobolevDerivative R u)] with x hx
    simp only [hx,Pi.neg_apply,←neg_add,map_neg,inner_neg_left]
  rw [integral_congr_ae he,integral_neg,hu v,neg_zero]

theorem classical_weak_boundary_continuity (g : SmoothMetric3) (R : ℝ) (hR : 0<R)
    {H F : E3 → ℝ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    (u : ZeroSobolev R)
    (hu : ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.energyOperator x (gradient H x+(sobolevDerivative R u) x),
        (sobolevDerivative R v) x⟫_ℝ)=0)
    (hF : ContinuousOn F (Metric.ball 0 R))
    (hFa : F =ᵐ[volume.restrict (Metric.ball 0 R)] (fun x ↦ H x+(sobolevValue R u) x)) :
    ∃ U : E3 → ℝ, EqOn U F (Metric.ball 0 R) ∧
      (∀ p, ‖p‖=R → U p=H p) ∧ ContinuousOn U (Metric.closedBall 0 R) := by
  classical
  let U : E3 → ℝ := (Metric.ball (0:E3) R).piecewise F H
  have hUi : EqOn U F (Metric.ball 0 R) := by
    intro x hx
    exact piecewise_eq_of_mem _ _ _ hx
  have hUb (p : E3) (hp : ‖p‖=R) : U p=H p := by
    apply piecewise_eq_of_notMem
    simp only [Metric.mem_ball,dist_zero_right,hp,lt_self_iff_false,not_false_eq_true]
  have hneg : (-F) =ᵐ[volume.restrict (Metric.ball 0 R)]
      (fun x ↦ (-H) x+(sobolevValue R (-u)) x) := by
    rw [map_neg]
    filter_upwards [hFa,ae_restrict_of_ae (Lp.coeFn_neg (sobolevValue R u))] with x h1 h2
    simp only [Pi.neg_apply,h2,h1,neg_add_rev]
    ring
  have hun := g.affine_weak_neg R u hH hu
  have hupper (f : E3 → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
      (hb : ∀ x, ‖x‖=R → H x<f x)
      (hLap : ∀ x ∈ Metric.closedBall (0:E3) R, g.laplacian f x ≤ 0) :
      ∀ x ∈ Metric.closedBall (0:E3) R, U x ≤ f x := by
    have hi := g.classical_weak_le_superharmonic R hR hH hHc hf hfc hb hLap u hu hF hFa
    intro x hx
    by_cases hb' : x ∈ Metric.ball (0:E3) R
    · rw [hUi hb']
      exact hi x hb'
    · have hs : ‖x‖=R := le_antisymm
        (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
        (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hb')
      rw [hUb x hs]
      exact (hb x hs).le
  have hlower (f : E3 → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
      (hb : ∀ x, ‖x‖=R → (-H) x<f x)
      (hLap : ∀ x ∈ Metric.closedBall (0:E3) R, g.laplacian f x ≤ 0) :
      ∀ x ∈ Metric.closedBall (0:E3) R, -f x ≤ U x := by
    have hi := g.classical_weak_le_superharmonic R hR hH.neg hHc.neg hf hfc hb hLap (-u) hun hF.neg hneg
    intro x hx
    by_cases hb' : x ∈ Metric.ball (0:E3) R
    · rw [hUi hb']
      have hh := hi x hb'
      simp only [Pi.neg_apply] at hh
      linarith
    · have hs : ‖x‖=R := le_antisymm
        (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
        (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hb')
      rw [hUb x hs]
      have hh := hb x hs
      simp only [Pi.neg_apply] at hh
      linarith
  refine ⟨U,hUi,hUb,fun p hp ↦ ?_⟩
  by_cases hi : p ∈ Metric.ball (0:E3) R
  · exact ((hF p hi).continuousAt (Metric.isOpen_ball.mem_nhds hi)).congr
      (hUi.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hi)).symm |>.continuousWithinAt
  · have hs : ‖p‖=R := le_antisymm
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)
      (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hi)
    change Tendsto U (𝓝[Metric.closedBall (0:E3) R] p) (𝓝 (U p))
    rw [hUb p hs,Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨f,hf,hfc,hfp,hfb,hfl⟩ := g.exists_boundary_majorant R hR p hs hH.continuous (ε/2) (half_pos hε)
    obtain ⟨q,hq,hqc,hqp,hqb,hql⟩ := g.exists_boundary_majorant R hR p hs hH.neg.continuous (ε/2) (half_pos hε)
    have hfe : ∀ᶠ x in 𝓝 p, f x < H p+ε :=
      hf.continuous.continuousAt.eventually (gt_mem_nhds (by rw [hfp]; linarith))
    have hqe : ∀ᶠ x in 𝓝 p, q x < -H p+ε :=
      hq.continuous.continuousAt.eventually (gt_mem_nhds (by rw [hqp]; linarith))
    filter_upwards [hfe.filter_mono nhdsWithin_le_nhds,hqe.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with x hx hy hz
    have hh := hupper f hf hfc hfb hfl x hz
    have hq' := hlower q hq hqc hqb hql x hz
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith

theorem metric_classical_dirichlet (g : SmoothMetric3) (R : ℝ) (hR : 0<R)
    {H : E3 → ℝ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H) :
    ∃ U : E3 → ℝ, ContinuousOn U (Metric.closedBall 0 R) ∧
      ContDiffOn ℝ ∞ U (Metric.ball 0 R) ∧
      (∀ p, ‖p‖=R → U p=H p) ∧
      (∀ x ∈ Metric.ball (0:E3) R, g.laplacian U x=0) := by
  obtain ⟨u,F,hu,hF,hFa,hFL⟩ := g.metric_affine_classical_open_ball R hR hH hHc
  obtain ⟨U,hUi,hUb,hUc⟩ := g.classical_weak_boundary_continuity R hR hH hHc u hu hF.continuousOn hFa
  refine ⟨U,hUc,hF.congr hUi,hUb,fun x hx ↦ ?_⟩
  rw [g.laplacian_congr_nhds (hUi.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx))]
  exact hFL x hx

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
