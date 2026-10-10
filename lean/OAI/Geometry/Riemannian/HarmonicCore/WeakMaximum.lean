import OAI.Geometry.Riemannian.HarmonicCore.SobolevComposition

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

lemma smoothTransition_deriv_bound : ∃ K : NNReal, ∀ t, ‖deriv Real.smoothTransition t‖ ≤ K := by
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    apply (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ isClosed_Icc
    intro x hx
    by_contra hn
    have hnot : x < 0 ∨ 1 < x := by simpa only [mem_Icc,not_and_or,not_le] using hn
    rcases hnot with hneg|hpos
    · have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ ↦ (0:ℝ)) := by
        filter_upwards [eventually_lt_nhds hneg] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      exact hx (he.deriv_eq.trans (deriv_const x 0))
    · have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ ↦ (1:ℝ)) := by
        filter_upwards [eventually_gt_nhds hpos] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      exact hx (he.deriv_eq.trans (deriv_const x 1))
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous
    ((show ContDiff ℝ ∞ Real.smoothTransition from Real.smoothTransition.contDiff).continuous_deriv (by simp))
  exact ⟨⟨max C 0,le_max_right _ _⟩,fun t ↦ (hC t).trans (le_max_left _ _)⟩

lemma weak_maximum_from_transition (R : ℝ) (A : E3 → E3 →L[ℝ] E3) (C c : ℝ) (hc : 0<c)
    (hA : AEStronglyMeasurable A (volume : Measure E3)) (hbound : ∀ x, ‖A x‖ ≤ C)
    (hpos : ∀ x z, c*‖z‖^2 ≤ ⟪A x z,z⟫_ℝ)
    (w : ValueL2) (z : DerivativeL2) (v : ZeroSobolev R)
    (hv : (sobolevValue R v : E3 → ℝ) =ᵐ[volume] (fun x ↦ Real.smoothTransition (w x)))
    (hd : (sobolevDerivative R v : E3 → E3) =ᵐ[volume]
      (fun x ↦ deriv Real.smoothTransition (w x) • z x))
    (hweak : ⟪coefficientCLM A C hA hbound z,sobolevDerivative R v⟫_ℝ ≤ 0) :
    ∀ᵐ x ∂volume, w x ≤ 0 := by
  let f (x : E3) := ⟪(coefficientCLM A C hA hbound z) x,(sobolevDerivative R v) x⟫_ℝ
  have hi : Integrable f (volume : Measure E3) := L2.integrable_inner _ _
  have he : f =ᵐ[volume] (fun x ↦ deriv Real.smoothTransition (w x)*⟪A x (z x),z x⟫_ℝ) := by
    filter_upwards [(coefficient_memLp A C hA hbound z).coeFn_toLp,hd] with x h1 h2
    change (coefficientCLM A C hA hbound z) x = _ at h1
    dsimp only [f]
    rw [h1,h2,inner_smul_right]
  have hnn : 0 ≤ᵐ[volume] f := by
    filter_upwards [he] with x hx
    rw [hx]
    exact mul_nonneg Real.smoothTransition.monotone.deriv_nonneg
      ((mul_nonneg hc.le (sq_nonneg _)).trans (hpos x (z x)))
  have hiz : ∫ x, f x = 0 := by
    apply le_antisymm _ (integral_nonneg_of_ae hnn)
    simpa only [L2.inner_def] using hweak
  have hfz := (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hiz
  have hdz : sobolevDerivative R v=0 := by
    apply Lp.ext
    filter_upwards [hfz,he,hd,Lp.coeFn_zero E3 2 (volume:Measure E3)] with x h1 h2 h3 h4
    rw [h3,h4]
    have heq : deriv Real.smoothTransition (w x)*⟪A x (z x),z x⟫_ℝ=0 := h2.symm.trans h1
    rcases mul_eq_zero.mp heq with ha|hb
    · simp only [ha,zero_smul,Pi.zero_apply]
    · have hp := hpos x (z x)
      rw [hb] at hp
      have hs : ‖z x‖^2 ≤ 0 := by
        by_contra hn
        have ht := mul_pos hc (lt_of_not_ge hn)
        linarith
      have hn : ‖z x‖=0 := by nlinarith [norm_nonneg (z x)]
      simp only [norm_eq_zero.mp hn,smul_zero,Pi.zero_apply]
  have hvz : sobolevValue R v=0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [hdz,norm_zero,mul_zero] using sobolev_poincare R v
  have hvz' : (sobolevValue R v : E3 → ℝ) =ᵐ[volume] 0 := by
    simpa only [hvz] using Lp.coeFn_zero ℝ 2 (volume:Measure E3)
  filter_upwards [hv,hvz'] with x h1 h2
  by_contra hn
  have hp := Real.smoothTransition.pos_of_pos (lt_of_not_ge hn)
  exact (ne_of_gt hp) (h1.symm.trans h2)

theorem affine_weak_maximum (R S : ℝ) (H : DirichletTest S) (u : ZeroSobolev R)
    (hS : tsupport (Real.smoothTransition ∘ (H:E3 → ℝ)) ⊆ Metric.ball 0 R)
    (A : E3 → E3 →L[ℝ] E3) (C c : ℝ) (hc : 0<c)
    (hA : AEStronglyMeasurable A (volume : Measure E3)) (hbound : ∀ x, ‖A x‖ ≤ C)
    (hpos : ∀ x z, c*‖z‖^2 ≤ ⟪A x z,z⟫_ℝ)
    (hw : ∀ v : ZeroSobolev R, (∀ᵐ x ∂volume, 0 ≤ (sobolevValue R v) x) →
      ⟪coefficientCLM A C hA hbound (testDerivativeLinear S H+sobolevDerivative R u),
        sobolevDerivative R v⟫_ℝ ≤ 0) :
    ∀ᵐ x ∂volume, (testValueLinear S H+sobolevValue R u) x ≤ 0 := by
  obtain ⟨K,hK⟩ := smoothTransition_deriv_bound
  obtain ⟨v,hv,hd⟩ := sobolev_affine_smooth_composition R S H Real.smoothTransition
    Real.smoothTransition.contDiff (Real.smoothTransition.zero_of_nonpos le_rfl) hS K hK u
  refine weak_maximum_from_transition R A C c hc hA hbound hpos _ _ v hv hd (hw v ?_)
  filter_upwards [hv] with x hx
  rw [hx]
  exact Real.smoothTransition.nonneg _



lemma negative_sphere_collar (R : ℝ) (hR : 0<R) {f : E3 → ℝ} (hf : Continuous f)
    (hb : ∀ x, ‖x‖=R → f x<0) :
    ∃ δ : ℝ, 0<δ ∧ δ<R ∧ ∀ x, |‖x‖-R|<δ → f x<0 := by
  let K := Metric.closedBall (0:E3) (R+1) ∩ {x | 0 ≤ f x}
  have hK : IsCompact K := (isCompact_closedBall (0:E3) (R+1)).inter_right
    (isClosed_le continuous_const hf)
  have hc : Continuous (fun x : E3 ↦ |‖x‖-R|) := (continuous_norm.sub continuous_const).abs
  by_cases he : K.Nonempty
  · obtain ⟨y,hy,hmin⟩ := hK.exists_isMinOn he hc.continuousOn
    have hd : 0 < |‖y‖-R| := by
      apply abs_pos.mpr
      intro hz
      exact (not_lt_of_ge hy.2) (hb y (sub_eq_zero.mp hz))
    let δ := min R (min 1 |‖y‖-R|)/2
    have hm : 0 < min R (min 1 |‖y‖-R|) := lt_min hR (lt_min zero_lt_one hd)
    have hp : 0<δ := half_pos hm
    have hδR : δ<R := (half_lt_self hm).trans_le (min_le_left _ _)
    have hδ1 : δ<1 := (half_lt_self hm).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hδd : δ < |‖y‖-R| := (half_lt_self hm).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨δ,hp,hδR,fun x hx ↦ ?_⟩
    by_contra hn
    have hxn : ‖x‖ ≤ R+1 := by have := (abs_lt.mp hx).2; linarith
    have hxK : x ∈ K := ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxn,not_lt.mp hn⟩
    have hm' : |‖y‖-R| ≤ |‖x‖-R| := hmin hxK
    linarith
  · refine ⟨min R 1/2,half_pos (lt_min hR zero_lt_one),?_,fun x hx ↦ ?_⟩
    · exact (half_lt_self (lt_min hR zero_lt_one)).trans_le (min_le_left _ _)
    · by_contra hn
      apply he
      refine ⟨x,?_,not_lt.mp hn⟩
      have hm : min R 1/2<1 := (half_lt_self (lt_min hR zero_lt_one)).trans_le (min_le_right _ _)
      have hx' := (abs_lt.mp hx).2
      simpa only [Metric.mem_closedBall,dist_zero_right] using (show ‖x‖ ≤ R+1 by linarith)

lemma strict_boundary_test_extension (R : ℝ) (hR : 0<R) {f : E3 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hb : ∀ x, ‖x‖=R → f x<0) :
    ∃ S : ℝ, ∃ H : DirichletTest S,
      EqOn (H:E3 → ℝ) f (Metric.closedBall 0 R) ∧
      tsupport (Real.smoothTransition ∘ (H:E3 → ℝ)) ⊆ Metric.ball 0 R := by
  obtain ⟨δ,hδ,hδR,hneg⟩ := negative_sphere_collar R hR hf.continuous hb
  let χ : ContDiffBump (0:E3) := ⟨R+δ/4,R+δ/2,by linarith,by linarith⟩
  let F : E3 → ℝ := fun x ↦ χ x*f x
  have hFc : HasCompactSupport F := χ.hasCompactSupport.mul_right
  have hFs : tsupport F ⊆ Metric.ball (0:E3) (R+δ) := by
    apply (show tsupport F ⊆ tsupport (χ:E3 → ℝ) from tsupport_mul_subset_left).trans
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [χ]; linarith)
  let H : DirichletTest (R+δ) := ⟨F,χ.contDiff.mul hf,hFc,hFs⟩
  refine ⟨R+δ,H,?_,?_⟩
  · intro x hx
    have hχ : χ x=1 := χ.one_of_mem_closedBall
      (Metric.closedBall_subset_closedBall (show R≤χ.rIn by dsimp [χ]; linarith) hx)
    change χ x*f x=f x
    rw [hχ,one_mul]
  · apply (show tsupport (Real.smoothTransition ∘ (H:E3 → ℝ)) ⊆
        Metric.closedBall (0:E3) (R-δ/2) from ?_).trans
      (Metric.closedBall_subset_ball (by linarith))
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra hn
    have hxn : R-δ/2<‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hn
    have hnon : F x ≤ 0 := by
      by_cases hz : χ x=0
      · simp only [F,hz,zero_mul,le_refl]
      · have hxout : ‖x‖<R+δ/2 := by
          have hs : x ∈ Metric.ball (0:E3) χ.rOut := by
            rw [←χ.support_eq]
            exact hz
          simpa only [Metric.mem_ball,dist_zero_right] using hs
        have hfx := hneg x (abs_lt.mpr (by constructor <;> linarith))
        exact mul_nonpos_of_nonneg_of_nonpos χ.nonneg hfx.le
    apply hx
    exact Real.smoothTransition.zero_of_nonpos hnon

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
