import OAI.Geometry.EinsteinFour.FlowLocalDifferentiability
import Mathlib.Analysis.Calculus.FDeriv.Partial

namespace OAI

/-! The actual time derivative and the constructed initial-data derivative
give the joint derivative of a local autonomous flow. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasStrictFDerivAt_joint_flow
    (f : E → E) (α : E × ℝ → E) (V : E × ℝ → E →L[ℝ] E)
    (u : E × ℝ)
    (hinitial : ∀ᶠ z in 𝓝 u,
      HasFDerivAt (fun q => α (q, z.2)) (V z) z.1)
    (htime : ∀ᶠ z in 𝓝 u,
      HasDerivAt (fun t => α (z.1, t)) (f (α z)) z.2)
    (hV : ContinuousAt V u)
    (hvelocity : ContinuousAt (fun z => f (α z)) u) :
    HasStrictFDerivAt α
      ((V u).coprod (ContinuousLinearMap.toSpanSingleton ℝ (f (α u)))) u := by
  have ht : ∀ᶠ z in 𝓝 u, HasFDerivAt (fun t => α (z.1, t))
      (ContinuousLinearMap.toSpanSingleton ℝ (f (α z))) z.2 :=
    htime.mono fun z hz => hz.hasFDerivAt
  have hc : ContinuousAt
      (fun z => ContinuousLinearMap.toSpanSingleton ℝ (f (α z))) u :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).continuous.continuousAt.comp
      hvelocity
  exact hasStrictFDerivAt_uncurry_coprod
    (f := fun q t => α (q, t))
    (f₁ := fun q t => V (q, t))
    (f₂ := fun q t => ContinuousLinearMap.toSpanSingleton ℝ (f (α (q, t))))
    hinitial ht hV hc

/-- A C² autonomous field has an actual jointly differentiable local flow.
The linear part in the initial state is supplied by the variational ODE. -/
theorem exists_jointly_differentiable_local_flow [CompleteSpace E]
    (f : E → E) (p : E) (hf : ContDiffAt ℝ 2 f p) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ α : E × ℝ → E, ∃ V : E × ℝ → E →L[ℝ] E,
        ContinuousOn α (Metric.ball p r ×ˢ Ioo (-ε) ε) ∧
        ContinuousOn V (Metric.ball p r ×ˢ Ioo (-ε) ε) ∧
        ∀ q ∈ Metric.ball p r,
          α (q, 0) = q ∧ V (q, 0) = ContinuousLinearMap.id ℝ E ∧
          ∀ t ∈ Ioo (-ε) ε,
            HasDerivAt (fun s => α (q, s)) (f (α (q, t))) t ∧
            HasDerivAt (fun s => V (q, s))
              ((fderiv ℝ f (α (q, t))).comp (V (q, t))) t ∧
            HasStrictFDerivAt α
              ((V (q, t)).coprod
                (ContinuousLinearMap.toSpanSingleton ℝ (f (α (q, t))))) (q, t) := by
  obtain ⟨r₀, hr₀, ε₀, hε₀, α, V, hαc, hVc, hsol⟩ :=
    exists_differentiable_local_flow f p hf
  have hfnear : ∀ᶠ z in 𝓝 p, ContinuousAt f z :=
    (hf.eventually (by norm_num)).mono fun z hz => hz.continuousAt
  have hp0 : α (p, 0) = p := (hsol p (Metric.mem_ball_self hr₀)).1
  have hpD : (p, (0 : ℝ)) ∈ Metric.ball p r₀ ×ˢ Ioo (-ε₀) ε₀ :=
    ⟨Metric.mem_ball_self hr₀, by constructor <;> linarith⟩
  have hαat : ContinuousAt α (p, 0) :=
    hαc.continuousAt ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hpD)
  have hnear : ∀ᶠ z in 𝓝 (p, (0 : ℝ)), ContinuousAt f (α z) :=
    hαat.tendsto.eventually (by simpa only [hp0] using hfnear)
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let r := min r₀ (δ / 2)
  let ε := min ε₀ (δ / 2)
  have hr : 0 < r := lt_min hr₀ (half_pos hδ)
  have hε : 0 < ε := lt_min hε₀ (half_pos hδ)
  have hsub : Metric.ball p r ×ˢ Ioo (-ε) ε ⊆
      Metric.ball p r₀ ×ˢ Ioo (-ε₀) ε₀ := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    refine ⟨Metric.ball_subset_ball (min_le_left _ _) hq, ?_⟩
    have he : ε ≤ ε₀ := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨r, hr, ε, hε, α, V, hαc.mono hsub, hVc.mono hsub, ?_⟩
  intro q hq
  have hq₀ : q ∈ Metric.ball p r₀ := Metric.ball_subset_ball (min_le_left _ _) hq
  refine ⟨(hsol q hq₀).1, (hsol q hq₀).2.1, ?_⟩
  intro t ht
  have hu₀ : (q, t) ∈ Metric.ball p r₀ ×ˢ Ioo (-ε₀) ε₀ :=
    hsub (show (q, t) ∈ Metric.ball p r ×ˢ Ioo (-ε) ε from ⟨hq, ht⟩)
  have hnhds : Metric.ball p r₀ ×ˢ Ioo (-ε₀) ε₀ ∈ 𝓝 (q, t) :=
    (Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hu₀
  have hi : ∀ᶠ z in 𝓝 (q, t),
      HasFDerivAt (fun x => α (x, z.2)) (V z) z.1 := by
    filter_upwards [hnhds] with z hz
    exact (hsol z.1 hz.1).2.2.2 z.2 hz.2
  have ht' : ∀ᶠ z in 𝓝 (q, t),
      HasDerivAt (fun s => α (z.1, s)) (f (α z)) z.2 := by
    filter_upwards [hnhds] with z hz
    exact ((hsol z.1 hz.1).2.2.1 z.2 hz.2).1
  have hfc : ContinuousAt f (α (q, t)) := by
    apply hδnear
    rw [Prod.dist_eq, dist_zero_right, Real.norm_eq_abs, max_lt_iff]
    constructor
    · exact (Metric.mem_ball.mp hq).trans_le (min_le_right _ _) |>.trans
        (half_lt_self hδ)
    · exact (abs_lt.mpr ht).trans_le (min_le_right _ _) |>.trans
        (half_lt_self hδ)
  refine ⟨((hsol q hq₀).2.2.1 t hu₀.2).1,
    ((hsol q hq₀).2.2.1 t hu₀.2).2, ?_⟩
  exact hasStrictFDerivAt_joint_flow f α V (q, t) hi ht'
    (hVc.continuousAt hnhds) (hfc.comp (hαc.continuousAt hnhds))

end
end PositiveEinsteinFour.FlowCalculus

end OAI
