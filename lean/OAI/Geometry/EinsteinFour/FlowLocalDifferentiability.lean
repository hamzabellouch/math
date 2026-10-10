import OAI.Geometry.EinsteinFour.FlowVariationalExistence
import OAI.Geometry.EinsteinFour.FlowTimeReversal

namespace OAI

/-! Actual differentiability in initial data for a local autonomous flow.
The derivative is obtained from the constructed variational ODE, using the
quadratic remainder estimate; it is not an assumed property of the flow. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set Metric
open scoped ContDiff Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_differentiable_local_flow (f : E → E) (p : E)
    (hf : ContDiffAt ℝ 2 f p) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ α : E × ℝ → E, ∃ V : E × ℝ → E →L[ℝ] E,
        ContinuousOn α (ball p r ×ˢ Ioo (-ε) ε) ∧
        ContinuousOn V (ball p r ×ˢ Ioo (-ε) ε) ∧
        ∀ q ∈ ball p r,
          α (q, 0) = q ∧ V (q, 0) = ContinuousLinearMap.id ℝ E ∧
          (∀ t ∈ Ioo (-ε) ε,
            HasDerivAt (fun s => α (q, s)) (f (α (q, t))) t ∧
            HasDerivAt (fun s => V (q, s))
              ((fderiv ℝ f (α (q, t))).comp (V (q, t))) t) ∧
          ∀ t ∈ Ioo (-ε) ε, HasFDerivAt (fun x => α (x, t)) (V (q, t)) q := by
  have hf1 : ContDiffAt ℝ 1 f p := hf.of_le (by norm_num)
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ f) p := hf.fderiv_right (by norm_num)
  obtain ⟨K, U, hU, hK⟩ := hf1.exists_lipschitzOnWith
  obtain ⟨L, W, hW, hL⟩ := hDf.exists_lipschitzOnWith
  have hdiff : ∀ᶠ z in 𝓝 p, DifferentiableAt ℝ f z :=
    (hf1.eventually (by norm_num)).mono fun z hz => hz.differentiableAt (by norm_num)
  obtain ⟨a, ha, hasub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (Filter.inter_mem hU hW) hdiff)
  let B := ball p a
  have hBdiff (z : E) (hz : z ∈ B) : DifferentiableAt ℝ f z := (hasub hz).2
  have hBK : LipschitzOnWith K f B := hK.mono (fun z hz => (hasub hz).1.1)
  have hBL : LipschitzOnWith L (fderiv ℝ f) B := hL.mono (fun z hz => (hasub hz).1.2)
  obtain ⟨r, hr, ε, hε, β, hβc, hβ⟩ :=
    exists_continuous_local_variational_flow f p hf B (ball_mem_nhds p ha)
  let α : E × ℝ → E := fun z => (β z).1
  let V : E × ℝ → E →L[ℝ] E := fun z => (β z).2
  have hα0 (q : E) (hq : q ∈ ball p r) : α (q, 0) = q :=
    congrArg Prod.fst (hβ q (ball_subset_closedBall hq)).1
  have hV0 (q : E) (hq : q ∈ ball p r) : V (q, 0) = ContinuousLinearMap.id ℝ E :=
    congrArg Prod.snd (hβ q (ball_subset_closedBall hq)).1
  have hsol (q : E) (hq : q ∈ ball p r) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt (fun s => α (q, s)) (f (α (q, t))) t ∧
      HasDerivAt (fun s => V (q, s))
        ((fderiv ℝ f (α (q, t))).comp (V (q, t))) t :=
    ⟨((hβ q (ball_subset_closedBall hq)).2 t ht).2.fst,
      ((hβ q (ball_subset_closedBall hq)).2 t ht).2.snd⟩
  have hBmem (q : E) (hq : q ∈ ball p r) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      α (q, t) ∈ B := ((hβ q (ball_subset_closedBall hq)).2 t ht).1
  have hsub : ball p r ×ˢ Ioo (-ε) ε ⊆ closedBall p r ×ˢ Ioo (-ε) ε :=
    fun z hz => ⟨ball_subset_closedBall hz.1, hz.2⟩
  refine ⟨r, hr, ε, hε, α, V, hβc.fst.mono hsub, hβc.snd.mono hsub,
    fun q hq => ⟨hα0 q hq, hV0 q hq, hsol q hq, ?_⟩⟩
  intro t ht
  by_cases hnonneg : 0 ≤ t
  · have htime {s : ℝ} (hs : s ∈ Icc 0 t) : s ∈ Ioo (-ε) ε := by
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    exact hasFDerivAt_flow_endpoint f α q (ball p r) B (isOpen_ball.mem_nhds hq)
      (convex_ball p a) hBdiff K L t hnonneg hBK hBL
      (fun z hz => norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hz) hBK)
      hα0 (fun x hx s hs => (hsol x hx s (htime hs)).1)
      (fun x hx s hs => hBmem x hx s (htime hs))
      (fun s => V (q, s)) (hV0 q hq) (fun s hs => (hsol q hq s (htime hs)).2)
  · have htime {s : ℝ} (hs : s ∈ Icc t 0) : s ∈ Ioo (-ε) ε := by
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    exact hasFDerivAt_flow_endpoint_nonpos f α q (ball p r) B (isOpen_ball.mem_nhds hq)
      (convex_ball p a) hBdiff K L t (le_of_lt (lt_of_not_ge hnonneg)) hBK hBL
      (fun z hz => norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hz) hBK)
      hα0 (fun x hx s hs => (hsol x hx s (htime hs)).1)
      (fun x hx s hs => hBmem x hx s (htime hs))
      (fun s => V (q, s)) (hV0 q hq) (fun s hs => (hsol q hq s (htime hs)).2)

end
end PositiveEinsteinFour.FlowCalculus

end OAI
