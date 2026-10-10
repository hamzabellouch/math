import OAI.Geometry.Riemannian.HarmonicCore.MetricLaplacian
import OAI.Geometry.Riemannian.HarmonicCore.SmoothBootstrap

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

lemma metric_energy_gradient_flux (g : SmoothMetric3) (F φ : E3 → ℝ) (x : E3) :
    ⟪g.energyOperator x (gradient F x),gradient φ x⟫_ℝ =
      ∑ i,coordDeriv φ i x*g.metricFlux F x i := by
  have hg (f : E3 → ℝ) (i : Fin 3) : gradient f x i = coordDeriv f i x := by
    change _ = fderiv ℝ f x (coordinateVector i)
    have h := inner_gradient_left (𝕜:=ℝ) (f:=f) (x:=x) (y:=coordinateVector i)
    simpa only [coordinateVector,EuclideanSpace.inner_single_right,RCLike.inner_apply,starRingEnd_apply,star_trivial,mul_one,one_mul,conj_trivial] using h
  change ⟪WithLp.toLp 2 (g.energyMatrix x *ᵥ (gradient F x).ofLp),gradient φ x⟫_ℝ = _
  simp only [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial,
    Matrix.mulVec,dotProduct,hg,metricFlux]

theorem metric_weak_classical_harmonic (g : SmoothMetric3) (r S T : ℝ)
    (hr : 0 < r) (hrS : r < S) (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      (∫ x, ⟪g.energyOperator x ((sobolevDerivative T u) x),
        (sobolevDerivative S v) x⟫_ℝ) = 0) :
    ∃ U : E3 →ᵇ ℝ, ContDiff ℝ ∞ (U:E3 → ℝ) ∧
      (U:E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)] (sobolevValue T u : E3 → ℝ) ∧
      ∀ x ∈ Metric.ball (0:E3) r, g.laplacian U x = 0 := by
  obtain ⟨R,hrR,hRS⟩ := exists_between hrS
  obtain ⟨U,hUd,hUa⟩ := g.metric_weak_smooth R S T (hr.trans hrR) hRS u hu
  obtain ⟨V,W,hW,hVa,hWa,hVd⟩ := g.metric_weak_classical_first R S T (hr.trans hrR) hRS u hu
  have he : EqOn (U:E3 → ℝ) (V:E3 → ℝ) (Metric.ball 0 R) :=
    (volume : Measure E3).eqOn_open_of_ae_eq (hUa.trans hVa.symm) Metric.isOpen_ball
      U.continuous.continuousOn V.continuous.continuousOn
  have hgrad (x : E3) (hx : x ∈ Metric.ball (0:E3) R) : gradient (U:E3 → ℝ) x = W x := by
    have hd : HasFDerivAt (U:E3 → ℝ) (InnerProductSpace.toDual ℝ E3 (W x)) x :=
      (hVd x hx).congr_of_eventuallyEq (he.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx))
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hd.hasGradientAt.gradient
  have hga : gradient (U:E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)]
      (sobolevDerivative T u : E3 → E3) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball hrR.le) hWa,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hy
    rw [hgrad x (Metric.ball_subset_ball hrR.le hy)]
    exact hx
  refine ⟨U,hUd,ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball hrR.le) hUa,?_⟩
  apply g.laplacian_eq_zero_of_weak_energy r hUd
  intro φ hφ hφc hφs
  let ψ : DirichletTest S := ⟨φ,hφ,hφc,hφs.trans (Metric.ball_subset_ball hrS.le)⟩
  let v : ZeroSobolev S := testSobolev S ψ
  have hv : (sobolevDerivative S v : E3 → E3) =ᵐ[volume] gradient φ :=
    ψ.derivative_memLp.coeFn_toLp
  rw [←hu v]
  apply integral_congr_ae
  have hga' := (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hga
  filter_upwards [hv,hga'] with x hx hy
  rw [hx,←g.metric_energy_gradient_flux]
  by_cases hxr : x ∈ Metric.ball (0:E3) r
  · rw [hy hxr]
  · have hxt : x ∉ tsupport φ := fun h ↦ hxr (hφs h)
    have hgφ : gradient φ x=0 := by simp only [gradient,fderiv_of_notMem_tsupport ℝ hxt,map_zero]
    rw [hgφ,inner_zero_right,inner_zero_right]



theorem metric_affine_classical_interior (g : SmoothMetric3) (R : ℝ) (hR : 0 < R)
    {F : E3 → ℝ} (hF : ContDiff ℝ ∞ F) (hcompact : HasCompactSupport F) :
    ∃ u : ZeroSobolev R,
      (∀ v : ZeroSobolev R,
        (∫ x, ⟪g.energyOperator x (gradient F x+(sobolevDerivative R u) x),
          (sobolevDerivative R v) x⟫_ℝ) = 0) ∧
      ∀ r : ℝ, 0 < r → r < R → ∃ U : E3 →ᵇ ℝ,
        ContDiff ℝ ∞ (U:E3 → ℝ) ∧
        (U:E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)]
          (fun x ↦ F x+(sobolevValue R u) x) ∧
        ∀ x ∈ Metric.ball (0:E3) r, g.laplacian U x = 0 := by
  obtain ⟨u,hu,_⟩ := g.metric_affine_weak_dirichlet R hR.le hF hcompact
  obtain ⟨T,hRT,hTs⟩ := compact_test_extension hF hcompact R
  let φ : DirichletTest T := ⟨F,hF,hcompact,hTs⟩
  let w : ZeroSobolev T := testSobolev T φ+includeSobolev hRT u
  have hw : ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.energyOperator x ((sobolevDerivative T w) x),(sobolevDerivative R v) x⟫_ℝ) = 0 := by
    intro v
    rw [←hu v]
    apply integral_congr_ae
    filter_upwards [affineSobolev_derivative hRT φ u] with x hx
    rw [hx]
  refine ⟨u,hu,fun r hr hrR ↦ ?_⟩
  obtain ⟨U,hUd,hU,hUh⟩ := g.metric_weak_classical_harmonic r R T hr hrR w hw
  exact ⟨U,hUd,hU.trans ((affineSobolev_value hRT φ u).filter_mono ae_restrict_le),hUh⟩



lemma laplacian_congr_nhds (g : SmoothMetric3) {f h : E3 → ℝ} {x : E3}
    (he : f =ᶠ[𝓝 x] h) : g.laplacian f x = g.laplacian h x := by
  unfold laplacian coordDeriv
  rw [he.fderiv_eq,(he.iteratedFDeriv ℝ 2).eq_of_nhds]

lemma glue_classical_inner_balls (g : SmoothMetric3) (R : ℝ) (w : E3 → ℝ)
    (h : ∀ r : ℝ, 0 < r → r < R → ∃ U : E3 →ᵇ ℝ,
      ContDiff ℝ ∞ (U:E3 → ℝ) ∧
      (U:E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)] w ∧
      ∀ x ∈ Metric.ball (0:E3) r, g.laplacian U x = 0) :
    ∃ F : E3 → ℝ, ContDiffOn ℝ ∞ F (Metric.ball 0 R) ∧
      F =ᵐ[volume.restrict (Metric.ball 0 R)] w ∧
      ∀ x ∈ Metric.ball (0:E3) R, g.laplacian F x = 0 := by
  classical
  let I := {q : ℚ // 0 < (q:ℝ) ∧ (q:ℝ) < R}
  let rad (q : I) : ℝ := q.val
  have hrep (q : I) := h (rad q) q.property.1 q.property.2
  choose U hUd hUa hUh using hrep
  have hcover : ∀ x ∈ Metric.ball (0:E3) R, ∃ q : I, x ∈ Metric.ball (0:E3) (rad q) := by
    intro x hx
    have hx' : ‖x‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    obtain ⟨q,hxq,hqR⟩ := exists_rat_btwn hx'
    exact ⟨⟨q,lt_of_le_of_lt (norm_nonneg x) hxq,hqR⟩,by simpa only [Metric.mem_ball,dist_zero_right] using hxq⟩
  have hcompat (p q : I) (x : E3)
      (hp : x ∈ Metric.ball (0:E3) (rad p)) (hq : x ∈ Metric.ball (0:E3) (rad q)) : U p x=U q x := by
    let s := Metric.ball (0:E3) (min (rad p) (rad q))
    have hap : (U p:E3 → ℝ) =ᵐ[volume.restrict s] w :=
      ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball (min_le_left (rad p) (rad q))) (hUa p)
    have haq : (U q:E3 → ℝ) =ᵐ[volume.restrict s] w :=
      ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball (min_le_right (rad p) (rad q))) (hUa q)
    have ha : (U p:E3 → ℝ) =ᵐ[volume.restrict s] (U q:E3 → ℝ) := hap.trans haq.symm
    exact ((volume:Measure E3).eqOn_open_of_ae_eq ha Metric.isOpen_ball
      (U p).continuous.continuousOn (U q).continuous.continuousOn)
      (by simpa only [s,Metric.mem_ball,lt_min_iff] using And.intro hp hq)
  let F (x : E3) : ℝ := if hx : x ∈ Metric.ball (0:E3) R then U (Classical.choose (hcover x hx)) x else 0
  have hFeq (q : I) : EqOn F (U q:E3 → ℝ) (Metric.ball (0:E3) (rad q)) := by
    intro x hx
    have hxR : x ∈ Metric.ball (0:E3) R := Metric.ball_subset_ball q.property.2.le hx
    change (if hx : x ∈ Metric.ball (0:E3) R then U (Classical.choose (hcover x hx)) x else 0) = _
    rw [dite_eq_left hxR]
    exact hcompat _ q x (Classical.choose_spec (hcover x hxR)) hx
  have hFn (q : I) (x : E3) (hx : x ∈ Metric.ball (0:E3) (rad q)) : F =ᶠ[𝓝 x] (U q:E3 → ℝ) :=
    (hFeq q).eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx)
  have hball : Metric.ball (0:E3) R = ⋃ q : I, Metric.ball (0:E3) (rad q) := by
    ext x
    exact ⟨fun hx ↦ mem_iUnion.mpr (hcover x hx),fun hx ↦ by
      obtain ⟨q,hq⟩ := mem_iUnion.mp hx
      exact Metric.ball_subset_ball q.property.2.le hq⟩
  refine ⟨F,?_,?_,?_⟩
  · intro x hx
    obtain ⟨q,hq⟩ := hcover x hx
    exact (((hUd q).contDiffAt).congr_of_eventuallyEq (hFn q x hq)).contDiffWithinAt
  · rw [hball,ae_eq_restrict_iUnion_iff]
    intro q
    exact ((hFeq q).aeEq_restrict Metric.isOpen_ball.measurableSet).trans (hUa q)
  · intro x hx
    obtain ⟨q,hq⟩ := hcover x hx
    rw [g.laplacian_congr_nhds (hFn q x hq)]
    exact hUh q x hq

theorem metric_affine_classical_open_ball (g : SmoothMetric3) (R : ℝ) (hR : 0 < R)
    {H : E3 → ℝ} (hH : ContDiff ℝ ∞ H) (hcompact : HasCompactSupport H) :
    ∃ u : ZeroSobolev R, ∃ F : E3 → ℝ,
      (∀ v : ZeroSobolev R,
        (∫ x, ⟪g.energyOperator x (gradient H x+(sobolevDerivative R u) x),
          (sobolevDerivative R v) x⟫_ℝ) = 0) ∧
      ContDiffOn ℝ ∞ F (Metric.ball 0 R) ∧
      F =ᵐ[volume.restrict (Metric.ball 0 R)] (fun x ↦ H x+(sobolevValue R u) x) ∧
      ∀ x ∈ Metric.ball (0:E3) R, g.laplacian F x = 0 := by
  obtain ⟨u,hu,hr⟩ := g.metric_affine_classical_interior R hR hH hcompact
  obtain ⟨F,hF,ha,hh⟩ := g.glue_classical_inner_balls R _ hr
  exact ⟨u,F,hu,hF,ha,hh⟩

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
