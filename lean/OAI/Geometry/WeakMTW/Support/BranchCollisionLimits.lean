import Mathlib
import OAI.Geometry.WeakMTW.Support.CollisionBranches
import OAI.Geometry.WeakMTW.Support.CollisionGradient
import OAI.Geometry.WeakMTW.Support.CollisionGeometry
import OAI.Geometry.WeakMTW.Support.ActiveRepresentation
import OAI.Geometry.WeakMTW.Support.CollisionCalculus
import OAI.Geometry.WeakMTW.Support.NormalizedSeparation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem branch_collision_limits (y : ι → M) (h : ι → ℝ)
    {p q : ℕ → TangentBundle (model n) M} {p₀ : TangentBundle (model n) M}
    (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto (fun j => (q j).1) atTop (𝓝 p₀.1))
    {sⱼ : ℕ → ℝ} {s ℓ : ℝ} (hs : Tendsto sⱼ atTop (𝓝 s))
    (hqp : Tendsto (fun j => mulState (sⱼ j) (q j)) atTop (𝓝 (mulState s p₀)))
    (hpos : ∀ᶠ j in atTop, 0 < sⱼ j) (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1)
    (hcollision : ∀ᶠ j in atTop, exp (p j).1 (sⱼ j•(p j).2) = exp (q j).1 (sⱼ j•(q j).2))
    (hvalue : ∀ᶠ j in atTop, scaledPoleValue y h (sⱼ j) (q j) ≤ scaledPoleValue y h (sⱼ j) (p j))
    (R : ∀ j, ActiveRepresentation y h (p j)) (R₀ : ActiveRepresentation y h p₀)
    (hθ : ∀ i, Tendsto (fun j => (R j).θ i) atTop (𝓝 (R₀.θ i)))
    (ha : ∀ i, Tendsto (fun j => (⟨(p j).1,(R j).a i⟩ : TangentBundle (model n) M))
      atTop (𝓝 ⟨p₀.1,R₀.a i⟩))
    (B : ActionBranch (n := n) p₀.1 (exp p₀.1 (s•p₀.2)))
    (hB : stateChart p₀.1 (mulState s p₀) ∈ B.coord.source)
    (C : ∀ i, ActionBranch (n := n) p₀.1 (exp p₀.1 (ℓ•R₀.a i)))
    (hC : ∀ i, stateChart p₀.1 (⟨p₀.1,ℓ•R₀.a i⟩ : TangentBundle (model n) M) ∈ (C i).coord.source)
    {e : Model n}
    (hd : Tendsto (fun j => NormedSpace.normalize
      (chartAt (Model n) p₀.1 (q j).1 - chartAt (Model n) p₀.1 (p j).1)) atTop (𝓝 e))
    (hne : ∀ᶠ j in atTop, chartAt (Model n) p₀.1 (q j).1 ≠ chartAt (Model n) p₀.1 (p j).1) :
    (∀ i, fderiv ℝ B.value (chartAt (Model n) p₀.1 p₀.1,
        chartAt (Model n) (exp p₀.1 (s•p₀.2)) (exp p₀.1 (s•p₀.2))) (e,0) -
      (s/ℓ)*fderiv ℝ (C i).value (chartAt (Model n) p₀.1 p₀.1,
        chartAt (Model n) (exp p₀.1 (ℓ•R₀.a i)) (exp p₀.1 (ℓ•R₀.a i))) (e,0) ≤ 0) ∧
    (∑ i, R₀.θ i*(fderiv ℝ (fderiv ℝ B.value)
      (chartAt (Model n) p₀.1 p₀.1,chartAt (Model n) (exp p₀.1 (s•p₀.2)) (exp p₀.1 (s•p₀.2))) (e,0) (e,0) -
      (s/ℓ)*fderiv ℝ (fderiv ℝ (C i).value)
        (chartAt (Model n) p₀.1 p₀.1,chartAt (Model n) (exp p₀.1 (ℓ•R₀.a i)) (exp p₀.1 (ℓ•R₀.a i))) (e,0) (e,0))) ≤ 0 := by
  let x := p₀.1
  let z := exp p₀.1 (s•p₀.2)
  let w := fun i => exp p₀.1 (ℓ•R₀.a i)
  let xp := fun j => chartAt (Model n) x (p j).1
  let xq := fun j => chartAt (Model n) x (q j).1
  let yp := fun j => chartAt (Model n) z (exp (p j).1 (sⱼ j•(p j).2))
  let ap := fun j i => chartAt (Model n) (w i) (exp (p j).1 (ℓ•(R j).a i))
  have hpS : mulState s p₀ ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hpp := tangentScale_continuous.continuousAt.tendsto.comp (hs.prodMk_nhds hp)
  have hBp := B.eventually_source hpp hpS hB
  have hBq := B.eventually_source hqp hpS hB
  have hpa (i : ActiveIndex n) : Tendsto
      (fun j => (⟨(p j).1,ℓ•(R j).a i⟩ : TangentBundle (model n) M)) atTop
      (𝓝 (⟨x,ℓ•R₀.a i⟩ : TangentBundle (model n) M)) :=
    tangentScale_continuous.continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds (ha i))
  have hCy (i : ActiveIndex n) := bundle_endpoint_limit (hpa i)
  have hCi (i : ActiveIndex n) : ℓ•R₀.a i ∈ injectivityDomain x :=
    strict_radial_mem_injectivity (R₀.active i).1 hℓ.le hℓ₁
  have hCp := eventually_all.mpr (fun i => (C i).eventually_source (hpa i)
    ((stateChart_source x _).mpr (mem_chart_source (Model n) x)) (hC i))
  have hCpV := eventually_all.mpr (fun i => (C i).eq_cost_along (hCi i) (hC i)
    (bundle_base_limit hp) (hCy i) (mem_chart_source (Model n) (w i)))
  have hCqV := eventually_all.mpr (fun i => (C i).eq_cost_along (hCi i) (hC i)
    hq (hCy i) (mem_chart_source (Model n) (w i)))
  have hxp : Tendsto xp atTop (𝓝 (chartAt (Model n) x x)) := base_chart_limit hp
  have hxq : Tendsto xq atTop (𝓝 (chartAt (Model n) x x)) :=
    ((chartAt (Model n) x).continuousAt (mem_chart_source (Model n) x)).tendsto.comp hq
  have hyp : Tendsto yp atTop (𝓝 (chartAt (Model n) z z)) := scaled_endpoint_chart_limit hp hs
  have hap (i : ActiveIndex n) : Tendsto (fun j => ap j i) atTop (𝓝 (chartAt (Model n) (w i) (w i))) :=
    ((chartAt (Model n) (w i)).continuousAt (mem_chart_source (Model n) (w i))).tendsto.comp (hCy i)
  have hBt := B.smooth_value.contDiffAt (B.coord.open_target.mem_nhds (B.target_state _ hpS hB))
  have hCt (i : ActiveIndex n) : ContDiffAt ℝ ∞ (C i).value
      (chartAt (Model n) x x,chartAt (Model n) (w i) (w i)) := by
    have hAiS : (⟨x,ℓ•R₀.a i⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
      (stateChart_source x _).mpr (mem_chart_source (Model n) x)
    exact (C i).smooth_value.contDiffAt ((C i).coord.open_target.mem_nhds
      ((C i).target_state (⟨x,ℓ•R₀.a i⟩ : TangentBundle (model n) M) hAiS (hC i)))
  apply MovingTaylor.collision_limits hBt hCt hxp hd hyp hap (hs.div_const ℓ) hθ
    (MovingTaylor.separation_scale_limit hxp hxq)
  · filter_upwards [hne] with j hj
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hj)
  · exact Filter.Eventually.of_forall (fun j => (R j).nonneg)
  · filter_upwards [hBp,hBq,hpos,hcollision,hvalue,hCpV,hCqV] with j hjp hjq hjs hje hjv hjCp hjCq
    intro i
    rw [MovingTaylor.separation_identity]
    exact branch_support_inequality y h hjs.le hℓ hℓ₁ ((R j).active i) B (C i)
      hjp.1 hjq.1 hjp.2 hjq.2 hje hjv (hjCp i) (hjCq i)
  · filter_upwards [hBp,hCp] with j hjp hjC
    exact branch_gradient_weighted (R j).a (R j).θ (R j).sum_one (R j).bary hℓ.ne'
      ((stateChart_source x _).mp hjp.1) B hjp.2 w C (fun i => (hjC i).2) _

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
