import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.IntrinsicUniqueness
import OAI.Geometry.WeakMTW.Coordinates.TwoPointSpeed

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open ChartMetric CoordinateGeometry

 theorem coordinate_corner_deriv_eq (x : M) {c d : ℝ → E} {u v : E} {C : ℝ}
    (hc : HasDerivAt c u 0) (hd : HasDerivAt d v 0) (h0 : c 0 = d 0)
    (ht : c 0 ∈ (chartAt E x).target)
    (hu : metric x (c 0) u u = C ^ 2) (hv : metric x (c 0) v v = C ^ 2)
    (he : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      dist ((chartAt E x).symm (c (-t))) ((chartAt E x).symm (d t)) = 2*C*t) : u = v := by
  have hc' : HasDerivAt (fun t => c (-t)) (-u) 0 := by
    simpa only [neg_zero,neg_smul,one_smul,Function.comp_def] using hc.scomp_of_eq 0 (hasDerivAt_neg (0 : ℝ)) (by simp)
  have H := two_point_coordinate_speed x hc' hd (by simpa only [neg_zero] using h0)
    (by simpa only [neg_zero] using ht) he
  simp only [neg_zero, sub_neg_eq_add] at H
  have hsym := metric_symmetric x (c 0) u v
  have hz : metric x (c 0) (u-v) (u-v) = 0 := by
    simp only [map_add,add_apply] at H
    simp only [map_sub,sub_apply]
    nlinarith
  by_contra hne
  have hp := metric_positive x ht (sub_ne_zero.mpr hne)
  linarith

 theorem intrinsic_no_corner {γ η : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hη : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ η)
    {C : ℝ} (hC : 0 ≤ C)
    (hγd : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball 0 ε, ∀ t ∈ Metric.ball 0 ε,
      dist (γ s) (γ t) = C * |s-t|)
    (hηd : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball 0 ε, ∀ t ∈ Metric.ball 0 ε,
      dist (η s) (η t) = C * |s-t|)
    (h0 : γ 0 = η 0)
    (he : ∀ᶠ t in 𝓝[>] (0 : ℝ), dist (γ (-t)) (η t) = 2*C*t) :
    curveState (E := E) γ 0 = curveState (E := E) η 0 := by
  let x := γ 0
  let e := chartAt E x
  have hγ₀ : γ 0 ∈ e.source := mem_chart_source E (γ 0)
  have hη₀ : η 0 ∈ e.source := by rw [← h0]; exact hγ₀
  obtain ⟨ε,hε,hγdist⟩ := hγd
  obtain ⟨δ,hδ,hηdist⟩ := hηd
  let U : Set ℝ := Metric.ball 0 ε ∩ Metric.ball 0 δ ∩ (γ ⁻¹' e.source ∩ η ⁻¹' e.source)
  have hU : IsOpen U := (Metric.isOpen_ball.inter Metric.isOpen_ball).inter
    ((e.open_source.preimage hγ.continuous).inter (e.open_source.preimage hη.continuous))
  have h0U : (0 : ℝ) ∈ U := ⟨⟨Metric.mem_ball_self hε,Metric.mem_ball_self hδ⟩,hγ₀,hη₀⟩
  let c := e ∘ γ
  let d := e ∘ η
  have hc : ContDiffOn ℝ ∞ c U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp hγ.contMDiffOn (fun t ht => ht.2.1))
  have hd : ContDiffOn ℝ ∞ d U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp hη.contMDiffOn (fun t ht => ht.2.2))
  have hcd : HasDerivAt c (deriv c 0) 0 :=
    (((hc 0 h0U).contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasDerivAt
  have hdd : HasDerivAt d (deriv d 0) 0 :=
    (((hd 0 h0U).contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasDerivAt
  have hct : ∀ t ∈ U, c t ∈ e.target := fun t ht => e.map_source ht.2.1
  have hdt : ∀ t ∈ U, d t ∈ e.target := fun t ht => e.map_source ht.2.2
  have hdistc : ∀ s ∈ U, ∀ t ∈ U, dist (e.symm (c s)) (e.symm (c t)) = C*|s-t| := by
    intro s hs t ht
    change dist (e.symm (e (γ s))) (e.symm (e (γ t))) = _
    rw [e.left_inv hs.2.1,e.left_inv ht.2.1]
    exact hγdist s hs.1.1 t ht.1.1
  have hdistd : ∀ s ∈ U, ∀ t ∈ U, dist (e.symm (d s)) (e.symm (d t)) = C*|s-t| := by
    intro s hs t ht
    change dist (e.symm (e (η s))) (e.symm (e (η t))) = _
    rw [e.left_inv hs.2.2,e.left_inv ht.2.2]
    exact hηdist s hs.1.2 t ht.1.2
  have hu := coordinate_speed_of_local_distance x hcd (hct 0 h0U) hC (by
    filter_upwards [hU.mem_nhds h0U] with t ht
    rw [hdistc 0 h0U t ht,abs_sub_comm])
  have hv := coordinate_speed_of_local_distance x hdd (hdt 0 h0U) hC (by
    filter_upwards [hU.mem_nhds h0U] with t ht
    rw [hdistd 0 h0U t ht,abs_sub_comm])
  have hcd0 : c 0 = d 0 := congrArg e h0
  rw [← hcd0] at hv
  have hec : ∀ᶠ t in 𝓝[>] (0 : ℝ), dist (e.symm (c (-t))) (e.symm (d t)) = 2*C*t := by
    have hneg : ∀ᶠ t in 𝓝 (0 : ℝ), -t ∈ U :=
      (continuous_neg.continuousAt.preimage_mem_nhds (by simpa only [neg_zero] using hU.mem_nhds h0U))
    have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ U := hU.mem_nhds h0U
    filter_upwards [he,hneg.filter_mono nhdsWithin_le_nhds,hmem.filter_mono nhdsWithin_le_nhds]
      with t ht hn hm
    change dist (e.symm (e (γ (-t)))) (e.symm (e (η t))) = _
    rwa [e.left_inv hn.2.1,e.left_inv hm.2.2]
  have hdereq := coordinate_corner_deriv_eq x hcd hdd hcd0 (hct 0 h0U) hu hv hec
  have hgerm := coordinate_germ_unique x hU hc hd hct hdt h0U hC hC hdistc hdistd hcd0 hdereq
  apply curveState_congr
  filter_upwards [hgerm,hU.mem_nhds h0U] with t ht htU
  have hh := congrArg e.symm ht
  change e.symm (e (γ t)) = e.symm (e (η t)) at hh
  rwa [e.left_inv htU.2.1,e.left_inv htU.2.2] at hh
end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
