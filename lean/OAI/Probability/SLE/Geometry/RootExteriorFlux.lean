import OAI.Probability.SLE.Geometry.RootExteriorRadius
import OAI.Probability.SLE.Geometry.ConformalLaplacianIntegral
import OAI.Probability.SLE.Geometry.ExteriorCompactFlux

namespace OAI

/-! Positivity of the signed boundary area for the actual exterior root
map. Compact omitted sets and the ordinary area change of variables
supply the sign, without a boundary regularity assumption at radius one. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SLEExactGauge

lemma root_exterior_flux_nonneg {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1))
    (hne : ∀ z∈ball (0:ℂ) 1, q z≠0)
    (hi : InjOn (fun z : ℂ => z*q (z^2)) (ball 0 1))
    {r : ℝ} (hr : 1<r) :
    0≤∫ θ in -Real.pi..Real.pi,
      radialLaplacianFlux (fun z => ‖rootExteriorChart q z‖^2) (r,θ) := by
  let F := rootExteriorChart q
  let D := {z : ℂ | r<‖z‖}
  have hD : IsOpen D := isOpen_lt continuous_const continuous_norm
  have hDsub : D⊆{z : ℂ | 1<‖z‖} := fun z hz => hr.trans hz
  obtain ⟨hF,hFi⟩ := root_exterior_univalent hq hne hi
  have hK : IsCompact (F '' D)ᶜ := root_exterior_omitted_radius_isCompact hq hne hi hr
  obtain ⟨u,hu,hs,he,_,hint⟩ := exterior_compact_test_laplacian_nonpos hD
    (hF.mono hDsub) (hFi.mono hDsub) hK
  have hFc (z : ℂ) (hz : r≤‖z‖) : AnalyticAt ℂ F z :=
    hF.analyticAt ((isOpen_lt continuous_const continuous_norm).mem_nhds (hr.trans_le hz))
  have hv (z : ℂ) (hz : r≤‖z‖) : ContDiffAt ℝ 2 (u ∘ F) z :=
    hu.contDiffAt.comp z ((hFc z hz).contDiffAt.restrict_scalars ℝ)
  have hvs : HasCompactSupport (u ∘ F) := by
    rw [hasCompactSupport_iff_eventuallyEq,Filter.coclosedCompact_eq_cocompact] at hs ⊢
    exact (root_exterior_tendsto_cocompact hq hne).eventually hs
  have hpos := exterior_compact_flux_nonneg (zero_lt_one.trans hr) hv hvs hint
  convert! hpos using 1
  apply intervalIntegral.integral_congr
  intro θ _
  have hn : ‖polarPoint r θ‖=r := by
    rw [polarPoint_norm,abs_of_pos (zero_lt_one.trans hr)]
  have hz : F (polarPoint r θ)∈(F '' D)ᶜ :=
    root_exterior_circle_omitted hq hne hi hr hn
  have hlocal : (u ∘ F) =ᶠ[𝓝 (polarPoint r θ)] (fun z => ‖F z‖^2) :=
    (he _ hz).comp_tendsto (hFc _ hn.ge).continuousAt
  simp only [radialLaplacianFlux,hlocal.fderiv_eq]
  rfl

end SLEExactGauge

end

end OAI
