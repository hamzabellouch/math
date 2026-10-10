import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.MaximumPolePositive
import OAI.Analysis.BiholderTransport.Regularity.ModifiedOuterNeighborhood

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section MaximumOuterBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma MaximumJensenFamily.outer_bound
    {hmtw:WeakMTW (n := n) (M := M)}
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {x0:M}
    {uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv:uv∈densityDualClass (metricVolume n) lam cap x0)
    {α D bminus bplus:ℝ} {Bc Bo:ℝ → ℝ} (ho:ContDiff ℝ ∞ Bo)
    {F:MaximumFamily (n := n) uv.2 α D bminus bplus Bc Bo}
    {a c:M} {N:Set (Model n)}
    (J:MaximumJensenFamily hmtw uv.2.continuous ho.continuous F a c N)
    {β:ℝ} (hb:Tendsto F.b atTop (𝓝 β))
    (hbcoord:Tendsto (fun k=>graphBaseCoordinate a (F.row k).q.1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (i:ℕ → Fin (Module.finrank ℝ (Model n)+1)) {r:Model n}
    (hr:Tendsto (fun k=>(J.first k).pj₀ (i k)) atTop (𝓝 r))
    {mstar:ℝ} (hmstar:0 < mstar) (hm:∀ᶠ k in atTop,mstar ≤ (J.first k).w₀ (i k))
    (hmono:∀k,StrictMono (fun s=>modifiedScalar α D Bo (F.b k,s)))
    (hmono0:StrictMono (fun s=>modifiedScalar α D Bo (β,s)))
    (hslope:1 < deriv (fun s=>modifiedScalar α D Bo (β,s)) (uv.2 (riemannianExp a r)))
    (hcurve:iteratedDeriv 2 (fun s=>modifiedScalar α D Bo (β,s))
      (uv.2 (riemannianExp a r)) < 0) :
    ∃C≥0,∀ᶠ k in atTop,∀d:Model n,(J.first k).L d d ≤ C*‖d‖^2 := by
  have hactive:(show TangentSpace 𝓘(ℝ,Model n) a from r)∈
      activeLogs (modifiedDatum uv.2 α D β Bo) a :=
    modified_active_coordinates_limit uv.2.continuous ho.continuous hb hbcoord hr
      (Eventually.of_forall (fun k=>(extChartAt 𝓘(ℝ,Model n) a).map_source (J.poleSource k)))
      (Eventually.of_forall (fun k=>(J.first k).activeLimit (i k)))
  obtain ⟨U,hU,C,hC,HC⟩:=hmtw.modified_outer_neighborhood hlam hcap huv
    (modifiedScalar_contDiff ho α D) hmono0 hactive hslope hcurve
  have hlim:Tendsto (fun k=>((graphBaseCoordinate a (F.row k).q.1,(J.first k).pj₀ (i k)),F.b k))
      atTop (𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,r),β)) :=
    (hbcoord.prodMk_nhds hr).prodMk_nhds hb
  have hnear:∀ᶠ k in atTop,U∈𝓝 ((graphBaseCoordinate a (F.row k).q.1,(J.first k).pj₀ (i k)),F.b k) :=
    hlim.eventually (eventually_eventually_nhds.mpr hU)
  refine ⟨C/mstar,div_nonneg hC hmstar.le,?_⟩
  filter_upwards [hnear,hm] with k hUk hmk
  have hσ:=(J.first k).strictMono.tendsto_atTop
  obtain ⟨hq,hb',hp'⟩:=(F.row k).jensen_graph_limit hmtw uv.2.continuous ho.continuous
    (F.prefixTime k).1 (F.prefixTime k).2 (J.sample k) (J.endpointSource k) (J.poleSource k)
  have hlj:Tendsto (fun j=>((graphBaseCoordinate a (J.samplePoint k j).1,
      (J.first k).pj j (i k)),F.b k)) atTop
      (𝓝 ((graphBaseCoordinate a (F.row k).q.1,(J.first k).pj₀ (i k)),F.b k)) :=
    ((hb'.comp hσ).prodMk_nhds (tendsto_pi_nhds.mp (J.first k).pjLimit (i k))).prodMk_nhds tendsto_const_nhds
  have hw:Tendsto (fun j=>(J.first k).w j (i k)) atTop (𝓝 ((J.first k).w₀ (i k))) :=
    tendsto_pi_nhds.mp (J.first k).wLimit (i k)
  have hwpos:∀ᶠ j in atTop,0 < (J.first k).w j (i k) :=
    hw.eventually (lt_mem_nhds (hmstar.trans_le hmk))
  have H:∀ᶠ j in atTop,∀d:Model n,(J.first k).w j (i k)*J.sampleL k j d d ≤ C*‖d‖^2 := by
    filter_upwards [hlj.eventually hUk,hwpos,J.sample_pole_positive k,(J.first k).samples]
      with j hj hwj hpos hjets
    intro d
    exact HC _ hj (hmono k) ((J.first k).w j (i k) • J.sampleL k j)
      (fun e=>by exact mul_nonneg hwj.le (hpos e)) (hjets.2.2.2.2 (i k) hwj) d
  intro d
  have hld:Tendsto (fun j=>J.sampleL k j d d) atTop (𝓝 ((J.first k).L d d)) :=
    ((show Continuous (fun B:Model n →L[ℝ] Model n →L[ℝ] ℝ=>B d d) from
      (continuous_id.clm_apply continuous_const).clm_apply continuous_const).tendsto _).comp
        (J.first k).LLimit
  have HQ:(J.first k).w₀ (i k)*(J.first k).L d d ≤ C*‖d‖^2 :=
    le_of_tendsto (hw.mul hld) (H.mono (fun j hj=>hj d))
  have Hstar:mstar*(J.first k).L d d ≤ C*‖d‖^2 :=
    (mul_le_mul_of_nonneg_right hmk ((J.first k).positive d)).trans HQ
  calc
    (J.first k).L d d ≤ (C*‖d‖^2)/mstar := (le_div_iff₀ hmstar).mpr (by nlinarith only [Hstar])
    _ = C/mstar*‖d‖^2 := by ring

end MaximumOuterBound
end WeakMTWTransport

end
end

end OAI
