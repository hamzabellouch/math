import OAI.Probability.SLE.Loewner.SlitChartProper
import OAI.Probability.SLE.Geometry.ComplexEndpointCluster

namespace OAI

/-! A physical sequence approaching the slit boundary has forward-chart
height tending to zero. -/
noncomputable section
open Set Filter Function Metric Complex
open scoped Topology

namespace SLEExactGauge

theorem SimpleSlitChart.forward_height_tendsto_zero {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) {z : ℕ → ℂ} {b : ℂ}
    (hz : Tendsto z atTop (𝓝 b))
    (hzD : ∀ n, z n∈upperHalfPlane \ range p) (hb : b∉upperHalfPlane \ range p) :
    Tendsto (fun n => (P.forward (z n)).im) atTop (𝓝 0) := by
  obtain ⟨R,hR⟩ := (Metric.isBounded_range_of_tendsto z hz).exists_norm_le
  obtain ⟨M,hM⟩ := P.forward_bounded_over_ball R
  apply tendsto_of_subseq_tendsto
  intro φ hφ
  obtain ⟨w,_,ψ,hψ,hw⟩ := (isCompact_closedBall (0:ℂ) M).tendsto_subseq (fun n => by
    rw [mem_closedBall,dist_zero_right]
    exact hM (z (φ n)) (hzD _) (hR _ (mem_range_self _)))
  have hwim : 0≤w.im := ge_of_tendsto (continuous_im.continuousAt.tendsto.comp hw)
    (Eventually.of_forall fun n => (show 0<(P.forward (z (φ (ψ n)))).im from
      P.bijOn.mapsTo (hzD _)).le)
  have hezero : w.im=0 := by
    by_contra hne
    have hwH : w∈upperHalfPlane := lt_of_le_of_ne hwim (Ne.symm hne)
    have hback := ((P.inverse_differentiable.continuousOn w hwH).continuousAt
      (isOpen_upperHalfPlane.mem_nhds hwH)).tendsto.comp hw
    have he : P.inverse w=b := by
      apply tendsto_nhds_unique hback
      have hzb := (hz.comp hφ).comp hψ.tendsto_atTop
      apply hzb.congr
      intro n
      exact (P.left_inverse _ (hzD _)).symm
    exact hb (he ▸ P.inverse_mapsTo hwH)
  refine ⟨ψ,?_⟩
  have hh := continuous_im.continuousAt.tendsto.comp hw
  change Tendsto (fun n => (P.forward (z (φ (ψ n)))).im) atTop (𝓝 w.im) at hh
  rwa [hezero] at hh

theorem SimpleSlitChart.forward_height_tendsto_zero_filter {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {z : α → ℂ} {b : ℂ} (hz : Tendsto z l (𝓝 b))
    (hzD : ∀ᶠ x in l, z x∈upperHalfPlane \ range p)
    (hb : b∉upperHalfPlane \ range p) :
    Tendsto (fun x => (P.forward (z x)).im) l (𝓝 0) := by
  classical
  apply tendsto_iff_seq_tendsto.mpr
  intro u hu
  let w : ℕ → ℂ := fun n =>
    if z (u n)∈upperHalfPlane \ range p then z (u n) else P.inverse I
  have he : w =ᶠ[atTop] fun n => z (u n) := by
    filter_upwards [hu.eventually hzD] with n hn
    exact ite_eq_left hn
  have hw : Tendsto w atTop (𝓝 b) := (hz.comp hu).congr' he.symm
  have hwD : ∀ n, w n∈upperHalfPlane \ range p := by
    intro n
    dsimp only [w]
    split_ifs with hn
    · exact hn
    · exact P.inverse_mapsTo (by change 0<(I:ℂ).im; norm_num)
  exact (P.forward_height_tendsto_zero hw hwD hb).congr'
    (he.mono fun n hn => congrArg (fun v => (P.forward v).im) hn)

end SLEExactGauge

end

end OAI
