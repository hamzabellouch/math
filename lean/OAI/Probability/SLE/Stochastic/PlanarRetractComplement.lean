import OAI.Probability.SLE.Geometry.LocalLogObstruction

namespace OAI

/-! A closed planar retract has no bounded complementary component, since
the identity on a circle has no continuous logarithm. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma no_point_avoiding_identity_outside_ball (z : ℂ) {R : ℝ} (hR : 0 < R)
    (f : ℂ → ℂ) (hf : Continuous f) (hne : ∀ w, f w ≠ z)
    (hout : ∀ w, R ≤ dist w z → f w=w) : False := by
  let S := sphere (0 : ℂ) R
  let H : C(unitInterval × S,ℂ) :=
    ⟨fun p => f (z+(p.1 : ℂ)*(p.2 : ℂ))-z,by fun_prop⟩
  let L : C(S,ℂ) := ContinuousMap.const _ (Complex.log (f z-z))
  have hn : f z-z ≠ 0 := sub_ne_zero.mpr (hne z)
  obtain ⟨M,hM⟩ := continuous_log_at_end_of_homotopy H
    (fun p => sub_ne_zero.mpr (hne _)) L (fun a => by
      simpa [H,L] using Complex.exp_log hn)
  apply univalent_boundary_no_continuous_log id R hR continuous_id.continuousOn
    injective_id.injOn M
  intro a
  have ha : R ≤ dist (z+(a : ℂ)) z := by
    simpa only [dist_eq_norm,add_sub_cancel_left,sub_zero] using a.property.ge
  simpa [H,hout _ ha] using hM a

theorem bounded_open_frontier_not_retract
    {D K : Set ℂ} (hDb : Bornology.IsBounded D)
    {z : ℂ} (hz : z ∈ D) (hdisj : Disjoint D K)
    (hfrontier : frontier D ⊆ K)
    (r : ℂ → ℂ) (hr : Continuous r) (hrK : ∀ w, r w ∈ K)
    (hrfix : ∀ w ∈ K, r w=w) : False := by
  classical
  let f : ℂ → ℂ := D.piecewise r id
  have hf : Continuous f := hr.piecewise
    (fun w hw => hrfix w (hfrontier hw)) continuous_id
  have hne (w : ℂ) : f w ≠ z := by
    change (D.piecewise r id) w ≠ z
    by_cases hw : w ∈ D
    · rw [piecewise_eq_of_mem D r id hw]
      intro he
      exact Set.disjoint_left.mp hdisj hz (he ▸ hrK w)
    · rw [piecewise_eq_of_notMem D r id hw]
      intro he
      have he' : w=z := he
      exact hw (he'.symm ▸ hz)
  obtain ⟨R,hR,hball⟩ := hDb.subset_ball_lt 0 z
  apply no_point_avoiding_identity_outside_ball z hR f hf hne
  intro w hw
  have hn : w ∉ D := fun hd => (hball hd).not_ge hw
  exact piecewise_eq_of_notMem D r id hn

lemma frontier_connectedComponentIn_subset_compl {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} : frontier (connectedComponentIn U z) ⊆ Uᶜ := by
  intro w hw hwin
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU w hwin
  obtain ⟨v,hvball,hvC⟩ := mem_closure_iff_nhds.mp hw.1 _ (ball_mem_nhds w hε)
  have hsub : ball w ε ⊆ connectedComponentIn U v :=
    isPreconnected_ball.subset_connectedComponentIn hvball hball
  have hwC : w ∈ connectedComponentIn U z := by
    rw [connectedComponentIn_eq hvC]
    exact hsub (mem_ball_self hε)
  exact hw.2 (by simpa only [(hU.connectedComponentIn).interior_eq] using hwC)

theorem retract_complement_component_unbounded
    {K : Set ℂ} (hK : IsClosed K)
    (r : ℂ → ℂ) (hr : Continuous r) (hrK : ∀ w, r w ∈ K)
    (hrfix : ∀ w ∈ K, r w=w) {z : ℂ} (hz : z ∉ K) :
    ¬ Bornology.IsBounded (connectedComponentIn Kᶜ z) := by
  intro hb
  have hfront : frontier (connectedComponentIn Kᶜ z) ⊆ K := by
    simpa only [compl_compl] using
      (frontier_connectedComponentIn_subset_compl hK.isOpen_compl (z := z))
  apply bounded_open_frontier_not_retract hb
    (mem_connectedComponentIn hz) (disjoint_left.mpr (fun w hw hwin =>
      connectedComponentIn_subset (Kᶜ) z hw hwin))
    hfront r hr hrK hrfix

end SLEExactGauge

end

end OAI
