import OAI.Probability.SLE.Loewner.SlitChartBoundaryBasics

namespace OAI

/-! Normalization at infinity prevents bounded physical points from having
unbounded chart coordinates, including when they approach the slit. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.forward_bounded_over_ball {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) (R : ℝ) :
    ∃ M : ℝ, ∀ z∈upperHalfPlane \ range p, ‖z‖≤R → ‖P.forward z‖≤M := by
  have he := Metric.tendsto_nhds.mp P.inverse_normalized (1/2) (by norm_num)
  rw [eventually_inf_principal,← Metric.cobounded_eq_cocompact] at he
  obtain ⟨N,_,hN⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  refine ⟨max (max N 1) (2*R),fun z hz hzR => ?_⟩
  by_cases hb : ‖P.forward z‖ ≤ max N 1
  · exact hb.trans (le_max_left _ _)
  have hb' := lt_of_not_ge hb
  have hnorm : 0<‖P.forward z‖ := by linarith [le_max_right N (1:ℝ)]
  have hsmall := hN ((le_max_left N (1:ℝ)).trans hb'.le) (P.bijOn.mapsTo hz)
  rw [dist_eq_norm,P.left_inverse z hz] at hsmall
  have htri := norm_le_norm_sub_add (1:ℂ) (z/P.forward z)
  rw [norm_one,norm_sub_rev,norm_div] at htri
  have hprod : (1/2:ℝ)*‖P.forward z‖<‖z‖ := by
    apply (lt_div_iff₀ hnorm).mp
    linarith
  exact (show ‖P.forward z‖≤2*R by linarith).trans (le_max_right _ _)

end SLEExactGauge

end

end OAI
