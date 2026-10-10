import OAI.Analysis.CoulombTransport.CoulombSupportExistence

namespace OAI

noncomputable section

open Set Metric

namespace Problem356.CoulombSupportExistence

open LocalGeometry StationaryMap CoulombCalculus

private theorem outside_central_ball {a y : E3} (ha : ‖a‖ = 1)
    (hy : y ∈ ball a (1 / 4 : ℝ)) : y ∉ ball (0 : E3) (1 / 4 : ℝ) := by
  intro hx
  have htri := dist_triangle a y (0 : E3)
  rw [dist_zero_right, ha, dist_comm a y] at htri
  have hy' := mem_ball.mp hy
  have hx' := mem_ball.mp hx
  linarith

/-- Shrink both local domains before forming the global contact predicate.
Every parameter of the entire retained graph, not just parameters in a later
component ball, has both outer coordinates outside the fixed central ball. -/
theorem exists_separated_shrink {a : E3} (ha : ‖a‖ = 1)
    (C : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a)) :
    ∃ D : LocalSupportingCharts (jointPotential a) (stationary a) a (0, -a),
      ∀ y ∈ D.charts.central.source,
        y ∉ ball (0 : E3) (1 / 4 : ℝ) ∧
          D.charts.opposite y ∉ ball (0 : E3) (1 / 4 : ℝ) := by
  obtain ⟨D, hsource, hstate, _, _, _⟩ :=
    C.exists_shrink (1 / 4) (1 / 4) (by norm_num) (by norm_num)
  refine ⟨D, ?_⟩
  intro y hy
  refine ⟨outside_central_ball ha (hsource hy).2, ?_⟩
  have hs := (hstate (D.charts.mapsTo_state hy)).2
  have hz : D.charts.opposite y ∈ ball (-a) (1 / 4 : ℝ) := by
    rw [← ball_prod_same] at hs
    exact hs.2
  exact outside_central_ball (by simpa only [norm_neg] using ha) hz

/-- Unconditional actual Coulomb supporting charts with graph-wide exclusion
of both outer coordinates from a common fixed central neighborhood. -/
theorem exists_coulombLocalSupportingCharts_separated (k : Fin 3) :
    ∃ C : LocalSupportingCharts (jointPotential (axisVector k))
      (stationary (axisVector k)) (axisVector k) (0, -axisVector k),
      ∀ y ∈ C.charts.central.source,
        y ∉ ball (0 : E3) (1 / 4 : ℝ) ∧
          C.charts.opposite y ∉ ball (0 : E3) (1 / 4 : ℝ) := by
  obtain ⟨C⟩ := nonempty_coulombLocalSupportingCharts_stationary k
  exact exists_separated_shrink (norm_axisVector k) C

end Problem356.CoulombSupportExistence

end

end OAI
