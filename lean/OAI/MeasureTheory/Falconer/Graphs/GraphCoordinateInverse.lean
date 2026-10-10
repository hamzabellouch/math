import OAI.MeasureTheory.Falconer.Graphs.GraphGeometry

namespace OAI

namespace PlanarFalconer

theorem quarterTurn_smul (r : ℝ) (v : Plane) : quarterTurn (r • v) = r • quarterTurn v := by
  ext i
  fin_cases i <;> simp [quarterTurn]

theorem graph_quarterTurn_norm (v : Plane) : ‖quarterTurn v‖ = ‖v‖ := by
  simpa using norm_quarterTurn_add 0 v

theorem orthogonal_vector_quarterTurn (d w : Plane) (hw : w ≠ 0)
    (hd : planeDot d w = 0) :
    d = (planeDot d (quarterTurn w)/‖w‖^2) • quarterTurn w := by
  have hn : ‖w‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hs := EuclideanSpace.real_norm_sq_eq w
  simp only [Fin.sum_univ_two] at hs
  have hm0 : (d 0*w 0+d 1*w 1)*w 0 = 0 := by rw [← planeDot,hd,zero_mul]
  have hm1 : (d 0*w 0+d 1*w 1)*w 1 = 0 := by rw [← planeDot,hd,zero_mul]
  ext i
  fin_cases i <;> simp [quarterTurn, planeDot] <;> field_simp <;> rw [hs] <;> nlinarith

noncomputable def graphChartZ (u v : Plane) : ℝ :=
  planeDot (u-v) (quarterTurn (u+v))/‖u+v‖^2

theorem graph_chart_difference (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : u+v ≠ 0) : u-v = graphChartZ u v • quarterTurn (u+v) := by
  apply orthogonal_vector_quarterTurn _ _ hw
  have hs₁ := EuclideanSpace.real_norm_sq_eq u
  have hs₂ := EuclideanSpace.real_norm_sq_eq v
  rw [hu] at hs₁
  rw [hv] at hs₂
  simp only [Fin.sum_univ_two] at hs₁ hs₂
  simp [planeDot]
  nlinarith

theorem graph_chart_endpoints (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : u+v ≠ 0) : u = graphB (graphChartZ u v) (u+v) ∧
      v = graphA (graphChartZ u v) (u+v) := by
  have hd := graph_chart_difference u v hu hv hw
  constructor
  · rw [graphB, ← hd, smul_add, smul_sub]
    module
  · rw [graphA, ← hd, smul_sub, smul_add, smul_sub]
    module

theorem graph_chart_radius_identity (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : u+v ≠ 0) : ‖u+v‖*Real.sqrt (1+(graphChartZ u v)^2) = 2 := by
  have hpar : ‖u+v‖^2+‖u-v‖^2 = 4 := by
    rw [norm_add_sq_real, norm_sub_sq_real, hu, hv]
    ring
  have hd := congrArg (fun w : Plane => ‖w‖^2) (graph_chart_difference u v hu hv hw)
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, graph_quarterTurn_norm] at hd
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1+(graphChartZ u v)^2)
  have he : (‖u+v‖*Real.sqrt (1+(graphChartZ u v)^2))^2 = (2:ℝ)^2 := by
    rw [mul_pow,hs]
    nlinarith
  exact (sq_eq_sq₀ (by positivity) (by norm_num)).mp he

theorem graph_chart_nondegenerate_bound (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hchart : 1/2 ≤ ‖u+v‖) :
    Real.sqrt (1+(graphChartZ u v)^2) ≤ 4 ∧ |graphChartZ u v| ≤ 4 := by
  have hw : u+v ≠ 0 := norm_pos_iff.mp (by linarith)
  have he := graph_chart_radius_identity u v hu hv hw
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1+(graphChartZ u v)^2)
  have hspos := Real.sqrt_nonneg (1+(graphChartZ u v)^2)
  have hb : Real.sqrt (1+(graphChartZ u v)^2) ≤ 4 := by nlinarith
  exact ⟨hb, by nlinarith [sq_abs (graphChartZ u v),abs_nonneg (graphChartZ u v)]⟩

theorem graph_chart_inverse (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hchart : 1/2 ≤ ‖u+v‖) {r : ℝ} (hr : 0 < r) :
    let ξ := r • (u+v)
    let z := graphChartZ u v
    r • u = graphB z ξ ∧ r • v = graphA z ξ ∧
      r = ‖ξ‖*Real.sqrt (1+z^2)/2 ∧ Real.sqrt (1+z^2) ≤ 4 := by
  dsimp only
  have hw : u+v ≠ 0 := norm_pos_iff.mp (by linarith)
  have hend := graph_chart_endpoints u v hu hv hw
  have he := graph_chart_radius_identity u v hu hv hw
  refine ⟨?_,?_,?_,(graph_chart_nondegenerate_bound u v hu hv hchart).1⟩
  · calc
      r • u = r • graphB (graphChartZ u v) (u+v) := congrArg (fun w : Plane => r • w) hend.1
      _ = _ := by
        ext i
        fin_cases i <;> simp [graphB,quarterTurn] <;> ring
  · calc
      r • v = r • graphA (graphChartZ u v) (u+v) := congrArg (fun w : Plane => r • w) hend.2
      _ = _ := by
        ext i
        fin_cases i <;> simp [graphA,quarterTurn] <;> ring
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith

end PlanarFalconer

end OAI
