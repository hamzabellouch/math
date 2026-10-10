import OAI.MeasureTheory.Falconer.Graphs.GraphRetainedEdges

namespace OAI

namespace PlanarFalconer
open Set

theorem planeDot_eq_inner (u v : Plane) : planeDot u v = inner ℝ u v := by
  simp [planeDot,EuclideanSpace.inner_eq_star_dotProduct,Fin.sum_univ_two,dotProduct]
  ring

theorem graphDirection_chart_endpoint (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : u+v ≠ 0) : graphDirection (graphChartZ u v) (graphChartAxis u v) = u := by
  have he := (graph_chart_endpoints u v hu hv hw).1
  have hr := graph_chart_radius_identity u v hu hv hw
  have hp : (u+v)+graphChartZ u v • quarterTurn (u+v) = (2:ℝ) • u := by
    calc
      _ = (2:ℝ) • graphB (graphChartZ u v) (u+v) := by dsimp only [graphB]; module
      _ = _ := congrArg (fun x : Plane => (2:ℝ) • x) he.symm
  calc
    _ = ((Real.sqrt (1+(graphChartZ u v)^2))⁻¹ * ‖u+v‖⁻¹) •
        ((u+v)+graphChartZ u v • quarterTurn (u+v)) := by
      simp only [graphDirection,graphChartAxis,quarterTurn_smul]
      module
    _ = _ := by
      rw [hp,smul_smul,← mul_inv, mul_comm (Real.sqrt _) ‖u+v‖,hr]
      norm_num

theorem graphChartAxis_norm {u v : Plane} (h : u+v ≠ 0) : ‖graphChartAxis u v‖ = 1 := by
  rw [graphChartAxis,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

theorem GraphSourceRepresentative.product_strip
    {plus : Bool} {axis θ : ℝ} {j k : ℕ} {q : UnitCircle × UnitCircle}
    (hq : GraphSourceRepresentative false plus axis θ j k q)
    (N : ℕ) (sig p : ℝ) (P : Fin 4 → DyadicSquare)
    (he : GraphRetainedEdge N sig p false plus P q) :
    |inner ℝ (quarterTurn (q.1:Plane)) ((P 0).center-(P 1).center)| ≤
      5*graphNonedgeThreshold N sig p := by
  have hn := graphSourceWeight_support_nondegenerate false plus axis (angularBinCount θ) j k hq.1
  change 1/2 ≤ ‖(q.1:Plane)+graphSourceSign false plus • (q.2:Plane)‖ at hn
  have hv := circle_sign_norm _ (graphSourceSign_cases false plus) q.2
  have hz := (graph_chart_nondegenerate_bound (q.1:Plane) _ q.1.property hv hn).1
  have hne : (q.1:Plane)+graphSourceSign false plus • (q.2:Plane) ≠ 0 :=
    norm_pos_iff.mp (by linarith)
  have hh := graph_product_strip (graphRepresentativeZ false plus q) (graphSourceSign false plus)
    (graphNonedgeThreshold N sig p) (graphRepresentativeAxis false plus q)
    ((P 0).center-(P 1).center) ((P 2).center-(P 3).center)
    (graphChartAxis_norm hne) (by unfold graphNonedgeThreshold; positivity) hz he.1
    (by rw [planeDot_eq_inner]; exact he.2 rfl)
  rw [graphRepresentativeZ,graphRepresentativeAxis,
    graphDirection_chart_endpoint _ _ q.1.property hv hne,planeDot_eq_inner] at hh
  exact hh

theorem graphRetainedProduct_reversal (N : ℕ) (sig p : ℝ) (plus : Bool)
    (P : Fin 4 → DyadicSquare) (q : UnitCircle × UnitCircle) :
    GraphRetainedEdge N sig p false plus ![P 1,P 0,P 3,P 2] q ↔
      GraphRetainedEdge N sig p false plus P q := by
  have hn (z s : ℝ) (u v : Plane) : graphA z (-u)+s • graphB z (-v) = -(graphA z u+s • graphB z v) := by
    ext l
    fin_cases l <;> simp [graphA,graphB,quarterTurn] <;> ring
  have hd (s : ℝ) (u v : Plane) : graphDerivative s (-u) (-v) = -graphDerivative s u v := by
    ext l
    fin_cases l <;> simp [graphDerivative,quarterTurn] <;> ring
  simp only [GraphRetainedEdge,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  rw [show (P 1).center-(P 0).center = -((P 0).center-(P 1).center) by abel,
    show (P 3).center-(P 2).center = -((P 2).center-(P 3).center) by abel]
  simp only [hn,hd,norm_neg,inner_neg_right,abs_neg]

end PlanarFalconer

end OAI
