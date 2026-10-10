import OAI.MeasureTheory.Falconer.Graphs.GraphSignChart
import OAI.MeasureTheory.Falconer.Graphs.GraphDirectionStability

namespace OAI

namespace PlanarFalconer
open Set

private theorem quarterTurn_sub (u v : Plane) : quarterTurn (u-v) = quarterTurn u-quarterTurn v := by
  ext i
  fin_cases i <;> simp [quarterTurn]
  ring

theorem graphChartZ_dist_le (u v u' v' : Plane)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1)
    (hw : 1/2 ≤ ‖u+v‖) (hw' : 1/2 ≤ ‖u'+v'‖) :
    |graphChartZ u v-graphChartZ u' v'| ≤ 10*(dist u u'+dist v v') := by
  have hd := graph_chart_difference u v hu hv (norm_pos_iff.mp (by linarith))
  have hd' := graph_chart_difference u' v' hu' hv' (norm_pos_iff.mp (by linarith))
  have hz := (graph_chart_nondegenerate_bound u' v' hu' hv' hw').2
  have hsum : ‖(u+v)-(u'+v')‖ ≤ dist u u'+dist v v' := by
    simpa only [dist_eq_norm] using dist_add_add_le u v u' v'
  have hdiff : ‖(u-v)-(u'-v')‖ ≤ dist u u'+dist v v' := by
    simpa only [dist_eq_norm] using dist_sub_sub_le u v u' v'
  have he : (graphChartZ u v-graphChartZ u' v') • quarterTurn (u+v) =
      ((u-v)-(u'-v'))-graphChartZ u' v' • quarterTurn ((u+v)-(u'+v')) := by
    rw [quarterTurn_sub, smul_sub, hd, hd', sub_smul]
    abel
  have hn : |graphChartZ u v-graphChartZ u' v'| *‖u+v‖ ≤
      5*(dist u u'+dist v v') := by
    calc
      _ = ‖(graphChartZ u v-graphChartZ u' v') • quarterTurn (u+v)‖ := by
        rw [norm_smul, Real.norm_eq_abs, graph_quarterTurn_norm]
      _ ≤ ‖(u-v)-(u'-v')‖+‖graphChartZ u' v' • quarterTurn ((u+v)-(u'+v'))‖ :=
        he ▸ norm_sub_le _ _
      _ = ‖(u-v)-(u'-v')‖+|graphChartZ u' v'| *‖(u+v)-(u'+v')‖ := by
        rw [norm_smul, Real.norm_eq_abs, graph_quarterTurn_norm]
      _ ≤ (dist u u'+dist v v')+4*(dist u u'+dist v v') :=
        add_le_add hdiff (mul_le_mul hz hsum (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  nlinarith [abs_nonneg (graphChartZ u v-graphChartZ u' v')]

noncomputable def graphChartAxis (u v : Plane) : Plane := ‖u+v‖⁻¹ • (u+v)

theorem graphChartAxis_dist_le (u v u' v' : Plane)
    (hw : 1/2 ≤ ‖u+v‖) (hw' : 1/2 ≤ ‖u'+v'‖) :
    dist (graphChartAxis u v) (graphChartAxis u' v') ≤ 4*(dist u u'+dist v v') := by
  have hw0 : 0 < ‖u+v‖ := by linarith
  have hh := normalized_vector_dist_le (u+v) (u'+v') (norm_pos_iff.mp hw0)
    (norm_pos_iff.mp (by linarith))
  have hb : dist (u+v) (u'+v') ≤ dist u u'+dist v v' := dist_add_add_le _ _ _ _
  apply hh.trans
  apply (div_le_iff₀ hw0).mpr
  have ht : 0 ≤ dist u u'+dist v v' := by positivity
  nlinarith

theorem graph_sign_bin_pair_variation (s : ℝ) (hs : s = 1 ∨ s = -1)
    (p q : UnitCircle × UnitCircle)
    (hp : 1/2 ≤ ‖(p.1:Plane)+s • (p.2:Plane)‖)
    (hq : 1/2 ≤ ‖(q.1:Plane)+s • (q.2:Plane)‖) :
    |graphChartZ (p.1:Plane) (s • (p.2:Plane))-graphChartZ (q.1:Plane) (s • (q.2:Plane))|+
      dist (graphChartAxis (p.1:Plane) (s • (p.2:Plane)))
        (graphChartAxis (q.1:Plane) (s • (q.2:Plane))) ≤
      14*(dist p.1 q.1+dist p.2 q.2) := by
  have hz := graphChartZ_dist_le _ _ _ _ p.1.property (circle_sign_norm s hs p.2)
    q.1.property (circle_sign_norm s hs q.2) hp hq
  have ha := graphChartAxis_dist_le (p.1:Plane) (s • (p.2:Plane))
    (q.1:Plane) (s • (q.2:Plane)) hp hq
  have hd : dist (s • (p.2:Plane)) (s • (q.2:Plane)) = dist p.2 q.2 := by
    change dist (s • (p.2:Plane)) (s • (q.2:Plane)) = dist (p.2:Plane) (q.2:Plane)
    rcases hs with rfl | rfl <;> simp
  rw [hd] at hz ha
  change _ ≤ 10*(dist p.1 q.1+dist p.2 q.2) at hz
  change _ ≤ 4*(dist p.1 q.1+dist p.2 q.2) at ha
  linarith

theorem graph_complete_support_representative (s δ : ℝ) (hs : s = 1 ∨ s = -1)
    (S : Set (UnitCircle × UnitCircle)) (hS : S.Nonempty)
    (hchart : ∀ p ∈ S, 1/2 ≤ ‖(p.1:Plane)+s • (p.2:Plane)‖)
    (hbin : ∀ p ∈ S, ∀ q ∈ S, dist p.1 q.1 ≤ δ ∧ dist p.2 q.2 ≤ δ) :
    ∃ q ∈ S, ∀ p ∈ S,
      |graphChartZ (p.1:Plane) (s • (p.2:Plane))-graphChartZ (q.1:Plane) (s • (q.2:Plane))|+
      dist (graphChartAxis (p.1:Plane) (s • (p.2:Plane)))
        (graphChartAxis (q.1:Plane) (s • (q.2:Plane))) ≤ 28*δ := by
  obtain ⟨q,hq⟩ := hS
  refine ⟨q,hq,?_⟩
  intro p hp
  have hv := graph_sign_bin_pair_variation s hs p q (hchart p hp) (hchart q hq)
  have hb := hbin p hp q hq
  linarith

end PlanarFalconer

end OAI
