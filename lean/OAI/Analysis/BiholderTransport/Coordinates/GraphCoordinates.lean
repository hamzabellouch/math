import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.UniformEnvelope
import OAI.Analysis.BiholderTransport.Geodesics.MinimizingChartParameters
import OAI.Analysis.BiholderTransport.Regularity.MovingPrefix

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

def graphBaseCoordinate (a : M) (q : TangentBundle 𝓘(ℝ,Model n) M) : Model n :=
  extChartAt 𝓘(ℝ,Model n) a q.1

def graphVelocityCoordinate (a : M) (q : TangentBundle 𝓘(ℝ,Model n) M) : Model n :=
  (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) q).2

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] in
lemma graph_coordinate_reconstruction {a : M} {q : TangentBundle 𝓘(ℝ,Model n) M}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm (graphBaseCoordinate a q),
      chartFiberInverse a (graphBaseCoordinate a q) (graphVelocityCoordinate a q)⟩ :
        TangentBundle 𝓘(ℝ,Model n) M)=q := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  have hs : q∈χ.source := (tangent_chart_source_iff _ _).mpr hq
  have hb : (χ q).1∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (tangent_chart_target_iff _ _).mp (χ.map_source hs)
  have H := χ.left_inv hs
  rw [tangent_chart_symm_trivialization hb] at H
  exact H

lemma movingPrefix_graph_coordinates {a : M} {q : TangentBundle 𝓘(ℝ,Model n) M}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).source) (t : ℝ) :
    movingPrefix a t (graphBaseCoordinate a q) (graphVelocityCoordinate a q)=
      riemannianExp q.1 (t • q.2) := by
  simp only [graphBaseCoordinate]
  rw [movingPrefix_eq ((extChartAt 𝓘(ℝ,Model n) a).map_source hq)]
  exact congrArg (fun z:TangentBundle 𝓘(ℝ,Model n) M=>riemannianExp z.1 (t • z.2))
    (graph_coordinate_reconstruction hq)

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] in
lemma graph_coordinates_at_center (q : TangentBundle 𝓘(ℝ,Model n) M) :
    graphVelocityCoordinate q.1 q=q.2 := by
  unfold graphVelocityCoordinate
  rw [tangent_chart_apply]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source q.1)
end WeakMTWTransport

end

end OAI
