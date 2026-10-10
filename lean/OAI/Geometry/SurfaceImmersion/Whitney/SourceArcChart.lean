import OAI.Geometry.SurfaceImmersion.Geometry.CompactAxisRectangle
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapConnectingArc

namespace OAI

/-! Actual rectangular source coordinates along the whole embedded crosscap arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem source_arc_chart (P : SmoothCompactArc planeModel M) :
    ∃ (c : OpenPartialHomeomorph M Base) (δ : ℝ), 0 < δ ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ c.source ∧ c (P.curve t) = ![0,t]) ∧
      (∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (P.start-δ) (P.finish+δ), (![x,t] : Base) ∈ c.target) := by
  let : Nonempty M := ⟨P.curve P.start⟩
  obtain ⟨F,hF,hFP⟩ := smooth_arc_parameter_extension P
  obtain ⟨c,hc⟩ := compact_arc_time_chart P hF hFP
  have haxis : ∀ t ∈ Icc P.start P.finish,
      P.curve t ∈ c.coord.source ∧ c.coord (P.curve t) = ![0,t] := by
    intro t ht
    change t ∈ {s : ℝ | P.curve s ∈ c.coord.source ∧ c.coord (P.curve s) = ![0,s]}
    exact mem_of_mem_nhdsWithin ht (hc t ht)
  obtain ⟨δ,hδ,hrect⟩ := compact_axis_rectangle P.start_lt_finish.le c.coord.open_target (by
    intro t ht
    rw [← (haxis t ht).2]
    exact c.coord.map_source (haxis t ht).1)
  exact ⟨c.coord,δ,hδ,c.smooth,c.inverse_smooth,haxis,hrect⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
