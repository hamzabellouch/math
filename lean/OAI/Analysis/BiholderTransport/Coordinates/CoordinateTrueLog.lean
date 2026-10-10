import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ChartGradientMap

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section CoordinateTrueLog
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_chart_covector_for_log {a : M} {p : TangentSpace 𝓘(ℝ,Model n) a}
    (hp : p∈injectivityDomain a) :
    let z := extChartAt 𝓘(ℝ,Model n) a a
    ∃ L : Model n →L[ℝ] ℝ,
      chartGradientVector a z L∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
      coordinateBackward a (-1,z,L)=riemannianExp a p ∧
      HasFDerivAt (chartCost a (riemannianExp a p)) (-L) z := by
  let : Nonempty M := ⟨a⟩
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let A : TangentBundle 𝓘(ℝ,Model n) M := ⟨a,0⟩
  let P : TangentBundle 𝓘(ℝ,Model n) M := ⟨a,p⟩
  let c := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) A
  let L := riemannianCoordinateMetric a z (c P).2
  have hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hPs : P∈c.source := (tangent_chart_source_iff A P).mpr (mem_extChartAt_source a)
  have he : (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z L⟩ :
      TangentBundle 𝓘(ℝ,Model n) M)=P := by
    rw [chartGradientVector_total_eq (q := (z,L)) hz]
    have hinv : (riemannianCoordinateMetric a z).inverse L=(c P).2 :=
      (riemannianCoordinateMetric_isInvertible hz).inverse_apply_self _
    rw [hinv]
    exact c.left_inv hPs
  have hreg : chartGradientVector a z L∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z) := by
    have H : P∈{Q : TangentBundle 𝓘(ℝ,Model n) M | Q.2∈injectivityDomain Q.1} := hp
    rwa [←he] at H
  have hex : coordinateBackward a (-1,z,L)=riemannianExp a p := by
    rw [coordinateBackward_eq_exp_chartGradient hz]
    exact congrArg (fun Q : TangentBundle 𝓘(ℝ,Model n) M => riemannianExp Q.1 Q.2) he
  refine ⟨L,hreg,hex,?_⟩
  rw [←hex]
  exact chartCost_gradient_at_contact hz hreg

end CoordinateTrueLog
end WeakMTWTransport

end

end

end

end OAI
