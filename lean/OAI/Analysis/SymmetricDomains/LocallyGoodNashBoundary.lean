import Mathlib
import OAI.Analysis.SymmetricDomains.GoodNashBoundary

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem nash_boundary_chart_of_projection {d m N : ℕ}
    (U V : Set (Affine N)) (hUV : U ⊆ V) (hV : IsClosed V) (hUs : IsSemialgebraic U)
    (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine N) (hqa : AnalyticOnNhd ℝ q B)
    (hqs : SemialgebraicOn B (fun x => complexRealEquiv N (q x)))
    (hqb : ∀ x ∈ B, q x ∈ closure U \ U)
    {a : Fin d → ℝ} (ha : a ∈ B)
    (hqi : Function.Injective (fderiv ℝ q a))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) a (Pi.single i 1)))
    (c : ProjectionNashChart V (q a) m) :
    ∃ b : NashBoundaryChart (m := m) U V B q, b.center = a := by
  let G := fun y => c.projection (y-q a)
  have hG : AnalyticAt ℂ G (q a) :=
    (c.projection.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hF : AnalyticAt ℂ c.inverse 0 := c.inverse_analytic 0 (by simpa only [mem_ofPred_eq,map_zero,norm_zero] using c.radius_pos)
  have hnear : ∀ᶠ z : Affine m in 𝓝 0, ‖complexRealEquiv m z‖ < c.radius :=
    (isOpen_lt ((complexRealEquiv m).continuous.norm) continuous_const).mem_nhds (by simpa only [mem_ofPred_eq,map_zero,norm_zero] using c.radius_pos)
  have hGF : (G ∘ c.inverse) =ᶠ[𝓝 (0 : Affine m)] id := by
    filter_upwards [hnear] with z hz
    exact c.left_inverse z hz
  have hqV : ∀ᶠ x in 𝓝 a, q x ∈ V := by
    filter_upwards [hB.mem_nhds ha] with x hx
    exact closure_minimal hUV hV (hqb x hx).1
  have ht : Tendsto q (𝓝 a) (𝓝[V] (q a)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(hqa a ha).continuousAt,hqV⟩
  have hFGq : (c.inverse ∘ G ∘ q) =ᶠ[𝓝 a] q := ht c.right_inverse
  obtain ⟨hMi,hMg⟩ := chart_parametric_generic c.inverse G q c.inverse_zero hF hG
    (hqa a ha).differentiableAt hqi hGF hFGq hr
  have hMa : AnalyticOnNhd ℝ (G ∘ q) B := by
    intro x hx
    exact ((c.projection.restrictScalars ℝ).analyticAt _).comp ((hqa x hx).sub analyticAt_const)
  let L := (complexRealEquiv m).toLinearMap.comp
    ((c.projection.restrictScalars ℝ).toLinearMap.comp (complexRealEquiv N).symm.toLinearMap)
  have hMs : SemialgebraicOn B (fun x => complexRealEquiv m ((G ∘ q) x)) := by
    have hs := (SemialgebraicOn.affine PolynomialSignSet.univ L (-L (complexRealEquiv N (q a)))).comp
      hqs (fun _ _ => mem_univ _)
    apply hs.congr
    intro x _
    simp [L,G,sub_eq_add_neg]
  obtain ⟨nc⟩ := generic_nash_normal_coordinates B hB (G ∘ q) hMa hMs ha hMi hMg
  obtain ⟨hDs,R,hR,hRle,hboundary⟩ := nash_normal_graph_boundary U V hUV hV hUs B q hqa hqb ha
    c.projection c.inverse c.right_inverse c.radius c.radius_pos c.inverse_semialgebraic nc
  exact ⟨⟨a,ha,c,nc,R,hR,hRle,hDs,hboundary⟩,rfl⟩

theorem locally_good_nash_boundary {d m N : ℕ}
    (U V : Set (Affine N)) (hUV : U ⊆ V) (hV : IsClosed V) (hUs : IsSemialgebraic U)
    (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine N) (hqa : AnalyticOnNhd ℝ q B)
    (hqs : SemialgebraicOn B (fun x => complexRealEquiv N (q x)))
    (hqb : ∀ x ∈ B, q x ∈ closure U \ U)
    {a : Fin d → ℝ} (ha : a ∈ B)
    (hqi : Function.Injective (fderiv ℝ q a))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) a (Pi.single i 1)))
    (c : ProjectionNashChart V (q a) m) :
    ∃ W : Set (Fin d → ℝ), IsOpen W ∧ a ∈ W ∧
      volume {x | x ∈ W ∧ ¬ GoodNashBoundary m U V B q x} = 0 := by
  obtain ⟨c,hca⟩ := nash_boundary_chart_of_projection U V hUV hV hUs B hB q hqa hqs hqb ha hqi hr c
  obtain ⟨W,hW,hcW,hnull⟩ := c.null_bad_parameters
  refine ⟨W,hW,hca ▸ hcW,measure_mono_null ?_ hnull⟩
  intro x hx
  exact ⟨hx.1,fun hg => hx.2 ⟨c,hg⟩⟩
end Release061

end

end OAI
