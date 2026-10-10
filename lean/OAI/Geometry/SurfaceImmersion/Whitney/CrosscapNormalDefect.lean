import OAI.Geometry.SurfaceImmersion.Geometry.NormalDefectDomain
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapStripRegularNeighborhood

namespace OAI

/-! The actual crosscap pair is exactly the zero set of a smooth
normal-defect map on one open rectangle. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.normal_defect_two_zeros (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ (a : Fin 3 → ℝ) (δ : ℝ) (U : Set Base), 0 < δ ∧ IsOpen U ∧ U ⊆ S.domain ∧
      (∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (A.arc.start-δ) (A.arc.finish+δ), (![x,t] : Base) ∈ U) ∧
      ContDiffOn ℝ ∞ (normalDefect S.model a) U ∧
      ∀ x ∈ U, normalDefect S.model a x = 0 ↔
        x = ![0,A.arc.start] ∨ x = ![0,A.arc.finish] := by
  classical
  obtain ⟨a,r,V,hr,hV,hVD,hrect,hN,hNI⟩ := S.normal_defect_rectangle
  obtain ⟨W,hW,hWD,hWaxis,hWI⟩ := S.regular_neighborhood hf
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  have haxis : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U := by
    intro t ht
    refine ⟨?_,hWaxis t ht⟩
    apply hrect 0 ⟨by linarith,by linarith⟩ t
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨δ,hδ,hδrect⟩ := compact_axis_rectangle A.arc.start_lt_finish.le hU haxis
  refine ⟨a,δ,U,hδ,hU,inter_subset_left.trans hVD,hδrect,hN.mono inter_subset_left,?_⟩
  intro x hx
  have hh : normalDefect S.model a x ≠ 0 ↔
      x ≠ ![0,A.arc.start] ∧ x ≠ ![0,A.arc.finish] :=
    (hNI x hx.1).symm.trans (hWI x hx.2)
  simpa only [not_not,not_and_or] using not_congr hh

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
