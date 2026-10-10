import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapCoordinateRegularity
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapNormalDefect

namespace OAI

/-! The actual pair has exactly two nondegenerate normal-defect zeros
in a single rectangular coordinate neighborhood. -/
noncomputable section
open Set Filter Matrix Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.nondegenerate_normal_defect (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ (a : Fin 3 → ℝ) (δ : ℝ) (U : Set Base), 0 < δ ∧ IsOpen U ∧ U ⊆ S.domain ∧
      (∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (A.arc.start-δ) (A.arc.finish+δ), (![x,t] : Base) ∈ U) ∧
      ContDiffOn ℝ ∞ (normalDefect S.model a) U ∧
      (∀ x ∈ U, normalDefect S.model a x = 0 ↔
        x = ![0,A.arc.start] ∨ x = ![0,A.arc.finish]) ∧
      Function.Bijective (fderiv ℝ (normalDefect S.model a) (![0,A.arc.start] : Base)) ∧
      Function.Bijective (fderiv ℝ (normalDefect S.model a) (![0,A.arc.finish] : Base)) := by
  classical
  obtain ⟨a,ha⟩ := exists_curve_transverse_vector S.transverseVector S.transverseVector_smooth
  obtain ⟨V,hV,hVD,hVaxis,hVI⟩ := S.regular_neighborhood hf
  let U := V ∩ normalFrameDomain S.model a
  have hU : IsOpen U := hV.inter (normalFrameDomain_open S.model_smooth a)
  have hframe : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ normalFrameDomain S.model a := by
    intro t ht
    change transverseDerivative S.model (![0,t] : Base) ⨯₃ a ≠ 0
    rw [S.transverseDerivative_axis]
    exact curve_transverse_cross_ne_zero (S.transverseVector_ne_zero ht) (ha t)
  have hUaxis : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U :=
    fun t ht => ⟨hVaxis t ht,hframe t ht⟩
  obtain ⟨δ,hδ,hrect⟩ := compact_axis_rectangle A.arc.start_lt_finish.le hU hUaxis
  have hl := hframe A.arc.start (left_mem_Icc.mpr A.arc.start_lt_finish.le)
  have hr := hframe A.arc.finish (right_mem_Icc.mpr A.arc.start_lt_finish.le)
  refine ⟨a,δ,U,hδ,hU,inter_subset_left.trans hVD,hrect,?_,?_,?_,?_⟩
  · exact normalDefect_smooth S.model_smooth (fun _ hx => normalFrameDomain_nonzero hx.2)
      (fun _ hx => normalFrameDomain_transverse hx.2)
  · intro x hx
    have hh : normalDefect S.model a x ≠ 0 ↔
        x ≠ ![0,A.arc.start] ∧ x ≠ ![0,A.arc.finish] :=
      (normalDefect_immersion_iff S.model a x (normalFrameDomain_nonzero hx.2)
        (normalFrameDomain_transverse hx.2)).symm.trans (hVI x hx.1)
    simpa only [not_not,not_and_or] using not_congr hh
  · exact normalDefect_nondegenerate_of_direction S.model_smooth a _
      (normalFrameDomain_nonzero hl) (normalFrameDomain_transverse hl) S.left_vertical
      S.endpoint_direction_regular.1
  · exact normalDefect_nondegenerate_of_direction S.model_smooth a _
      (normalFrameDomain_nonzero hr) (normalFrameDomain_transverse hr) S.right_vertical
      S.endpoint_direction_regular.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
