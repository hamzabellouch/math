import OAI.Geometry.SurfaceImmersion.Geometry.GeometricCurvePaths

namespace OAI

/-! Each retained compact interval edge is parametrized by an injective
path, in either orientation. -/
noncomputable section
open Set Topology unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

def CurveEdgeWitness.path {V E : Set X} (w : CurveEdgeWitness V E) :
    Path w.leftPoint w.rightPoint where
  toFun t := w.param ((iccHomeoI w.lo w.hi w.ordered).symm t)
  continuous_toFun := w.param_closedEmbedding.continuous.comp (iccHomeoI w.lo w.hi w.ordered).symm.continuous
  source' := by
    change w.param _ = w.param ⟨w.lo,le_rfl,w.ordered.le⟩
    congr 1
    apply Subtype.ext
    simp
  target' := by
    change w.param _ = w.param ⟨w.hi,w.ordered.le,le_rfl⟩
    congr 1
    apply Subtype.ext
    simp

lemma CurveEdgeWitness.path_injective {V E : Set X} (w : CurveEdgeWitness V E) :
    Function.Injective w.path :=
  w.param_closedEmbedding.injective.comp (iccHomeoI w.lo w.hi w.ordered).symm.injective

lemma CurveEdgeWitness.path_range {V E : Set X} (w : CurveEdgeWitness V E) :
    range w.path = closure E := by
  change range (w.param ∘ (iccHomeoI w.lo w.hi w.ordered).symm) = _
  rw [range_comp,(iccHomeoI w.lo w.hi w.ordered).symm.surjective.range_eq,image_univ,w.param_range]

lemma CurveEdgeWitness.endpoint_iff {V E : Set X} (w : CurveEdgeWitness V E)
    (hdis : Disjoint E V) {p : X} (hp : p ∈ V) :
    p ∈ closure E ↔ p = w.leftPoint ∨ p = w.rightPoint := by
  have hnot : p ∉ E := fun h => disjoint_left.mp hdis h hp
  have he : p ∈ closure E ↔ p ∈ closure E \ E := by simp only [mem_sdiff,hnot,not_false_eq_true,and_true]
  rw [he,w.frontier_eq]
  simp only [mem_insert_iff,mem_singleton_iff]

lemma CurveEdgeWitness.oriented_path {V E : Set X} (w : CurveEdgeWitness V E)
    (hdis : Disjoint E V) {p q : X} (hp : p ∈ V) (hq : q ∈ V) (hne : p ≠ q)
    (hpE : p ∈ closure E) (hqE : q ∈ closure E) :
    ∃ γ : Path p q, Function.Injective γ ∧ range γ = closure E := by
  rcases (w.endpoint_iff hdis hp).mp hpE with hpl | hpr <;>
    rcases (w.endpoint_iff hdis hq).mp hqE with hql | hqr
  · exact False.elim (hne (hpl.trans hql.symm))
  · exact ⟨w.path.cast hpl hqr,w.path_injective,w.path_range⟩
  · refine ⟨w.path.symm.cast hpr hql,?_,?_⟩
    · exact w.path_injective.comp unitInterval.symm_bijective.injective
    · simpa only [Path.cast_coe,Path.symm_range] using w.path_range
  · exact False.elim (hne (hpr.trans hqr.symm))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
