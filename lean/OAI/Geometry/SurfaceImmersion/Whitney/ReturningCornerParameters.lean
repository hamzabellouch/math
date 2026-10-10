import OAI.Geometry.SurfaceImmersion.Whitney.CornerGraphSeparation
import OAI.Geometry.SurfaceImmersion.Geometry.SmallGraphBlends

namespace OAI

/-! A genuine returning corner has separated graph traces arbitrarily near
its common endpoint, on an interval available for the explicit rounding. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

lemma graphs_meet (C : RegularPathCornerChart γ t) :
    C.leftGraph (C.leftParameter t) = C.rightGraph (C.leftParameter t) := by
  have hl := (C.left_chart t ⟨C.lower_lt.le,le_rfl⟩).2
  have hr := (C.right_chart t ⟨le_rfl,C.lt_upper.le⟩).2
  rw [← C.parameter_match] at hr
  exact congrFun (hl.symm.trans hr) 1

lemma returning_overlap (C : RegularPathCornerChart γ t)
    (hl : StrictAnti C.leftParameter) (hr : StrictMono C.rightParameter) :
    ∃ R > C.leftParameter t, ∀ x ∈ Ioo (C.leftParameter t) R,
      x ∈ C.leftParameter '' Ioo C.lower t ∧
      x ∈ C.rightParameter '' Ioo t C.upper := by
  let R := min (C.leftParameter C.lower) (C.rightParameter C.upper)
  have hR : C.leftParameter t < R := by
    apply lt_min
    · exact hl C.lower_lt
    · rw [C.parameter_match]
      exact hr C.lt_upper
  refine ⟨R,hR,?_⟩
  intro x hx
  constructor
  · rw [C.leftParameter.continuous.continuousOn.image_Ioo_of_strictAntiOn
      C.lower_lt.le (hl.strictAntiOn _)]
    exact ⟨hx.1,hx.2.trans_le (min_le_left _ _)⟩
  · rw [C.rightParameter.continuous.continuousOn.image_Ioo_of_strictMonoOn
      C.lt_upper.le (hr.strictMonoOn _),← C.parameter_match]
    exact ⟨hx.1,hx.2.trans_le (min_le_right _ _)⟩

theorem returning_corner_parameters (C : RegularPathCornerChart γ t)
    (hl : StrictAnti C.leftParameter) (hr : StrictMono C.rightParameter)
    {V : Set Base} (hV : IsOpen V) (htV : C.chart (γ.extend t) ∈ V) :
    ∃ a b : ℝ, 0 < b ∧ C.leftParameter t < a ∧
      (∀ x ∈ Icc a (a+4*b), x ∈ C.leftParameter '' Ioo C.lower t ∧
        x ∈ C.rightParameter '' Ioo t C.upper) ∧
      (∀ x ∈ Icc a (a+4*b), ∀ s ∈ Icc (0:ℝ) 1,
        (1-s) • graphPoint C.leftGraph x + s • graphPoint C.rightGraph x ∈ V) := by
  have hp : graphPoint C.leftGraph (C.leftParameter t) ∈ V := by
    rw [graphPoint,← (C.left_chart t ⟨C.lower_lt.le,le_rfl⟩).2]
    exact htV
  obtain ⟨δ,hδ,hblend⟩ := small_graph_blends C.left_smooth.continuous C.right_smooth.continuous
    (C.leftParameter t) C.graphs_meet hV hp
  obtain ⟨R,hR,hoverlap⟩ := C.returning_overlap hl hr
  let w := min δ (R-C.leftParameter t)
  have hw : 0 < w := lt_min hδ (sub_pos.mpr hR)
  have hwδ : w ≤ δ := min_le_left _ _
  have hwR : w ≤ R-C.leftParameter t := min_le_right _ _
  let a := C.leftParameter t+w/4
  let b := w/16
  have hb : 0 < b := div_pos hw (by norm_num)
  have hx : ∀ x ∈ Icc a (a+4*b), x ∈ Ioo (C.leftParameter t) R ∧
      x ∈ Ioo (C.leftParameter t-δ) (C.leftParameter t+δ) := by
    intro x hx
    dsimp only [a,b] at hx
    constructor
    · constructor <;> linarith [hx.1,hx.2]
    · constructor <;> linarith [hx.1,hx.2]
  refine ⟨a,b,hb,by dsimp [a]; linarith,?_,?_⟩
  · intro x hxx
    exact hoverlap x (hx x hxx).1
  · intro x hxx s hs
    exact hblend x (hx x hxx).2 s hs

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
