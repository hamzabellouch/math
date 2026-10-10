import OAI.Geometry.SurfaceImmersion.Whitney.ReturningCornerParameters

namespace OAI

/-! Small-scale data for graph branches advancing in the same horizontal direction. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

theorem advancing_corner_parameters (C : RegularPathCornerChart γ t)
    (hl : StrictMono C.leftParameter) (hr : StrictMono C.rightParameter)
    {V : Set Base} (hV : IsOpen V) (htV : C.chart (γ.extend t) ∈ V) :
    ∃ b > 0,
      C.leftParameter t-2*b ∈ C.leftParameter '' Ioo C.lower t ∧
      C.leftParameter t+2*b ∈ C.rightParameter '' Ioo t C.upper ∧
      ∀ s ∈ Icc (-2:ℝ) 2, ∀ θ ∈ Icc (0:ℝ) 1,
        (1-θ) • graphPoint C.leftGraph (C.leftParameter t+b*s) +
          θ • graphPoint C.rightGraph (C.leftParameter t+b*s) ∈ V := by
  have hp : graphPoint C.leftGraph (C.leftParameter t) ∈ V := by
    rw [graphPoint,← (C.left_chart t ⟨C.lower_lt.le,le_rfl⟩).2]
    exact htV
  obtain ⟨δ,hδ,hblend⟩ := small_graph_blends C.left_smooth.continuous C.right_smooth.continuous
    (C.leftParameter t) C.graphs_meet hV hp
  let w := min δ (min (C.leftParameter t-C.leftParameter C.lower)
    (C.rightParameter C.upper-C.leftParameter t))
  have hL : 0 < C.leftParameter t-C.leftParameter C.lower := sub_pos.mpr (hl C.lower_lt)
  have hR : 0 < C.rightParameter C.upper-C.leftParameter t := by
    rw [C.parameter_match]
    exact sub_pos.mpr (hr C.lt_upper)
  have hw : 0 < w := lt_min hδ (lt_min hL hR)
  have hwδ : w ≤ δ := min_le_left _ _
  have hwL : w ≤ C.leftParameter t-C.leftParameter C.lower :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hwR : w ≤ C.rightParameter C.upper-C.leftParameter t :=
    (min_le_right _ _).trans (min_le_right _ _)
  let b := w/4
  have hb : 0 < b := div_pos hw (by norm_num)
  refine ⟨b,hb,?_,?_,?_⟩
  · rw [C.leftParameter.continuous.continuousOn.image_Ioo_of_strictMonoOn
      C.lower_lt.le (hl.strictMonoOn _)]
    dsimp only [b]
    constructor <;> linarith
  · rw [C.rightParameter.continuous.continuousOn.image_Ioo_of_strictMonoOn
      C.lt_upper.le (hr.strictMonoOn _),← C.parameter_match]
    dsimp only [b]
    constructor <;> linarith
  · intro s hs θ hθ
    apply hblend _ _ θ hθ
    dsimp only [b]
    have h1 := mul_le_mul_of_nonneg_left hs.1 hw.le
    have h2 := mul_le_mul_of_nonneg_left hs.2 hw.le
    constructor <;> linarith

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
