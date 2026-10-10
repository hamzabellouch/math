import OAI.Geometry.SurfaceImmersion.Whitney.LocalCornerBridgeSeparation
import OAI.Geometry.SurfaceImmersion.Whitney.PathCornerNeighborhood

namespace OAI

/-! A local rounding can be chosen disjoint from the entire unchanged
part of the embedded compact source path. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ} {U O : Set M}

namespace LocalCornerBridge

def mono (B : LocalCornerBridge γ t U) (hUO : U ⊆ O) : LocalCornerBridge γ t O where
  arc := B.arc
  left := B.left
  right := B.right
  left_pos := B.left_pos
  left_lt := B.left_lt
  lt_right := B.lt_right
  right_lt_one := B.right_lt_one
  leftParameter := B.leftParameter
  rightParameter := B.rightParameter
  left_smooth := B.left_smooth
  right_smooth := B.right_smooth
  left_value := B.left_value
  right_value := B.right_value
  left_forward := B.left_forward
  right_forward := B.right_forward
  left_germ := B.left_germ
  right_germ := B.right_germ
  image_subset := fun _ hs => hUO (B.image_subset hs)

end LocalCornerBridge

namespace RegularPathCornerChart

theorem bridge_local_separation (C : RegularPathCornerChart γ t) (hi : Function.Injective γ)
    (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ B : LocalCornerBridge γ t O, C.lower < B.left ∧ B.right < C.upper ∧
      ∀ s ∈ Icc B.arc.start B.arc.finish, ∀ u ∈ Ico C.lower B.left ∪ Ioc B.right C.upper,
        B.arc.curve s ≠ γ.extend u := by
  rcases C.left_monotone with hl | hl <;> rcases C.right_monotone with hr | hr
  · exact C.advancing_bridge_local_separation hl hr hO htO
  · exact C.reflect.returning_bridge_local_separation hi (C.reflect_left_strictAnti hl)
      (C.reflect_right_strictMono hr) hO htO
  · exact C.returning_bridge_local_separation hi hl hr hO htO
  · exact C.reflect.advancing_bridge_local_separation (C.reflect_left_strictMono hl)
      (C.reflect_right_strictMono hr) hO htO

end RegularPathCornerChart

variable [IsManifold planeModel ∞ M] [T2Space M]

theorem separated_corner_bridge (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) (ht : t ∈ Ioo (0:ℝ) 1)
    (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ B : LocalCornerBridge γ t O,
      ∀ s ∈ Icc B.arc.start B.arc.finish, ∀ u ∈ Ico (0:ℝ) B.left ∪ Ioc B.right 1,
        B.arc.curve s ≠ γ.extend u := by
  obtain ⟨C⟩ := regular_path_corner_chart hγ hi ht
  obtain ⟨V,hV,htV,hVO,hfar⟩ := embedded_path_corner_neighborhood γ hi C.lower_pos.le
    C.lower_lt C.lt_upper C.upper_lt_one.le hO htO
  obtain ⟨B,hleft,hright,hlocal⟩ := C.bridge_local_separation hi hV htV
  refine ⟨B.mono hVO,?_⟩
  intro s hs u hu he
  rcases hu with hu | hu
  · by_cases hl : C.lower ≤ u
    · exact hlocal s hs u (Or.inl ⟨hl,hu.2⟩) he
    · exact hfar u (Or.inl ⟨hu.1,(lt_of_not_ge hl).le⟩) (he ▸ B.image_subset hs)
  · by_cases hr : u ≤ C.upper
    · exact hlocal s hs u (Or.inr ⟨hu.1,hr⟩) he
    · exact hfar u (Or.inr ⟨(lt_of_not_ge hr).le,hu.2⟩) (he ▸ B.image_subset hs)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
