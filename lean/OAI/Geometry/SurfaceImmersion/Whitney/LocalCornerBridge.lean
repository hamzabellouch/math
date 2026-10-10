import OAI.Geometry.SurfaceImmersion.Whitney.ReturningCornerArc
import OAI.Geometry.SurfaceImmersion.Whitney.AdvancingCornerArc
import OAI.Geometry.SurfaceImmersion.Whitney.CornerChartReflection
import OAI.Geometry.SurfaceImmersion.Whitney.CornerParameterOrientation

namespace OAI

/-! Every actual corner of the finite embedded source path admits a
small regular embedded bridge with oriented smooth attachment germs. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} (γ : Path p q) (t : ℝ) (O : Set M)

structure LocalCornerBridge where
  arc : SmoothCompactArc planeModel M
  left : ℝ
  right : ℝ
  left_pos : 0 < left
  left_lt : left < t
  lt_right : t < right
  right_lt_one : right < 1
  leftParameter : ℝ → ℝ
  rightParameter : ℝ → ℝ
  left_smooth : ContDiff ℝ ∞ leftParameter
  right_smooth : ContDiff ℝ ∞ rightParameter
  left_value : leftParameter arc.start = left
  right_value : rightParameter arc.finish = right
  left_forward : 0 < deriv leftParameter arc.start
  right_forward : 0 < deriv rightParameter arc.finish
  left_germ : arc.curve =ᶠ[𝓝 arc.start] γ.extend ∘ leftParameter
  right_germ : arc.curve =ᶠ[𝓝 arc.finish] γ.extend ∘ rightParameter
  image_subset : MapsTo arc.curve (Icc arc.start arc.finish) O

variable {γ t O}
namespace RegularPathCornerChart

theorem returning_bridge (C : RegularPathCornerChart γ t) (hi : Function.Injective γ)
    (hl : StrictAnti C.leftParameter) (hr : StrictMono C.rightParameter)
    (hO : IsOpen O) (htO : γ.extend t ∈ O) : Nonempty (LocalCornerBridge γ t O) := by
  obtain ⟨P,a,b,l,r,hPs,hPf,hb,hLl,hlt,htr,hrU,hPleft,hPright,hPO,hPc,hPL,hPR⟩ :=
    C.returning_corner_arc hi hl hr hO htO
  have hlx : C.leftParameter l = a+b*P.start^2 := by
    have H := (hPc P.start (left_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPleft,(C.left_chart l ⟨hLl.le,hlt.le⟩).2] at H
    exact congrFun H 0
  have hrx : C.rightParameter r = a+b*P.finish^2 := by
    have H := (hPc P.finish (right_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPright,(C.right_chart r ⟨htr.le,hrU.le⟩).2] at H
    exact congrFun H 0
  let L : ℝ → ℝ := fun s => C.leftParameter.symm (a+b*s^2)
  let R : ℝ → ℝ := fun s => C.rightParameter.symm (a+b*s^2)
  have hLs : ContDiff ℝ ∞ L := C.left_inverse_smooth.comp (by fun_prop)
  have hRs : ContDiff ℝ ∞ R := C.right_inverse_smooth.comp (by fun_prop)
  refine ⟨⟨P,l,r,C.lower_pos.trans hLl,hlt,htr,hrU.trans C.upper_lt_one,
    L,R,hLs,hRs,?_,?_,?_,?_,hPL,hPR,hPO⟩⟩
  · change C.leftParameter.symm (a+b*P.start^2) = l
    rw [← hlx,C.leftParameter.symm_apply_apply]
  · change C.rightParameter.symm (a+b*P.finish^2) = r
    rw [← hrx,C.rightParameter.symm_apply_apply]
  · rw [hPs]
    exact returning_left_parameter_deriv_pos C.leftParameter C.left_parameter_smooth
      C.left_inverse_smooth hl a hb
  · rw [hPf]
    exact returning_right_parameter_deriv_pos C.rightParameter C.right_parameter_smooth
      C.right_inverse_smooth hr a hb

theorem advancing_bridge (C : RegularPathCornerChart γ t)
    (hl : StrictMono C.leftParameter) (hr : StrictMono C.rightParameter)
    (hO : IsOpen O) (htO : γ.extend t ∈ O) : Nonempty (LocalCornerBridge γ t O) := by
  obtain ⟨P,a,b,l,r,hPs,hPf,hb,hLl,hlt,htr,hrU,hPleft,hPright,hPO,hPc,hPL,hPR⟩ :=
    C.advancing_corner_arc hl hr hO htO
  have hlx : C.leftParameter l = a+b*P.start := by
    have H := (hPc P.start (left_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPleft,(C.left_chart l ⟨hLl.le,hlt.le⟩).2] at H
    exact congrFun H 0
  have hrx : C.rightParameter r = a+b*P.finish := by
    have H := (hPc P.finish (right_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPright,(C.right_chart r ⟨htr.le,hrU.le⟩).2] at H
    exact congrFun H 0
  let L : ℝ → ℝ := fun s => C.leftParameter.symm (a+b*s)
  let R : ℝ → ℝ := fun s => C.rightParameter.symm (a+b*s)
  have hLs : ContDiff ℝ ∞ L := C.left_inverse_smooth.comp (by fun_prop)
  have hRs : ContDiff ℝ ∞ R := C.right_inverse_smooth.comp (by fun_prop)
  refine ⟨⟨P,l,r,C.lower_pos.trans hLl,hlt,htr,hrU.trans C.upper_lt_one,
    L,R,hLs,hRs,?_,?_,?_,?_,hPL,hPR,hPO⟩⟩
  · change C.leftParameter.symm (a+b*P.start) = l
    rw [← hlx,C.leftParameter.symm_apply_apply]
  · change C.rightParameter.symm (a+b*P.finish) = r
    rw [← hrx,C.rightParameter.symm_apply_apply]
  · exact advancing_parameter_deriv_pos C.leftParameter C.left_parameter_smooth
      C.left_inverse_smooth hl a hb P.start
  · exact advancing_parameter_deriv_pos C.rightParameter C.right_parameter_smooth
      C.right_inverse_smooth hr a hb P.finish

end RegularPathCornerChart

variable [IsManifold planeModel ∞ M]

theorem local_corner_bridge (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    (ht : t ∈ Ioo (0:ℝ) 1) (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    Nonempty (LocalCornerBridge γ t O) := by
  obtain ⟨C⟩ := regular_path_corner_chart hγ hi ht
  rcases C.left_monotone with hl | hl <;> rcases C.right_monotone with hr | hr
  · exact C.advancing_bridge hl hr hO htO
  · exact C.reflect.returning_bridge hi (C.reflect_left_strictAnti hl)
      (C.reflect_right_strictMono hr) hO htO
  · exact C.returning_bridge hi hl hr hO htO
  · exact C.reflect.advancing_bridge (C.reflect_left_strictMono hl)
      (C.reflect_right_strictMono hr) hO htO

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
