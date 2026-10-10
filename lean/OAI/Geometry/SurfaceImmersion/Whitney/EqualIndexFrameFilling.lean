import OAI.Geometry.SurfaceImmersion.Geometry.NormalizeFrameColumn
import OAI.Geometry.SurfaceImmersion.Whitney.ShiftedRotationFilling

namespace OAI

/-! The equal-index polynomial pair has a genuine compact relative frame filling. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def equalIndexFrame (x : Base) : Base →L[ℝ] FrameTarget :=
  axisNormalFrame 1 ((x 0)^2-(x 1)^2-1) (2*x 0*x 1)

theorem compact_equal_index_frame_filling_radius {R : ℝ} (hR : 1 < R) :
    ∃ (B : Base → Base →L[ℝ] FrameTarget) (K : Set Base),
      ContDiff ℝ ∞ B ∧ (∀ x, Function.Injective (B x)) ∧ IsCompact K ∧
      K ⊆ ball (0:Base) R ∧ ∀ x ∉ K, B =ᶠ[𝓝 x] equalIndexFrame := by
  obtain ⟨A,K,hA,hAI,hK,hKB,hAe⟩ := compact_shifted_double_filling_radius hR
  refine ⟨fun x => normalizeFrameColumn (A x),K,normalizeFrameColumn_smooth hA hAI,
    fun x => normalizeFrameColumn_injective (hAI x),hK,hKB,?_⟩
  intro x hx
  filter_upwards [hAe x hx] with y hy
  have he : shiftedDoubleFrame y =
      axisNormalFrame ((y 0)^2+(y 1)^2) ((y 0)^2-(y 1)^2-1) (2*y 0*y 1) :=
    shiftedRotationFrame_zero_c _ _ _
  have hr : 0 < (y 0)^2+(y 1)^2 := by
    have hp := firstColumnLength_pos (hAI y)
    rwa [hy,he,firstColumnLength_axisNormalFrame _ _ _ (by positivity)] at hp
  change normalizeFrameColumn (A y) = _
  rw [hy,he,normalizeFrameColumn_axisNormalFrame _ _ _ hr]
  rfl

theorem compact_equal_index_frame_filling :
    ∃ (B : Base → Base →L[ℝ] FrameTarget) (K : Set Base),
      ContDiff ℝ ∞ B ∧ (∀ x, Function.Injective (B x)) ∧ IsCompact K ∧
      K ⊆ ball (0:Base) 3 ∧ ∀ x ∉ K, B =ᶠ[𝓝 x] equalIndexFrame :=
  compact_equal_index_frame_filling_radius (by norm_num)

lemma equalIndexFrame_singular_iff (x : Base) :
    ¬ Function.Injective (equalIndexFrame x) ↔ x = ![1,0] ∨ x = ![-1,0] := by
  have hi : Function.Injective (equalIndexFrame x) ↔
      (x 0)^2-(x 1)^2-1 ≠ 0 ∨ 2*x 0*x 1 ≠ 0 := by
    constructor
    · intro hi
      by_contra hn
      push Not at hn
      have he : equalIndexFrame x (![0,1] : Base) = equalIndexFrame x 0 := by
        simp [equalIndexFrame,axisNormalFrame,hn.1,hn.2]
      have hh := congrFun (hi he) 1
      norm_num at hh
    · exact fun h => axisNormalFrame_injective (by norm_num) h
  rw [hi]
  constructor
  · intro hn
    push Not at hn
    have hab : x 0*x 1 = 0 := by nlinarith [hn.2]
    have h1 : x 1 = 0 := by
      rcases mul_eq_zero.mp hab with h0 | h1
      · nlinarith [hn.1,sq_nonneg (x 1)]
      · exact h1
    have h0 : x 0 = 1 ∨ x 0 = -1 := by
      have hs : (x 0-1)*(x 0+1) = 0 := by nlinarith [hn.1,h1]
      rcases mul_eq_zero.mp hs with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases h0 with h0 | h0
    · left
      ext i
      fin_cases i
      · exact h0
      · exact h1
    · right
      ext i
      fin_cases i
      · exact h0
      · exact h1
  · rintro (rfl | rfl) <;> norm_num

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
