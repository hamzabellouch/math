import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LocalChartDecisions

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section InactiveQuadrantAnchors

theorem positive_slope_quadrant_anchor (b c : CutRing) (hb : 1 ≤ ordinary b)
    (x y : ℝ) (h : 0 < y-ordinary b*x-ordinary c) :
    ∃ u v : CutRing, v-b*u=c ∧
      0 < ordinary u-x ∧ ordinary u-x < y-ordinary b*x-ordinary c ∧
      0 < y-ordinary v ∧ y-ordinary v < y-ordinary b*x-ordinary c := by
  let δ := y-ordinary b*x-ordinary c
  have hb' : 0 < ordinary b := by linarith
  have hδ : 0 < δ := h
  have hinterval : x+(δ/4)/ordinary b < x+(3*δ/4)/ordinary b := by
    apply add_lt_add_right
    exact (div_lt_div_iff_of_pos_right hb').mpr (by linarith)
  obtain ⟨u,hu,hu'⟩ := exists_cut_between hinterval
  have hL : δ/4 < (ordinary u-x)*ordinary b :=
    (div_lt_iff₀ hb').mp (by linarith)
  have hU : (ordinary u-x)*ordinary b < 3*δ/4 :=
    (lt_div_iff₀ hb').mp (by linarith)
  have hux : 0 < ordinary u-x := by nlinarith
  refine ⟨u,b*u+c,by ring,hux,?_,?_,?_⟩
  · nlinarith
  · simp only [map_add,map_mul]
    dsimp [δ] at hL hU
    nlinarith
  · simp only [map_add,map_mul]
    dsimp [δ] at hL hU
    nlinarith

theorem negative_slope_quadrant_anchor (b c : CutRing) (hb : 1 ≤ ordinary b)
    (x y : ℝ) (h : y-ordinary b*x-ordinary c < 0) :
    ∃ u v : CutRing, v-b*u=c ∧
      0 < x-ordinary u ∧ x-ordinary u < -(y-ordinary b*x-ordinary c) ∧
      0 < ordinary v-y ∧ ordinary v-y < -(y-ordinary b*x-ordinary c) := by
  obtain ⟨u,v,he,hx,hx',hy,hy'⟩ := positive_slope_quadrant_anchor b (-c) hb (-x) (-y)
    (by simp only [map_neg]; linarith)
  refine ⟨-u,-v,?_,?_,?_,?_,?_⟩
  · linear_combination -he
  all_goals simp only [map_neg] at *; linarith

theorem inactive_slope_quadrant_anchor (a : ℕ) (d : Fin 2) (c s : CutRing)
    (x : ℝ × ℝ) (hx : cutForm a (slopeDirection d) x ≠ ordinary c)
    (hs : |cutForm a (slopeDirection d) x-ordinary c| < ordinary s) :
    ∃ u : CutRing × CutRing, ∃ positive : Bool,
      integralCutForm a (slopeDirection d) u=c ∧
      (positive=true ↔ ordinary c < cutForm a (slopeDirection d) x) ∧
      ∀ j : Fin 2,
        ordinary (pointCoordinate u j)+ordinary (signQuadrantLower s d positive j) < realCoordinate x j ∧
        realCoordinate x j < ordinary (pointCoordinate u j)+ordinary (signQuadrantUpper s d positive j) := by
  have hb : 1 ≤ ordinary (cutTau^a) := by
    simpa using one_le_pow₀ Real.one_lt_goldenRatio.le
  fin_cases d
  · change x.2-Real.goldenRatio^a*x.1 ≠ ordinary c at hx
    change |x.2-Real.goldenRatio^a*x.1-ordinary c| < ordinary s at hs
    rcases lt_or_gt_of_ne hx with h | h
    · obtain ⟨u,v,he,hx₀,hx₁,hy₀,hy₁⟩ := negative_slope_quadrant_anchor (cutTau^a) c hb x.1 x.2
        (by simpa only [map_pow,ordinary_cutTau] using sub_neg.mpr h)
      refine ⟨(u,v),false,by simpa [integralCutForm,slopeDirection] using he,by simp [cutForm,slopeDirection]; linarith,?_⟩
      rw [abs_of_neg (sub_neg.mpr h)] at hs
      simp only [map_pow,ordinary_cutTau] at hx₁ hy₁
      intro j; fin_cases j <;> simp [realCoordinate,pointCoordinate,signQuadrantLower,signQuadrantUpper] <;>
        constructor <;> linarith
    · obtain ⟨u,v,he,hx₀,hx₁,hy₀,hy₁⟩ := positive_slope_quadrant_anchor (cutTau^a) c hb x.1 x.2
        (by simpa only [map_pow,ordinary_cutTau] using sub_pos.mpr h)
      refine ⟨(u,v),true,by simpa [integralCutForm,slopeDirection] using he,by simp; exact h,?_⟩
      rw [abs_of_pos (sub_pos.mpr h)] at hs
      simp only [map_pow,ordinary_cutTau] at hx₁ hy₁
      intro j; fin_cases j <;> simp [realCoordinate,pointCoordinate,signQuadrantLower,signQuadrantUpper] <;>
        constructor <;> linarith
  · change x.1-Real.goldenRatio^a*x.2 ≠ ordinary c at hx
    change |x.1-Real.goldenRatio^a*x.2-ordinary c| < ordinary s at hs
    rcases lt_or_gt_of_ne hx with h | h
    · obtain ⟨u,v,he,hx₀,hx₁,hy₀,hy₁⟩ := negative_slope_quadrant_anchor (cutTau^a) c hb x.2 x.1
        (by simpa only [map_pow,ordinary_cutTau] using sub_neg.mpr h)
      refine ⟨(v,u),false,by simpa [integralCutForm,slopeDirection] using he,by simp [cutForm,slopeDirection]; linarith,?_⟩
      rw [abs_of_neg (sub_neg.mpr h)] at hs
      simp only [map_pow,ordinary_cutTau] at hx₁ hy₁
      intro j; fin_cases j <;> simp [realCoordinate,pointCoordinate,signQuadrantLower,signQuadrantUpper] <;>
        constructor <;> linarith
    · obtain ⟨u,v,he,hx₀,hx₁,hy₀,hy₁⟩ := positive_slope_quadrant_anchor (cutTau^a) c hb x.2 x.1
        (by simpa only [map_pow,ordinary_cutTau] using sub_pos.mpr h)
      refine ⟨(v,u),true,by simpa [integralCutForm,slopeDirection] using he,by simp; exact h,?_⟩
      rw [abs_of_pos (sub_pos.mpr h)] at hs
      simp only [map_pow,ordinary_cutTau] at hx₁ hy₁
      intro j; fin_cases j <;> simp [realCoordinate,pointCoordinate,signQuadrantLower,signQuadrantUpper] <;>
        constructor <;> linarith

end InactiveQuadrantAnchors

end SimpleAmenable
end
end

end OAI
