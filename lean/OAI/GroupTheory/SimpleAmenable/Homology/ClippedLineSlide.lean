import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ClosedChartOverlap

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ClippedLineSlide

theorem coordinateRectangle_in_clippingOverlap {a : ℕ} (r : CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (z t : CutRing × CutRing) (L V : Fin 2 → CutRing)
    (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (ht : ∀ j, |ordinary (pointCoordinate t j)| ≤ 2*ordinary r)
    (hz : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z j) ∧
      ordinary (V j)-ordinary (pointCoordinate z j) ≤ ordinary r)
    (hzt : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate (z+t) j) ∧
      ordinary (V j)-ordinary (pointCoordinate (z+t) j) ≤ ordinary r) :
    coordinateRectangle a L V ≤ spatialTranslate z
      (coordinateRectangle a (clippingOverlapLower r t) (clippingOverlapUpper r t)) := by
  rw [spatialTranslate_coordinateRectangle]
  apply coordinateRectangle_mono L V _ _ _ hLV _ _
  · intro j
    have h0 := hz j
    have h1 := hzt j
    simp only [pointCoordinate_add,map_add] at h1
    change ordinary (clippingOverlapLower r t j + pointCoordinate z j) ≤ ordinary (L j)
    simp only [clippingOverlapLower,ordinary_orderedCutMax,map_add,map_sub,map_neg]
    have hh : max (-ordinary r) (ordinary (pointCoordinate t j)-ordinary r) ≤
        ordinary (L j)-ordinary (pointCoordinate z j) := max_le (by linarith) (by linarith)
    linarith
  · intro j
    have h0 := hz j
    have h1 := hzt j
    simp only [pointCoordinate_add,map_add] at h1
    change ordinary (V j) ≤ ordinary (clippingOverlapUpper r t j + pointCoordinate z j)
    simp only [clippingOverlapUpper,ordinary_orderedCutMin,map_add]
    have hh : ordinary (V j)-ordinary (pointCoordinate z j) ≤
        min (ordinary r) (ordinary (pointCoordinate t j)+ordinary r) := le_min (by linarith) (by linarith)
    linarith
  · intro j
    simpa only [map_add,add_sub_add_right_eq_sub] using (clippingOverlap_bounds r t hr ht j).2.1

noncomputable def tangentCoefficient (a : ℕ) (d j : Fin 2) : ℝ :=
  ordinary (pointCoordinate (tangentOffset a d 1) j)

theorem tangentCoefficient_pos (a : ℕ) (d j : Fin 2) : 0 < tangentCoefficient a d j := by
  fin_cases d <;> fin_cases j <;> simp [tangentCoefficient,pointCoordinate,tangentOffset,
    pow_pos Real.goldenRatio_pos]

theorem tangentCoefficient_bound (a : ℕ) (d j : Fin 2) :
    tangentCoefficient a d j ≤ 1+|ordinary (cutTau^a)| := by
  fin_cases d <;> fin_cases j <;> simp [tangentCoefficient,pointCoordinate,tangentOffset,
    abs_of_pos (pow_pos Real.goldenRatio_pos a)] <;> positivity

@[simp] theorem tangentOffset_coordinate (a : ℕ) (d j : Fin 2) (x : CutRing) :
    ordinary (pointCoordinate (tangentOffset a d x) j) = tangentCoefficient a d j*ordinary x := by
  fin_cases d <;> fin_cases j <;> simp [tangentCoefficient,pointCoordinate,tangentOffset]

noncomputable def tangentAllowedLower (a : ℕ) (r : CutRing) (d : Fin 2)
    (z : CutRing × CutRing) (V : Fin 2 → CutRing) : ℝ :=
  max ((ordinary (V 0)-ordinary (pointCoordinate z 0)-ordinary r)/tangentCoefficient a d 0)
    ((ordinary (V 1)-ordinary (pointCoordinate z 1)-ordinary r)/tangentCoefficient a d 1)

noncomputable def tangentAllowedUpper (a : ℕ) (r : CutRing) (d : Fin 2)
    (z : CutRing × CutRing) (L : Fin 2 → CutRing) : ℝ :=
  min ((ordinary (L 0)-ordinary (pointCoordinate z 0)+ordinary r)/tangentCoefficient a d 0)
    ((ordinary (L 1)-ordinary (pointCoordinate z 1)+ordinary r)/tangentCoefficient a d 1)

theorem tangentAllowed_iff (a : ℕ) (r : CutRing) (d : Fin 2)
    (z : CutRing × CutRing) (L V : Fin 2 → CutRing) (t : ℝ) :
    (tangentAllowedLower a r d z V ≤ t ∧ t ≤ tangentAllowedUpper a r d z L) ↔
      ∀ j : Fin 2, -ordinary r ≤ ordinary (L j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*t) ∧
        ordinary (V j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*t) ≤ ordinary r := by
  constructor
  · rintro ⟨hl,hu⟩ j
    have hl' : (ordinary (V j)-ordinary (pointCoordinate z j)-ordinary r)/tangentCoefficient a d j ≤ t := by
      fin_cases j
      · exact (le_max_left _ _).trans hl
      · exact (le_max_right _ _).trans hl
    have hu' : t ≤ (ordinary (L j)-ordinary (pointCoordinate z j)+ordinary r)/tangentCoefficient a d j := by
      fin_cases j
      · exact hu.trans (min_le_left _ _)
      · exact hu.trans (min_le_right _ _)
    have hlo := (div_le_iff₀ (tangentCoefficient_pos a d j)).mp hl'
    have hup := (le_div_iff₀ (tangentCoefficient_pos a d j)).mp hu'
    constructor <;> nlinarith
  · intro h
    have hlo (j : Fin 2) :
        (ordinary (V j)-ordinary (pointCoordinate z j)-ordinary r)/tangentCoefficient a d j ≤ t := by
      apply (div_le_iff₀ (tangentCoefficient_pos a d j)).mpr
      have hh := (h j).2
      nlinarith
    have hup (j : Fin 2) :
        t ≤ (ordinary (L j)-ordinary (pointCoordinate z j)+ordinary r)/tangentCoefficient a d j := by
      apply (le_div_iff₀ (tangentCoefficient_pos a d j)).mpr
      have hh := (h j).1
      nlinarith
    exact ⟨max_le (hlo 0) (hlo 1),le_min (hup 0) (hup 1)⟩

theorem tangentAllowed_wide (a : ℕ) (r u : CutRing) (hr : 0 < ordinary r)
    (d : Fin 2) (z : CutRing × CutRing) (L V : Fin 2 → CutRing) (c : ℝ)
    (hshort : 4*(1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) ≤ ordinary r)
    (hnear : ∀ j : Fin 2,
      |ordinary (L j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*c)| ≤ ordinary r/4 ∧
      |ordinary (V j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*c)| ≤ ordinary r/4) :
    4*(|ordinary u|+|ordinary (cutTau*u)|) ≤
      tangentAllowedUpper a r d z L-tangentAllowedLower a r d z V := by
  let b : ℝ := |ordinary u|+|ordinary (cutTau*u)|
  have hb : 0 ≤ b := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have he (j : Fin 2) : 2*tangentCoefficient a d j*b ≤ ordinary r/2 := by
    have hm := mul_le_mul_of_nonneg_right (tangentCoefficient_bound a d j) hb
    change 4*(1+|ordinary (cutTau^a)|)*b ≤ ordinary r at hshort
    nlinarith
  have hl := (tangentAllowed_iff a r d z L V (c-2*b)).mpr (by
    intro j
    have hn0 := abs_le.mp (hnear j).1
    have hn1 := abs_le.mp (hnear j).2
    have hh := he j
    have hp := mul_nonneg (tangentCoefficient_pos a d j).le hb
    constructor <;> nlinarith)
  have hu := (tangentAllowed_iff a r d z L V (c+2*b)).mpr (by
    intro j
    have hn0 := abs_le.mp (hnear j).1
    have hn1 := abs_le.mp (hnear j).2
    have hh := he j
    have hp := mul_nonneg (tangentCoefficient_pos a d j).le hb
    constructor <;> nlinarith)
  change 4*b ≤ _
  linarith

end ClippedLineSlide

end SimpleAmenable
end
end

end OAI
