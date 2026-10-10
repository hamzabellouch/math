import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ClippedLineSlide

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LocalChartDecisions

theorem fract_fract_add_eq (x y : ℝ) :
    Int.fract (Int.fract x+y)=Int.fract (x+y) := by
  change Int.fract (x-(⌊x⌋:ℝ)+y)=_
  rw [sub_add_eq_add_sub,Int.fract_sub_intCast]

theorem translate_planar_lift {a : ℕ} (p : GenericSquare a) (z : ℝ × ℝ)
    (hz : p.val=(Int.fract z.1,Int.fract z.2)) (u : CutRing × CutRing) :
    (translate a u p).val=(Int.fract (z.1+ordinary u.1),Int.fract (z.2+ordinary u.2)) := by
  simp only [translate_val,hz,fract_fract_add_eq]

theorem translated_clippedSlope_planar {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (u : CutRing × CutRing)
    (p : GenericSquare a) (z : ℝ × ℝ)
    (hz : p.val=(Int.fract z.1,Int.fract z.2))
    (hnear : |z.1-ordinary u.1|<ordinary r ∧ |z.2-ordinary u.2|<ordinary r) :
    p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ↔
      ordinary (integralCutForm a j u)≤cutForm a j z := by
  change translate a (-u) p ∈ (clippedSlopePrimitive a r j).val ↔ _
  have hp := translate_planar_lift p z hz (-u)
  simp only [Prod.fst_neg,Prod.snd_neg,map_neg,← sub_eq_add_neg] at hp
  rw [mem_clippedSlope_lift r j hr _ (z-(ordinary u.1,ordinary u.2))
    ⟨abs_lt.mp hnear.1,abs_lt.mp hnear.2⟩ hp,cutForm_sub,cutForm_ordinary]
  exact sub_nonneg

theorem fract_coordinate_sign (x : ℝ)
    (hl : -(2-Real.goldenRatio)<x) (hu : x<Real.goldenRatio-1) :
    Int.fract x<Real.goldenRatio-1 ↔ 0≤x := by
  have hτ := Real.one_lt_goldenRatio
  have hτ' := Real.goldenRatio_lt_two
  by_cases hx : 0≤x
  · rw [Int.fract_eq_self.mpr ⟨hx,by linarith⟩]
    exact iff_of_true hu hx
  · have hxf : Int.fract x=x+1 := by
      rw [← Int.fract_add_one x,Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩]
    rw [hxf]
    exact iff_of_false (by linarith) hx

noncomputable def realCoordinate (z : ℝ × ℝ) (j : Fin 2) : ℝ := ![z.1,z.2] j

theorem translated_coordinate_planar {a : ℕ} (j : Fin 2) (u : CutRing × CutRing)
    (p : GenericSquare a) (z : ℝ × ℝ)
    (hz : p.val=(Int.fract z.1,Int.fract z.2))
    (hl : -(2-Real.goldenRatio)<realCoordinate z j-ordinary (pointCoordinate u j))
    (hu : realCoordinate z j-ordinary (pointCoordinate u j)<Real.goldenRatio-1) :
    p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
      ordinary (pointCoordinate u j)≤realCoordinate z j := by
  have ht := translate_planar_lift p z hz (-u)
  simp only [Prod.fst_neg,Prod.snd_neg,map_neg,← sub_eq_add_neg] at ht
  have hc : coordinate j (translate a (-u) p)=
      Int.fract (realCoordinate z j-ordinary (pointCoordinate u j)) := by
    fin_cases j
    · exact congrArg Prod.fst ht
    · exact congrArg Prod.snd ht
  have hmem : p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
      coordinate j (translate a (-u) p)<Real.goldenRatio-1 := by
    change (cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val<ordinary (cutTau-1) ∧
      ¬cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val<ordinary 0) ↔ _
    have hform : cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val=
        coordinate j (translate a (-u) p) := by fin_cases j <;> rfl
    simp only [hform,map_sub,ordinary_cutTau,map_one,map_zero,not_lt,
      (coordinate_bounds j (translate a (-u) p)).1,and_true]
  rw [hmem,hc,fract_coordinate_sign _ hl hu]
  exact sub_nonneg

end LocalChartDecisions

section LineParameters

theorem slope_same_intercept (a : ℕ) (d : Fin 2) (z z' : CutRing × CutRing)
    (h : integralCutForm a (slopeDirection d) z = integralCutForm a (slopeDirection d) z') :
    ∃ w : CutRing, z'=z+tangentOffset a d w := by
  fin_cases d
  · refine ⟨z'.1-z.1,?_⟩
    change z.2-cutTau^a*z.1=z'.2-cutTau^a*z'.1 at h
    apply Prod.ext
    · simp [tangentOffset]
    · simp [tangentOffset]
      linear_combination -h
  · refine ⟨z'.2-z.2,?_⟩
    change z.1-cutTau^a*z.2=z'.1-cutTau^a*z'.2 at h
    apply Prod.ext
    · simp [tangentOffset]
      linear_combination -h
    · simp [tangentOffset]

theorem real_slope_parameter (a : ℕ) (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ)
    (h : cutForm a (slopeDirection d) z=ordinary (integralCutForm a (slopeDirection d) u)) :
    ∃ c : ℝ, ∀ j : Fin 2,
      realCoordinate z j=ordinary (pointCoordinate u j)+tangentCoefficient a d j*c := by
  fin_cases d
  · refine ⟨z.1-ordinary u.1,?_⟩
    change z.2-Real.goldenRatio^a*z.1=ordinary (u.2-cutTau^a*u.1) at h
    simp only [map_sub,map_mul,map_pow,ordinary_cutTau] at h
    intro j; fin_cases j
    · simp [realCoordinate,pointCoordinate,tangentCoefficient,tangentOffset]
    · simp [realCoordinate,pointCoordinate,tangentCoefficient,tangentOffset]
      linear_combination h
  · refine ⟨z.2-ordinary u.2,?_⟩
    change z.1-Real.goldenRatio^a*z.2=ordinary (u.1-cutTau^a*u.2) at h
    simp only [map_sub,map_mul,map_pow,ordinary_cutTau] at h
    intro j; fin_cases j
    · simp [realCoordinate,pointCoordinate,tangentCoefficient,tangentOffset]
      linear_combination h
    · simp [realCoordinate,pointCoordinate,tangentCoefficient,tangentOffset]

end LineParameters

end SimpleAmenable
end
end

end OAI
