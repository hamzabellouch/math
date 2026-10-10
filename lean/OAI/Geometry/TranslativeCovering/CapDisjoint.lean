import OAI.Geometry.TranslativeCovering.CrossSlots

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1

namespace CapDisjoint
open Set Real
open scoped RealInnerProductSpace
variable {V : Type u_1} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma projective_le_arccos {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ProjectiveCaps.angle x y ≤ Real.arccos |⟪x,y⟫| := by
  by_cases h : 0 ≤ ⟪x,y⟫
  · rw [abs_of_nonneg h]
    exact (min_le_left _ _).trans_eq (by simp [InnerProductGeometry.angle,hx,hy])
  · rw [abs_of_neg (lt_of_not_ge h)]
    exact (min_le_right _ _).trans_eq (by simp [InnerProductGeometry.angle,hx,hy])

lemma radius {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Real.arccos (1/Real.sqrt (1+4*ε)) ≤ 2*Real.sqrt ε := by
  have hs := Real.sqrt_nonneg ε
  have hsq := Real.sq_sqrt hε
  have hle : Real.sqrt ε ≤ 1 := by nlinarith only [hs,hsq,hε1]
  have hpi := Real.pi_gt_three
  have hc := Real.cos_le_one_div_sqrt_sq_add_one
    (x := 2*Real.sqrt ε) (by nlinarith only [hs,hpi]) (by nlinarith only [hle,hpi])
  have he : (2*Real.sqrt ε)^2+1 = 1+4*ε := by nlinarith only [hsq]
  rw [he] at hc
  have hh := Real.arccos_le_arccos hc
  rw [Real.arccos_cos (by positivity) (by nlinarith only [hle,hpi])] at hh
  exact hh

lemma disjoint {ε t s : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (ht : 1/Real.sqrt (1+4*ε) ≤ t) (hs : 1/Real.sqrt (1+4*ε) ≤ s)
    (hangle : 4*Real.sqrt ε < ProjectiveCaps.angle x y) :
    Disjoint {u : V | ‖u‖ = 1 ∧ t < |⟪u,x⟫|}
      {u : V | ‖u‖ = 1 ∧ s < |⟪u,y⟫|} := by
  rw [Set.disjoint_left]
  intro u hu hv
  have hux := (projective_le_arccos hu.1 hx).trans
    ((Real.arccos_le_arccos (ht.trans hu.2.le)).trans (radius hε hε1))
  have huy := (projective_le_arccos hu.1 hy).trans
    ((Real.arccos_le_arccos (hs.trans hv.2.le)).trans (radius hε hε1))
  have htri := ProjectiveCaps.angle_triangle x u y
  rw [ProjectiveCaps.angle_comm x u] at htri
  linarith only [htri,hux,huy,hangle]

end CapDisjoint

end OAI
