import OAI.Geometry.SurfaceImmersion.Whitney.ReturningCornerArc
import OAI.Geometry.SurfaceImmersion.Whitney.AdvancingCornerArc

namespace OAI

/-! The rounded graph cannot meet the portions of either old branch
lying beyond its attachment points. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

theorem returning_arc_local_separation (C : RegularPathCornerChart γ t)
    (P : SmoothCompactArc planeModel M)
    (hl : StrictAnti C.leftParameter) (hr : StrictMono C.rightParameter)
    {a b l r : ℝ} (hb : 0 < b) (hlt : l < t) (htr : t < r)
    (hPs : P.start = -2) (hPf : P.finish = 2)
    (hleft : C.leftParameter l = a+4*b) (hright : C.rightParameter r = a+4*b)
    (hcoord : ∀ s ∈ Icc P.start P.finish,
      C.chart (P.curve s) 0 = a+b*s^2) :
    ∀ s ∈ Icc P.start P.finish, ∀ u ∈ Ico C.lower l ∪ Ioc r C.upper,
      P.curve s ≠ γ.extend u := by
  intro s hs u hu he
  have hxy : C.chart (γ.extend u) 0 = a+b*s^2 := by rw [← he]; exact hcoord s hs
  have hs' : s ∈ Icc (-2:ℝ) 2 := by simpa only [hPs,hPf] using hs
  have hsq : s^2 ≤ 4 := by nlinarith [sq_nonneg (s+2),sq_nonneg (s-2),mul_nonneg (by linarith [hs'.1] : 0 ≤ s+2) (by linarith [hs'.2] : 0 ≤ 2-s)]
  have hxbound : a+b*s^2 ≤ a+4*b := by nlinarith
  rcases hu with hu | hu
  · have hC := congrFun (C.left_chart u ⟨hu.1,hu.2.le.trans hlt.le⟩).2 0
    change C.chart (γ.extend u) 0 = C.leftParameter u at hC
    have hm := hl hu.2
    rw [hleft,← hC,hxy] at hm
    exact (not_lt_of_ge hxbound) hm
  · have hC := congrFun (C.right_chart u ⟨htr.le.trans hu.1.le,hu.2⟩).2 0
    change C.chart (γ.extend u) 0 = C.rightParameter u at hC
    have hm := hr hu.1
    rw [hright,← hC,hxy] at hm
    exact (not_lt_of_ge hxbound) hm

theorem advancing_arc_local_separation (C : RegularPathCornerChart γ t)
    (P : SmoothCompactArc planeModel M)
    (hl : StrictMono C.leftParameter) (hr : StrictMono C.rightParameter)
    {a b l r : ℝ} (hb : 0 < b) (hlt : l < t) (htr : t < r)
    (hPs : P.start = -2) (hPf : P.finish = 2)
    (hleft : C.leftParameter l = a-2*b) (hright : C.rightParameter r = a+2*b)
    (hcoord : ∀ s ∈ Icc P.start P.finish,
      C.chart (P.curve s) 0 = a+b*s) :
    ∀ s ∈ Icc P.start P.finish, ∀ u ∈ Ico C.lower l ∪ Ioc r C.upper,
      P.curve s ≠ γ.extend u := by
  intro s hs u hu he
  have hxy : C.chart (γ.extend u) 0 = a+b*s := by rw [← he]; exact hcoord s hs
  have hs' : s ∈ Icc (-2:ℝ) 2 := by simpa only [hPs,hPf] using hs
  have hxlo : a-2*b ≤ a+b*s := by nlinarith [hs'.1]
  have hxhi : a+b*s ≤ a+2*b := by nlinarith [hs'.2]
  rcases hu with hu | hu
  · have hC := congrFun (C.left_chart u ⟨hu.1,hu.2.le.trans hlt.le⟩).2 0
    change C.chart (γ.extend u) 0 = C.leftParameter u at hC
    have hm := hl hu.2
    rw [hleft,← hC,hxy] at hm
    exact (not_lt_of_ge hxlo) hm
  · have hC := congrFun (C.right_chart u ⟨htr.le.trans hu.1.le,hu.2⟩).2 0
    change C.chart (γ.extend u) 0 = C.rightParameter u at hC
    have hm := hr hu.1
    rw [hright,← hC,hxy] at hm
    exact (not_lt_of_ge hxhi) hm

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
