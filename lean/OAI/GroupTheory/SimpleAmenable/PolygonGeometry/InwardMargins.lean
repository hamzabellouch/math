import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentInwardModel

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section InwardMargins
namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem mem_marginPolygon_of_planar (hr : ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (p : GenericSquare a) (y : ℝ × ℝ) (hy : p.val=(Int.fract y.1,Int.fract y.2))
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate y k ∧
      realCoordinate y k<ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (C.marginPolygon t u).val := by
  have hw (k) := (C.margins t).width C.positive k
  have hlen (k) : ordinary ((C.margins t).upper k+pointCoordinate u k)-
      ordinary ((C.margins t).lower k+pointCoordinate u k)<1 := by
    simp only [map_add]
    linarith [hw k,C.radius]
  have hle (k) : ordinary ((C.margins t).lower k+pointCoordinate u k) ≤
      ordinary ((C.margins t).upper k+pointCoordinate u k) := by
    simp only [map_add]
    linarith [hw k]
  have hh (k) : p ∈ coordinateBetween a k
      ((C.margins t).lower k+pointCoordinate u k)
      ((C.margins t).upper k+pointCoordinate u k) := by
    rw [mem_coordinateBetween_iff k _ _ (hle k) (hlen k)]
    refine ⟨⌊realCoordinate y k⌋,?_⟩
    have he : coordinate k p+(⌊realCoordinate y k⌋:ℤ)=realCoordinate y k := by
      have h := congrArg (fun q : ℝ × ℝ => realCoordinate q k) hy
      have hh : coordinate k p=Int.fract (realCoordinate y k) := by fin_cases k <;> exact h
      rw [hh]
      exact sub_add_cancel _ _
    rw [he]
    exact hcell k
  change p ∈ (spatialTranslate u (coordinateRectangle a (C.margins t).lower (C.margins t).upper)).val
  rw [spatialTranslate_coordinateRectangle]
  exact ⟨hh 0,hh 1⟩

theorem mem_inwardMargin_of_planar (hr : 0<ordinary r ∧ ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (z : ℝ × ℝ)
    (hboundary : ∀ k, realCoordinate z k=0 ∨ realCoordinate z k=1 →
      ordinary (pointCoordinate (u+C.anchors t (axisDirection k)) k)=realCoordinate z k)
    (hnearB : ∀ d, realCoordinate z d=0 ∨ realCoordinate z d=1 → ∀ y : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate y k ∧
        realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate y k-ordinary (pointCoordinate (u+C.anchors t (axisDirection d)) k)|<3*C.epsilon)
    (p : GenericSquare a)
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)≤realCoordinate p.val k ∧
      realCoordinate p.val k<ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (C.inwardMargin t u z).val := by
  have hy : p.val=(Int.fract p.val.1,Int.fract p.val.2) := by
    rw [Int.fract_eq_self.mpr p.property.1,Int.fract_eq_self.mpr p.property.2.1]
  have hpM := C.mem_marginPolygon_of_planar hr.2 t u p p.val hy hcell
  have hgate k : p ∈ (C.inwardGate t u z k).val := by
    by_cases hzero : realCoordinate z k=0
    · simp only [inwardGate,ite_eq_left hzero]
      have hd := C.positiveDecision_planar hr t u (axisDirection k)
        (hnearB k (Or.inl hzero)) p p.val hy (fun k => ⟨(hcell k).1,(hcell k).2.le⟩)
      rw [integralCutForm_axis,hboundary k (Or.inl hzero),hzero] at hd
      apply hd.mpr
      have haxis : cutForm a (axisDirection k) p.val=coordinate k p := by fin_cases k <;> rfl
      rw [haxis]
      exact (coordinate_bounds k p).1
    · by_cases hone : realCoordinate z k=1
      · simp only [inwardGate,ite_eq_right hzero,ite_eq_left hone]
        have hd := C.positiveDecision_planar hr t u (axisDirection k)
          (hnearB k (Or.inr hone)) p p.val hy (fun k => ⟨(hcell k).1,(hcell k).2.le⟩)
        rw [integralCutForm_axis,hboundary k (Or.inr hone),hone] at hd
        apply (not_congr hd).mpr
        have haxis : cutForm a (axisDirection k) p.val=coordinate k p := by fin_cases k <;> rfl
        rw [haxis]
        exact not_le_of_gt (coordinate_bounds k p).2
      · simp [inwardGate,hzero,hone,wholePolygon]
  exact ⟨⟨hpM,hgate 0⟩,hgate 1⟩

end ConcurrentGeometry
end InwardMargins

end SimpleAmenable
end
end

end OAI
