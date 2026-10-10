import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.Supported
import OAI.GroupTheory.SimpleAmenable.CentralCovers.BooleanCoordinateGeneration
import OAI.GroupTheory.SimpleAmenable.Configurations.PointwisePolygonTables

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CoordinateProductPatterns

theorem generic_fixed_x {a : ℕ} (p : GenericSquare a) (l r : ℝ)
    (hl : 0 ≤ l) (hr : r ≤ 1) (hlr : l < r) :
    ∃ q : GenericSquare a, q.val.1 = p.val.1 ∧ q.val.2 ∈ Set.Ioo l r := by
  let x := p.val.1
  let t := Real.goldenRatio^a
  have ht : t ≠ 0 := ne_of_gt (pow_pos Real.goldenRatio_pos a)
  let S := Set.range ordinary ∪ Set.range (fun z : CutRing => ordinary z+t*x) ∪
    Set.range (fun z : CutRing => (x-ordinary z)/t)
  have hS : S.Countable := ((Set.countable_range ordinary).union
    (Set.countable_range _)).union (Set.countable_range _)
  obtain ⟨y,hy,hy'⟩ : ∃ y ∈ Set.Ioo l r, y ∉ S := by
    apply Set.not_subset.mp
    intro hh
    have := Cardinal.Real.Ioo_countable_iff.mp (hS.mono hh)
    linarith
  have hav : AvoidsCuts a (x,y) := by
    intro j z hz
    fin_cases j
    · exact p.property.2.2 0 z hz
    · exact hy' (Or.inl (Or.inl ⟨z,by simpa [cutForm] using hz.symm⟩))
    · apply hy'
      apply Or.inl ∘ Or.inr
      refine ⟨z,?_⟩
      change ordinary z+t*x=y
      change y-t*x=ordinary z at hz
      linarith
    · apply hy'
      apply Or.inr
      refine ⟨z,?_⟩
      apply (div_eq_iff ht).mpr
      change x-t*y=ordinary z at hz
      linarith
  exact ⟨⟨(x,y),p.property.1,⟨by linarith [hy.1],by linarith [hy.2]⟩,hav⟩,rfl,hy⟩

def genericSwap {a : ℕ} (p : GenericSquare a) : GenericSquare a :=
  ⟨p.val.swap,p.property.2.1,p.property.1,by
    intro j z
    fin_cases j
    · exact p.property.2.2 1 z
    · exact p.property.2.2 0 z
    · exact p.property.2.2 3 z
    · exact p.property.2.2 2 z⟩

theorem generic_fixed_y {a : ℕ} (p : GenericSquare a) (l r : ℝ)
    (hl : 0 ≤ l) (hr : r ≤ 1) (hlr : l < r) :
    ∃ q : GenericSquare a, q.val.2 = p.val.2 ∧ q.val.1 ∈ Set.Ioo l r := by
  obtain ⟨q,hq,hqr⟩ := generic_fixed_x (genericSwap p) l r hl hr hlr
  exact ⟨genericSwap q,hq,hqr⟩

theorem coordinate_patterns_product {a : ℕ} {ι : Type*} [Finite ι]
    (U : Fin 2 × ι → polygonAlgebra a)
    (hcoord : ∀ j i (p q : GenericSquare a), coordinate j p = coordinate j q →
      (p ∈ (U (j,i)).val ↔ q ∈ (U (j,i)).val))
    (σ : Fin 2 × ι → Bool)
    (hσ : ∀ j : Fin 2, (fun i => σ (j,i)) ∈ Set.range (polygonAssignment (fun i => U (j,i)))) :
    σ ∈ Set.range (polygonAssignment U) := by
  classical
  let V : Fin 2 → polygonAlgebra a := fun j =>
    ⟨{q | polygonAssignment (fun i => U (j,i)) q = fun i => σ (j,i)},
      polygonAssignment_fiber_mem _ _⟩
  have hV (j : Fin 2) : (V j).val.Nonempty := hσ j
  obtain ⟨l₀,r₀,hl₀,hlr₀,hr₀,hl₀',hlr₀',hr₀',hbox₀⟩ := polygon_contains_rectangle (V 0) (hV 0)
  obtain ⟨l₁,r₁,hl₁,hlr₁,hr₁,hl₁',hlr₁',hr₁',hbox₁⟩ := polygon_contains_rectangle (V 1) (hV 1)
  obtain ⟨p,hpx,hpy⟩ := generic_rectangle a (ordinary l₀.1) (ordinary r₀.1)
    (ordinary l₁.2) (ordinary r₁.2) hl₀.le hr₀.le hlr₀ hl₁'.le hr₁'.le hlr₁'
  obtain ⟨q₀,hq₀,hq₀y⟩ := generic_fixed_x p (ordinary l₀.2) (ordinary r₀.2) hl₀'.le hr₀'.le hlr₀'
  obtain ⟨q₁,hq₁,hq₁x⟩ := generic_fixed_y p (ordinary l₁.1) (ordinary r₁.1) hl₁.le hr₁.le hlr₁
  have hq₀mem := hbox₀ q₀ (by rwa [hq₀]) hq₀y
  have hq₁mem := hbox₁ q₁ hq₁x (by rwa [hq₁])
  refine ⟨p,?_⟩
  funext ⟨j,i⟩
  fin_cases j
  · have he := congrFun hq₀mem i
    change decide (p ∈ (U (0,i)).val) = _
    change decide (q₀ ∈ (U (0,i)).val) = _ at he
    rw [decide_eq_decide.mpr (hcoord 0 i p q₀ hq₀.symm)]
    exact he
  · have he := congrFun hq₁mem i
    change decide (p ∈ (U (1,i)).val) = _
    change decide (q₁ ∈ (U (1,i)).val) = _ at he
    rw [decide_eq_decide.mpr (hcoord 1 i p q₁ hq₁.symm)]
    exact he

end CoordinateProductPatterns

end SimpleAmenable
end
end

end OAI
