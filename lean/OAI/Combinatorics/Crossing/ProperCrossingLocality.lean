import OAI.Combinatorics.Crossing.DrawingDefinition
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem chart_image_mem_iff (e : OpenPartialHomeomorph Plane Plane) (A L : Set Plane)
    (h : e '' (e.source ∩ A)=e.target ∩ L) (x : Plane) (hx : x ∈ e.source) :
    x ∈ A ↔ e x ∈ L := by
  constructor
  · intro ha
    have hh : e x ∈ e '' (e.source ∩ A) := ⟨x,⟨hx,ha⟩,rfl⟩
    rw [h] at hh
    exact hh.2
  · intro hl
    have hh : e x ∈ e '' (e.source ∩ A) := h.symm ▸ ⟨e.map_source hx,hl⟩
    obtain ⟨y,hy,he⟩ := hh
    have hyx : y=x := e.injOn hy.1 hx he
    exact hyx ▸ hy.2

theorem chart_restr_image_of_local_eq (e : OpenPartialHomeomorph Plane Plane)
    (A A' L U : Set Plane) (hU : IsOpen U) (hA : ∀ x ∈ U, x ∈ A ↔ x ∈ A')
    (h : e '' (e.source ∩ A)=e.target ∩ L) :
    (e.restrOpen U hU) '' ((e.restrOpen U hU).source ∩ A')=(e.restrOpen U hU).target ∩ L := by
  let f := e.restrOpen U hU
  apply Set.Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    have hs : x ∈ e.source ∩ U := hx.1
    exact ⟨f.map_source hx.1,(chart_image_mem_iff e A L h x hs.1).mp ((hA x hs.2).mpr hx.2)⟩
  · rintro y ⟨hy,hl⟩
    have hs : f.symm y ∈ f.source := f.map_target hy
    have hs' : f.symm y ∈ e.source ∩ U := hs
    have he : e (f.symm y)=y := f.right_inv hy
    have ha : f.symm y ∈ A := (chart_image_mem_iff e A L h _ hs'.1).mpr (he.symm ▸ hl)
    exact ⟨f.symm y,⟨hs,(hA _ hs'.2).mp ha⟩,f.right_inv hy⟩

theorem properCrossing_of_local_eq (A B A' B' : Set Plane) (x : Plane)
    (h : ProperCrossing A B x) (U : Set Plane) (hU : IsOpen U) (hx : x ∈ U)
    (hA : ∀ z ∈ U, z ∈ A ↔ z ∈ A') (hB : ∀ z ∈ U, z ∈ B ↔ z ∈ B') :
    ProperCrossing A' B' x := by
  obtain ⟨e,hs,he,hEA,hEB⟩ := h
  refine ⟨e.restrOpen U hU,⟨hs,hx⟩,he,?_,?_⟩
  · exact chart_restr_image_of_local_eq e A A' {y | y.2=0} U hU hA hEA
  · exact chart_restr_image_of_local_eq e B B' {y | y.1=0} U hU hB hEB

end Zarankiewicz

end

end OAI
