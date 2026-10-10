import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentAnchors
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LocalChartDecisions

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section VertexMargins

structure VertexMargin (z : ℝ × ℝ) (ε : ℝ) where
  lower : Fin 2 → CutRing
  upper : Fin 2 → CutRing
  lower_outer : ∀ j, realCoordinate z j-2*ε < ordinary (lower j)
  lower_inner : ∀ j, ordinary (lower j) < realCoordinate z j-ε
  upper_inner : ∀ j, realCoordinate z j+ε < ordinary (upper j)
  upper_outer : ∀ j, ordinary (upper j) < realCoordinate z j+2*ε

theorem vertexMargin_exists (z : ℝ × ℝ) {ε : ℝ} (hε : 0<ε) :
    Nonempty (VertexMargin z ε) := by
  choose L hL hL' using fun j : Fin 2 =>
    exists_cut_between (x := realCoordinate z j-2*ε) (y := realCoordinate z j-ε) (by linarith)
  choose V hV hV' using fun j : Fin 2 =>
    exists_cut_between (x := realCoordinate z j+ε) (y := realCoordinate z j+2*ε) (by linarith)
  exact ⟨⟨L,V,hL,hL',hV,hV'⟩⟩

theorem realCoordinate_dist_le (x y : ℝ × ℝ) (j : Fin 2) :
    |realCoordinate x j-realCoordinate y j| ≤ dist x y := by
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem realCoordinate_add (x y : ℝ × ℝ) (j : Fin 2) :
    realCoordinate (x+y) j=realCoordinate x j+realCoordinate y j := by
  fin_cases j <;> rfl

theorem realCoordinate_ordinary (u : CutRing × CutRing) (j : Fin 2) :
    realCoordinate (ordinary u.1,ordinary u.2) j=ordinary (pointCoordinate u j) := by
  fin_cases j <;> rfl

namespace VertexMargin
variable {z : ℝ × ℝ} {ε : ℝ} (V : VertexMargin z ε)

theorem width (_hε : 0<ε) (j : Fin 2) :
    ordinary (V.lower j)<ordinary (V.upper j) ∧
    ordinary (V.upper j)-ordinary (V.lower j)<4*ε := by
  have h₁ := V.lower_inner j
  have h₂ := V.upper_inner j
  have h₃ := V.lower_outer j
  have h₄ := V.upper_outer j
  constructor <;> linarith

theorem translated_inner (u : CutRing × CutRing) (x : ℝ × ℝ)
    (hx : dist x (z+(ordinary u.1,ordinary u.2))≤ε) (j : Fin 2) :
    ordinary (V.lower j+pointCoordinate u j)<realCoordinate x j ∧
    realCoordinate x j<ordinary (V.upper j+pointCoordinate u j) := by
  have hh := (abs_le.mp ((realCoordinate_dist_le x (z+(ordinary u.1,ordinary u.2)) j).trans hx))
  rw [realCoordinate_add,realCoordinate_ordinary] at hh
  rw [map_add,map_add]
  have h₁ := V.lower_inner j
  have h₂ := V.upper_inner j
  constructor <;> linarith

theorem translated_outer (u b : CutRing × CutRing) (x : ℝ × ℝ)
    (hb : dist (ordinary b.1,ordinary b.2) (z+(ordinary u.1,ordinary u.2))<ε)
    (hx : ∀ j, ordinary (V.lower j+pointCoordinate u j)≤realCoordinate x j ∧
      realCoordinate x j≤ordinary (V.upper j+pointCoordinate u j)) (j : Fin 2) :
    |realCoordinate x j-ordinary (pointCoordinate b j)|<3*ε := by
  have hh := (abs_lt.mp ((realCoordinate_dist_le (ordinary b.1,ordinary b.2)
      (z+(ordinary u.1,ordinary u.2)) j).trans_lt hb))
  rw [realCoordinate_add,realCoordinate_ordinary,realCoordinate_ordinary] at hh
  have hk := hx j
  rw [map_add,map_add] at hk
  have h₁ := V.lower_outer j
  have h₂ := V.upper_outer j
  apply abs_lt.mpr
  constructor <;> linarith

end VertexMargin

theorem finite_vertex_margins (D : ℕ) {ε : ℝ} (hε : 0<ε) :
    Nonempty (∀ t : VertexType D, VertexMargin (vertexRepresentative D t) ε) := by
  classical
  exact ⟨fun t => Classical.choice (vertexMargin_exists (vertexRepresentative D t) hε)⟩

end VertexMargins

end SimpleAmenable
end
end

end OAI
