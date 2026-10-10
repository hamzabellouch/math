import Mathlib
import OAI.Combinatorics.HoneycombCorridor.Incidence
import OAI.Combinatorics.HoneycombCorridor.Curvature

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def SimplePolygonTurning : Prop := ∀ (g : Germ) (w : List Bool),
  w ≠ [] → (traced g w).Nodup → terminalGerm g w = g →
    turnUnits w = 6 ∨ turnUnits w = -6

theorem simple_polygon_signed_turn (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (ε : ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (hpne : p ≠ 0) (hε : ε = 1 ∨ ε = -1)
    (hvals : ∀ a, p a = 0 ∨ p a = ε) : ε * turnUnits w = 6 := by
  have hEuler := simple_cycle_cell_euler g w hne hN hc p hp hpne
  have hw := simple_closed_word_contour g w hN hc
  have hsub : (traced g w).toFinset ⊆ cellVertices p.support := by
    intro v hv
    exact (contour_flat_trace p (wordFlow g w) hp (fun _ => 0)
      (by intros; rfl) g w hw v (List.mem_toFinset.mp hv)).1
  have hsum : (∑ v ∈ cellVertices p.support,cellCurvature p.support v) = ε * turnUnits w := by
    calc
      _ = ∑ v ∈ (traced g w).toFinset,cellCurvature p.support v := by
        symm
        apply Finset.sum_subset hsub
        intro v hv hnot
        exact nonboundary_cellCurvature g w hc p hp v hv
          (by simpa only [List.mem_toFinset] using hnot)
      _ = ((traced g w).map (cellCurvature p.support)).sum := List.sum_toFinset _ hN
      _ = _ := contour_curvature_sum p ε hε hvals (wordFlow g w) hp g w hw
  rw [sum_cellCurvature,hEuler,mul_one] at hsum
  exact hsum.symm

theorem simple_polygon_turning : SimplePolygonTurning := by
  intro g w hne hN hc
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator g w hne hN hc
  have hsum := simple_polygon_signed_turn g w hne hN hc p ε hp hpne hε hvals
  rcases hε with rfl | rfl
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)


def IsPolygon (E : Finset EdgeIndex) : Prop := ∃ (g : Germ) (w : List Bool),
  w ≠ [] ∧ (traced g w).Nodup ∧ terminalGerm g w = g ∧ (wordFlow g w).support = E

abbrev Polygon := { E : Finset EdgeIndex // IsPolygon E }

namespace Polygon
noncomputable def germ (P : Polygon) : Germ := P.property.choose
noncomputable def turns (P : Polygon) : List Bool := P.property.choose_spec.choose

theorem traversal (P : Polygon) :
    P.turns ≠ [] ∧ (traced P.germ P.turns).Nodup ∧
    terminalGerm P.germ P.turns = P.germ ∧ (wordFlow P.germ P.turns).support = P.val :=
  P.property.choose_spec.choose_spec

theorem has_indicator (P : Polygon) :
    ∃ (p : FaceIndex →₀ ℤ) (ε : ℤ), RepresentsFlow p (wordFlow P.germ P.turns) ∧
      p ≠ 0 ∧ (ε = 1 ∨ ε = -1) ∧ ∀ a, p a = 0 ∨ p a = ε :=
  simple_closed_word_indicator P.germ P.turns P.traversal.1 P.traversal.2.1 P.traversal.2.2.1

noncomputable def potential (P : Polygon) : FaceIndex →₀ ℤ := P.has_indicator.choose
noncomputable def orientation (P : Polygon) : ℤ := P.has_indicator.choose_spec.choose

theorem potential_spec (P : Polygon) :
    RepresentsFlow P.potential (wordFlow P.germ P.turns) ∧ P.potential ≠ 0 ∧
    (P.orientation = 1 ∨ P.orientation = -1) ∧
    ∀ a, P.potential a = 0 ∨ P.potential a = P.orientation :=
  P.has_indicator.choose_spec.choose_spec

noncomputable def interiorFaces (P : Polygon) : Finset FaceIndex := P.potential.support

def vertices (P : Polygon) : Finset Vertex := P.val.biUnion fun e => {upEnd e,downEnd e}

noncomputable def interior (P : Polygon) : Finset Vertex :=
  cellVertices P.interiorFaces \ P.vertices

def length (P : Polygon) : ℕ := P.val.card

noncomputable def ccwTurn (P : Polygon) (v : Vertex) : ℝ :=
  Real.pi / 3 * (3 - 2 * (faceCount P.interiorFaces v : ℝ))
end Polygon

noncomputable def inducedEdges (D : Finset Vertex) : Finset EdgeIndex := by
  classical
  exact ((D.product Finset.univ).image edgeOf).filter fun e => upEnd e ∈ D ∧ downEnd e ∈ D

noncomputable def polygons (D : Finset Vertex) : Finset Polygon := by
  classical
  exact (inducedEdges D).powerset.subtype IsPolygon

def Filled (D : Finset Vertex) : Prop := ∀ P ∈ polygons D, P.interior ⊆ D

noncomputable def visitMass (D : Finset Vertex) (v : Vertex) : ℝ := (visitSum D v).re

noncomputable def excursionMass (D : Finset Vertex) (v : Vertex) : ℝ := by
  classical
  exact ∑ e ∈ excursions D, if v ∈ traced e.1 e.2 then criticalActivity ^ e.2.length else 0

noncomputable def polygonSystems (D : Finset Vertex) (f : FaceIndex) :
    Finset (Finset Polygon) := by
  classical
  exact (polygons D).powerset.filter fun S =>
    (S : Set Polygon).Pairwise (fun P Q => Disjoint P.vertices Q.vertices) ∧
    ∀ P ∈ S, f ∈ P.interiorFaces

noncomputable def faceNestingMass (D : Finset Vertex) (f : FaceIndex) : ℝ :=
  ∑ S ∈ polygonSystems D f, ∏ P ∈ S, 2 * criticalActivity ^ P.length

noncomputable def tilingCoordinate (k : Fin 3) (z : ℝ × ℝ) : ℝ :=
  if k = 0 then 2 * z.2 / Real.sqrt 3
  else if k = 1 then z.1 - z.2 / Real.sqrt 3 + 1 / 2
  else z.1 + z.2 / Real.sqrt 3 + 1 / 2

def AdmissiblyConvex (D : Finset Vertex) : Prop :=
  ∃ lo hi : Fin 3 → ℤ, ∀ v : Vertex, v ∈ D ↔ ∀ k : Fin 3,
    (lo k : ℝ) < tilingCoordinate k (position v) ∧
    tilingCoordinate k (position v) < (hi k : ℝ)

def FiniteVisitRecursion : Prop := ∀ (D : Finset Vertex) (v : Vertex), Filled D → v ∈ D →
  visitMass D v = 3 +
    (∑ P ∈ polygons D, if v ∈ P.vertices then
      2 * criticalActivity ^ (P.length - 1) *
        (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v))) else 0) +
    (∑ P ∈ polygons D, if v ∈ P.interior then
      2 * criticalActivity ^ P.length * visitMass P.interior v else 0)

def FiniteVisitsTheorem : Prop := FiniteVisitRecursion ∧
  (∀ P : Polygon, 0 < 2 * criticalActivity ^ P.length ∧
    ∀ v ∈ P.vertices, 0 < 2 * criticalActivity ^ (P.length - 1) *
      (-Real.cos ((3 / 8 : ℝ) * (2 * Real.pi - P.ccwTurn v)))) ∧
  (∀ D v, Filled D → v ∈ D → 3 ≤ visitMass D v) ∧
  (∀ D E v, Filled D → Filled E → D ⊆ E → v ∈ D → visitMass D v ≤ visitMass E v) ∧
  (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ D v, Filled D → v ∈ D →
    c * (∑ k : Fin 3, faceNestingMass D (leftFace (v,k))) ≤ visitMass D v ∧
    visitMass D v ≤ C * (∑ k : Fin 3, faceNestingMass D (leftFace (v,k)))) ∧
  (∀ D v, AdmissiblyConvex D → v ∈ D →
    Real.cos (3 * Real.pi / 8) * excursionMass D v ≤ visitMass D v ∧
    visitMass D v ≤ excursionMass D v)

end PolynomialVacuumBridge.Corridor

end

end OAI
