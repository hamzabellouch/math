import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryDegreeOne
import OAI.Geometry.SurfaceImmersion.Geometry.OrdinaryDegreeTwo
import OAI.Geometry.SurfaceImmersion.Geometry.DegreeOneReachability

namespace OAI

/-! Every boundary point of a compact curve is connected to a different
boundary point in its actual finite interval incidence graph. -/
noncomputable section
open Set Topology
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem curve_incidence_degrees (D V : Set X) (hV : V.Finite) (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E) (hwitness : ∀ E ∈ P, Nonempty (CurveEdgeWitness V E))
    (hline : ∀ p ∉ D, ∃ c : OpenPartialHomeomorph X ℝ, p ∈ c.source)
    (hhalf : ∀ p ∈ D, ∃ c : OpenPartialHomeomorph X (Ici (0:ℝ)),
      p ∈ c.source ∧ c p = ⟨0,by simp⟩) [Fintype V] :
    (∀ p : V, (curveIncidenceGraph V P).degree (Sum.inl p) = if p.val ∈ D then 1 else 2) ∧
    (∀ E : P, (curveIncidenceGraph V P).degree (Sum.inr E) = 2) := by
  constructor
  · intro p
    by_cases hp : p.val ∈ D
    · simp only [hp, ↓reduceIte]
      obtain ⟨c,hc,hc0⟩ := hhalf p.val hp
      exact curveIncidenceGraph_degree_left_one V P p
        (boundary_vertex_degree_one V hV P hP hdis hcover p.property c hc hc0)
    · simp only [hp, ↓reduceIte]
      obtain ⟨c,hc⟩ := hline p.val hp
      exact curveIncidenceGraph_degree_left_two V P p
        (ordinary_vertex_degree_two V hV P hP hdis hcover hwitness p.property c hc)
  · intro E
    exact curveIncidenceGraph_degree_right_two V P E (hP E.val E.property).2.1
      (Classical.choice (hwitness E.val E.property))

theorem curve_boundary_pair (D V : Set X) (hDV : D ⊆ V) (hV : V.Finite)
    (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E) (hwitness : ∀ E ∈ P, Nonempty (CurveEdgeWitness V E))
    (hline : ∀ p ∉ D, ∃ c : OpenPartialHomeomorph X ℝ, p ∈ c.source)
    (hhalf : ∀ p ∈ D, ∃ c : OpenPartialHomeomorph X (Ici (0:ℝ)),
      p ∈ c.source ∧ c p = ⟨0,by simp⟩)
    (p : D) : ∃ (q : D), q ≠ p ∧ Nonempty
      ((curveIncidenceGraph V P).Path (Sum.inl ⟨p.val,hDV p.property⟩)
        (Sum.inl ⟨q.val,hDV q.property⟩)) := by
  let : Fintype V := hV.fintype
  let G := curveIncidenceGraph V P
  obtain ⟨hl,hr⟩ := curve_incidence_degrees D V hV P hP hdis hcover hwitness hline hhalf
  have hdegrees : ∀ x, G.degree x = 1 ∨ G.degree x = 2 := by
    rintro (v|E)
    · rw [hl]
      split_ifs <;> simp
    · exact Or.inr (hr E)
  have hp : G.degree (Sum.inl ⟨p.val,hDV p.property⟩) = 1 := by
    rw [hl]
    simp only [p.property, ↓reduceIte]
  obtain ⟨q,hqp,hq,hpath⟩ := degree_one_reaches_degree_one G hdegrees
    (Sum.inl ⟨p.val,hDV p.property⟩) hp
  cases q with
  | inr E => rw [hr] at hq; norm_num at hq
  | inl v =>
    have hvD : v.val ∈ D := by
      rw [hl] at hq
      by_contra hn
      simp only [hn, ↓reduceIte] at hq
      norm_num at hq
    refine ⟨⟨v.val,hvD⟩,?_,hpath⟩
    intro he
    exact hqp (congrArg Sum.inl (Subtype.ext (congrArg (fun z : D => z.val) he)))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
