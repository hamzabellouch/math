import OAI.Geometry.SurfaceImmersion.Geometry.EmbeddedCurveGraphPath
import OAI.Geometry.SurfaceImmersion.Geometry.CurveIncidenceBoundaryPair

namespace OAI

/-! An actual embedded interval joins two boundary points and has no
other boundary point in its interior. -/
noncomputable section
open Set Topology unitInterval
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem curve_boundary_embedded_arc (D V : Set X) (hDV : D ⊆ V) (hV : V.Finite)
    (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E) (hwitness : ∀ E ∈ P, Nonempty (CurveEdgeWitness V E))
    (hline : ∀ p ∉ D, ∃ c : OpenPartialHomeomorph X ℝ, p ∈ c.source)
    (hhalf : ∀ p ∈ D, ∃ c : OpenPartialHomeomorph X (Ici (0:ℝ)),
      p ∈ c.source ∧ c p = ⟨0,by simp⟩)
    (p : D) : ∃ q : D, q ≠ p ∧ ∃ γ : Path p.val q.val, IsClosedEmbedding γ ∧
      ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∉ D := by
  classical
  let : Fintype V := hV.fintype
  let G := curveIncidenceGraph V P
  let a : V := ⟨p.val,hDV p.property⟩
  obtain ⟨q,hqp,⟨r⟩⟩ := curve_boundary_pair D V hDV hV P hP hdis hcover hwitness hline hhalf p
  let b : V := ⟨q.val,hDV q.property⟩
  let w (E : P) := Classical.choice (hwitness E.val E.property)
  obtain ⟨ρ⟩ := realize_simple_curve_walk (fun E hE => (hP E hE).2.1) hdis w r.val r.property
  have hab : a ≠ b := by
    intro he
    exact hqp (Subtype.ext (congrArg (fun v : V => v.val) he).symm)
  have hρ := ρ.injective hab
  obtain ⟨hl,_⟩ := curve_incidence_degrees D V hV P hP hdis hcover hwitness hline hhalf
  refine ⟨q,hqp,ρ.path,ρ.path.continuous.isClosedEmbedding hρ,?_⟩
  intro t ht0 ht1 htD
  let v : V := ⟨ρ.path t,hDV htD⟩
  have hva : v ≠ a := by
    intro he
    have hx : ρ.path t = ρ.path 0 := by simpa using congrArg (fun v : V => v.val) he
    have ht : (t:ℝ) = 0 := congrArg (fun t : I => (t:ℝ)) (hρ hx)
    linarith
  have hvb : v ≠ b := by
    intro he
    have hx : ρ.path t = ρ.path 1 := by simpa using congrArg (fun v : V => v.val) he
    have ht : (t:ℝ) = 1 := congrArg (fun t : I => (t:ℝ)) (hρ hx)
    linarith
  have hdeg : G.degree (Sum.inl v) = 1 := by
    rw [hl]
    change (if ρ.path t ∈ D then 1 else 2) = 1
    simp only [htD,↓reduceIte]
  obtain ⟨z,hz,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  have hsub : (G.neighborSet (Sum.inl v)).Subsingleton := by
    intro x hx y hy
    exact (hunique x hx).trans (hunique y hy).symm
  have hnot := r.property.isTrail.not_mem_support_of_subsingleton_neighborSet
    (fun he => hva (Sum.inl.inj he)) (fun he => hvb (Sum.inl.inj he)) hsub
  exact hnot (ρ.vertex v (mem_range_self t))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
