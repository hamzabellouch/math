import OAI.Geometry.SurfaceImmersion.Geometry.CurveIncidenceGraph

namespace OAI

/-! A finite graph of degrees one and two joins each degree-one vertex
to a distinct degree-one vertex by a simple path. -/
noncomputable section
open Set
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem degree_one_reaches_degree_one {A : Type*} [Fintype A]
    (G : SimpleGraph A) (hdegrees : ∀ x, G.degree x = 1 ∨ G.degree x = 2)
    (p : A) (hp : G.degree p = 1) :
    ∃ q : A, q ≠ p ∧ G.degree q = 1 ∧ Nonempty (G.Path p q) := by
  classical
  let C : Set A := {x | G.Reachable p x}
  let H := G.induce C
  let p' : C := ⟨p,SimpleGraph.Reachable.rfl⟩
  have hdegree (x : C) : H.degree x = G.degree x.val :=
    G.degree_induce_of_neighborSet_subset (fun _ hy => x.property.trans hy.reachable)
  have hodd : Odd (H.degree p') := by rw [hdegree,hp]; decide
  obtain ⟨q,hne,hq⟩ := H.exists_ne_odd_degree_of_exists_odd_degree p' hodd
  have hqp : q.val ≠ p := by
    intro he
    exact hne (Subtype.ext he)
  have hq1 : G.degree q.val = 1 := by
    rw [hdegree] at hq
    rcases hdegrees q.val with h | h
    · exact h
    · rw [h] at hq
      norm_num at hq
  obtain ⟨w,hw⟩ := q.property.exists_isPath
  exact ⟨q.val,hqp,hq1,⟨⟨w,hw⟩⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
