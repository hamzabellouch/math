import OAI.Geometry.SurfaceImmersion.Geometry.CurveEdgeLocalization
import OAI.Geometry.SurfaceImmersion.Geometry.InjectivePathConcatenation

namespace OAI

/-! A simple path in the interval incidence graph has an actual
embedded realization in the compact curve. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

structure RealizedCurveWalk {V : Set X} {P : Finset (Set X)} {a b : V}
    (p : (curveIncidenceGraph V P).Walk (Sum.inl a) (Sum.inl b)) where
  path : Path a.val b.val
  injective : a ≠ b → Function.Injective path
  vertex : ∀ v : V, v.val ∈ range path → Sum.inl v ∈ p.support
  edge : ∀ E : P, (range path ∩ E.val).Nonempty → Sum.inr E ∈ p.support

theorem realize_simple_curve_walk {V : Set X} {P : Finset (Set X)}
    (hP : ∀ E ∈ P, Disjoint E V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (w : ∀ E : P, CurveEdgeWitness V E.val)
    {a b : V} (p : (curveIncidenceGraph V P).Walk (Sum.inl a) (Sum.inl b))
    (hp : p.IsPath) : Nonempty (RealizedCurveWalk p) := by
  classical
  suffices ∀ n (a b : V) (p : (curveIncidenceGraph V P).Walk (Sum.inl a) (Sum.inl b)),
      p.length = n → p.IsPath → Nonempty (RealizedCurveWalk p) by
    exact this p.length a b p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b p hn hp
    cases p with
    | nil =>
      refine ⟨⟨Path.refl a.val,?_,?_,?_⟩⟩
      · intro h
        exact False.elim (h rfl)
      · rintro v ⟨t,ht⟩
        have hv : v = a := Subtype.ext ht.symm
        simp [hv]
      · rintro E ⟨x,⟨t,ht⟩,hxE⟩
        have hx : x = a.val := ht.symm
        exact False.elim (disjoint_left.mp (hP E.val E.property) hxE (hx ▸ a.property))
    | cons h p =>
      rename_i c
      cases c with
      | inl c => exact False.elim h
      | inr E =>
        cases p with
        | cons h' q =>
          rename_i c
          cases c with
          | inr F => exact False.elim h'
          | inl c =>
            obtain ⟨hp',haNot⟩ := (SimpleGraph.Walk.cons_isPath_iff _ _).mp hp
            obtain ⟨hq,hENot⟩ := (SimpleGraph.Walk.cons_isPath_iff _ _).mp hp'
            have hac : a ≠ c := by
              intro he
              apply haNot
              simp [he]
            obtain ⟨σ,hσ,hσrange⟩ := (w E).oriented_path (hP E.val E.property)
              a.property c.property (fun he => hac (Subtype.ext he)) h h'
            obtain ⟨hσV,hσE⟩ := curve_edge_path_localization hP hdis E (w E) a c hac h h' σ hσrange
            by_cases hcb : c = b
            · subst b
              refine ⟨⟨σ,fun _ => hσ,?_,?_⟩⟩
              · intro v hv
                rcases hσV v hv with he | he <;> simp [he]
              · intro F hF
                have he := hσE F hF
                simp [he]
            · have hqn : q.length < n := by
                simp only [SimpleGraph.Walk.length_cons] at hn
                omega
              obtain ⟨r⟩ := ih q.length hqn c b q rfl hq
              have hmeet : range σ ∩ range r.path ⊆ {c.val} := by
                rintro x ⟨hxσ,hxr⟩
                by_cases hxE : x ∈ E.val
                · exact False.elim (hENot (r.edge E ⟨x,hxr,hxE⟩))
                · have hfront : x ∈ closure E.val \ E.val := ⟨hσrange ▸ hxσ,hxE⟩
                  rw [curve_edge_frontier_endpoints (w E) (hP E.val E.property) a c hac h h'] at hfront
                  rcases hfront with he | he
                  · have ha : a.val ∈ range r.path := he ▸ hxr
                    exact False.elim (haNot (by simp [r.vertex a ha]))
                  · exact he
              refine ⟨⟨σ.trans r.path,fun _ => path_trans_injective_of_range σ r.path hσ
                (r.injective hcb) hmeet,?_,?_⟩⟩
              · intro v hv
                rw [Path.trans_range] at hv
                rcases hv with hv | hv
                · rcases hσV v hv with he | he <;> simp [he]
                · simp [r.vertex v hv]
              · intro F hF
                obtain ⟨x,hx,hxF⟩ := hF
                rw [Path.trans_range] at hx
                rcases hx with hx | hx
                · have he := hσE F ⟨x,hx,hxF⟩
                  simp [he]
                · simp [r.edge F ⟨x,hx,hxF⟩]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
