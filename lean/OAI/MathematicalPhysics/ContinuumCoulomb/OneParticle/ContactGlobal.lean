import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactMediatorLinks
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactSourceGrid
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceMatrix

namespace OAI

/-! Gluing the independently adjusted nineteen-link gadgets along the
actual original lattice vertices. All fresh sites retain their source-edge
label under the explicit final-graph permutation. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

abbrev GlobalSite (d : SquareLatticeHeisenberg) :=
  Fin (d.vertices + d.edges * 2 + d.edges * 2 * 2 + (d.edges * 2 + d.edges * 2 * 2) * 2)

abbrev GlobalEdge (d : SquareLatticeHeisenberg) :=
  Fin (d.edges + ((d.edges * 2 + d.edges * 2 * 2) + (d.edges * 2 + d.edges * 2 * 2) * 2))

def joinedPosition (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint) :
    Fin d.vertices ⊕ (Fin d.edges × LocalInternal) → ContactPoint
  | Sum.inl i => contactGridPoint (d.coordinate i)
  | Sum.inr (e, u) => (d.contactEdge e).place (P e (Sum.inr u))

def globalPosition (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint) (i : GlobalSite d) : ContactPoint :=
  joinedPosition d P ((siteEquiv d.vertices d.edges).symm i)

@[simp] theorem globalPosition_old (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint) (i : Fin d.vertices) :
    globalPosition d P (siteEquiv d.vertices d.edges (Sum.inl i)) =
      contactGridPoint (d.coordinate i) := by
  simp [globalPosition, joinedPosition]

@[simp] theorem globalPosition_internal (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint) (e : Fin d.edges) (u : LocalInternal) :
    globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u))) =
      (d.contactEdge e).place (P e (Sum.inr u)) := by
  simp [globalPosition, joinedPosition]

/-- Anchoring a local gadget at zero and seventeen makes its two old
vertices agree with the unique global positions of the original spins. -/
theorem globalPosition_local (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (h₀ : ∀ e, P e (localOld 0) = contactPoint 0 0)
    (h₁ : ∀ e, P e (localOld 1) = contactPoint 17 0)
    (e : Fin d.edges) (x : LocalSite) :
    globalPosition d P (localVertex (d.left e) (d.right e) e x) =
      (d.contactEdge e).place (P e x) := by
  cases x with
  | inl s =>
    fin_cases s
    · change globalPosition d P (siteEquiv d.vertices d.edges (Sum.inl (d.left e))) =
        (d.contactEdge e).place (P e (localOld 0))
      rw [globalPosition_old, h₀ e, ContactGridEdge.place_zero, d.contactEdge_left]
    · change globalPosition d P (siteEquiv d.vertices d.edges (Sum.inl (d.right e))) =
        (d.contactEdge e).place (P e (localOld 1))
      rw [globalPosition_old, h₁ e, ContactGridEdge.place_end, d.contactEdge_right]
  | inr u => simp [localVertex]

/-- The exact edge lengths of the local gadgets are the lengths of every
edge in the actual final mediator enumeration. -/
theorem globalPosition_link_lengths (d : SquareLatticeHeisenberg) (W G : ℕ)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (h₀ : ∀ e, P e (localOld 0) = contactPoint 0 0)
    (h₁ : ∀ e, P e (localOld 1) = contactPoint 17 0)
    (ℓ : GlobalEdge d → ℝ)
    (hℓ : ∀ e a, dist (P e (localLeft (member (d.coefficient e)) a))
      (P e (localRight a)) = ℓ (encodeEdge d.edges e a)) (a : GlobalEdge d) :
    dist (globalPosition d P ((finalGraph d.bonds W G).left a))
      (globalPosition d P ((finalGraph d.bonds W G).right a)) = ℓ a := by
  obtain ⟨⟨e, a⟩, rfl⟩ := (edgeEquiv d.edges).surjective a
  change dist (globalPosition d P ((finalGraph d.bonds W G).left (encodeEdge d.edges e a)))
    (globalPosition d P ((finalGraph d.bonds W G).right (encodeEdge d.edges e a))) = _
  rw [finalGraph_left, finalGraph_right]
  change dist (globalPosition d P (localVertex (d.left e) (d.right e) e
      (localLeft (member (d.coefficient e)) a)))
    (globalPosition d P (localVertex (d.left e) (d.right e) e (localRight a))) = _
  rw [globalPosition_local d P h₀ h₁, globalPosition_local d P h₀ h₁,
    ContactGridEdge.place_dist]
  exact hℓ e a

/-- The independent local adjustments stay close to points in the exact
canonical strip belonging to their original source edge. -/
theorem globalPosition_internal_near_strip (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (hP : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20)
    (e : Fin d.edges) (u : LocalInternal) :
    ∃ p : ContactStripSite, dist ((d.contactEdge e).place
      (contactPoint p.axial p.transverse))
      (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u)))) < 1 / 20 := by
  have hleft : localToContact (Sum.inr u) ≠ Sum.inl 0 := by
    intro h
    have heq := congrArg contactToLocal h
    rw [contact_local_inverse] at heq
    simp only [contactToLocal, Matrix.cons_val_zero, localOld, reduceCtorEq] at heq
  have hright : localToContact (Sum.inr u) ≠
      contactGadgetRightNode (edgeNegative d.bonds e) 9 := by
    intro h
    have heq := congrArg contactToLocal h
    rw [contact_local_inverse] at heq
    cases hn : edgeNegative d.bonds e <;>
      simp [contactToLocal, contactGadgetRightNode, localOld] at heq
  obtain ⟨p, hp⟩ := contactBaseGadget_internal_strip (edgeNegative d.bonds e)
    (localToContact (Sum.inr u)) hleft hright
  refine ⟨p, ?_⟩
  rw [globalPosition_internal, ContactGridEdge.place_dist, ← hp, dist_comm]
  exact hP e (Sum.inr u)

/-- All fresh sites belonging to distinct original edges have the fixed
nonedge margin, uniformly in the size of the original lattice graph. -/
theorem globalPosition_distinct_gadgets (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (hP : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20)
    (e f : Fin d.edges) (hef : e ≠ f) (u v : LocalInternal) :
    6 / 5 < dist (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u))))
      (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (f, v)))) := by
  obtain ⟨p, hp⟩ := globalPosition_internal_near_strip d P hP e u
  obtain ⟨q, hq⟩ := globalPosition_internal_near_strip d P hP f v
  exact ContactGridEdge.distinct_perturbed_separation (d.contactEdge e) (d.contactEdge f)
    (fun h => hef (d.contactEdge_key_injective h)) p q _ _ hp.le hq.le

/-- A nonincident original spin is separated from every fresh site of a
gadget, including after its independent contact-length adjustment. -/
theorem globalPosition_nonincident (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (hP : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20)
    (i : Fin d.vertices) (e : Fin d.edges) (hi₀ : i ≠ d.left e) (hi₁ : i ≠ d.right e)
    (u : LocalInternal) :
    6 / 5 < dist (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u))))
      (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inl i))) := by
  obtain ⟨p, hp⟩ := globalPosition_internal_near_strip d P hP e u
  have hs := ContactGridEdge.external_vertex_separation (d.contactEdge e) (d.coordinate i)
    (by simpa using fun h => hi₀ (d.coordinate_injective h))
    (by simpa using fun h => hi₁ (d.coordinate_injective h)) p
  rw [globalPosition_old]
  have ht := dist_triangle ((d.contactEdge e).place (contactPoint p.axial p.transverse))
    (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u))))
    (contactGridPoint (d.coordinate i))
  linarith

end ContinuumCoulomb.ContactMediator

end

end OAI
