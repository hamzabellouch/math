import OAI.Combinatorics.BalancedRyser.Deletion.DeletionFieldTransport
import OAI.Combinatorics.BalancedRyser.Incidence.CorePencil

namespace OAI

noncomputable section

namespace Balanced.FieldTransport

variable {F G : Type*} [Field F] [Field G]

def projectivePointEquiv (e : F ≃+* G) : ProjectivePoint F ≃ ProjectivePoint G :=
  Equiv.sumCongr (pointEquiv e) (directionEquiv e)

@[simp] theorem throughProjective_transport (e : F ≃+* G)
    (l : Line F) (P : ProjectivePoint F) :
    ThroughProjective (lineEquiv e l) (projectivePointEquiv e P) ↔
      ThroughProjective l P := by
  cases P with
  | inl p => exact onLine_transport e p l
  | inr d =>
      change directionEquiv e l.1 = directionEquiv e d ↔ l.1 = d
      exact (directionEquiv e).injective.eq_iff

variable [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]

omit [Fintype F] [Fintype G] in

@[simp] theorem pencilSize_transport (e : F ≃+* G)
    (C : Finset (Line F)) (P : ProjectivePoint F) :
    pencilSize (mapLines e C) (projectivePointEquiv e P) = pencilSize C P := by
  rw [pencilSize, mapLines, Finset.filter_map, Finset.card_map]
  congr 1
  ext l
  simp

@[simp] theorem uncoveredPoints_transport (e : F ≃+* G)
    (D : Finset (Line F)) :
    uncoveredPoints (mapLines e D) = mapPoints e (uncoveredPoints D) :=
  uncoveredBy_transport e D

theorem corePencilEvent_map (e : F ≃+* G) (D : Finset (Line F)) (ζ : ℝ)
    (h : CorePencilEvent ζ D) : CorePencilEvent ζ (mapLines e D) := by
  intro C hdisj hsize hcover
  have hsurj : Function.Surjective (mapLines e) := by
    intro C
    exact ⟨mapLines e.symm C, mapLines_symm e.symm C⟩
  obtain ⟨C, rfl⟩ := hsurj C
  have hdisj' : Disjoint C D := (disjoint_mapLines e C D).mp hdisj
  have hsize' : C.card ≤ Fintype.card F := by
    simpa only [card_mapLines, cardinal_field e] using hsize
  have hcover' : CoversPoints C (uncoveredPoints D) := by
    rw [uncoveredPoints_transport, coversPoints_transport] at hcover
    exact hcover
  obtain ⟨P, hP⟩ := h C hdisj' hsize' hcover'
  refine ⟨projectivePointEquiv e P, ?_⟩
  simpa only [pencilSize_transport, cardinal_field e] using hP

@[simp] theorem corePencilEvent_transport (e : F ≃+* G)
    (D : Finset (Line F)) (ζ : ℝ) :
    CorePencilEvent ζ (mapLines e D) ↔ CorePencilEvent ζ D := by
  constructor
  · intro h
    simpa only [mapLines_symm] using corePencilEvent_map e.symm (mapLines e D) ζ h
  · exact corePencilEvent_map e D ζ

theorem core_pencil_failure_probability_transport (e : F ≃+* G) {k : ℕ}
    (Q : PMF (DeletionSet F k)) (ζ : ℝ) :
    deletionEventProbability (mapLaw e Q) (fun D => ¬ CorePencilEvent ζ D.val) =
      deletionEventProbability Q (fun D => ¬ CorePencilEvent ζ D.val) := by
  rw [deletionEventProbability_mapLaw]
  simp only [deletionEquiv_val, corePencilEvent_transport]

theorem same_order_core_pencil_transport
    (hcard : Fintype.card F = Fintype.card G) {k : ℕ}
    (Q : PMF (DeletionSet F k)) :
    ∃ Q' : PMF (DeletionSet G k),
      (∀ K : ℝ, DeletionDominated k K Q' ↔ DeletionDominated k K Q) ∧
      ∀ ζ : ℝ,
        deletionEventProbability Q' (fun D => ¬ CorePencilEvent ζ D.val) =
          deletionEventProbability Q (fun D => ¬ CorePencilEvent ζ D.val) := by
  let e : F ≃+* G := FiniteField.ringEquivOfCardEq hcard
  exact ⟨mapLaw e Q, deletionDominated_transport e Q,
    core_pencil_failure_probability_transport e Q⟩

end Balanced.FieldTransport

end

end OAI
