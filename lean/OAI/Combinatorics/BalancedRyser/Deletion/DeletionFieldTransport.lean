import Mathlib
import OAI.Combinatorics.BalancedRyser.Deletion.Deletion

namespace OAI

noncomputable section

namespace Balanced.FieldTransport

variable {F G : Type*} [Field F] [Field G]

def pointEquiv (e : F ≃+* G) : Point F ≃ Point G :=
  Equiv.prodCongr e.toEquiv e.toEquiv

def directionEquiv (e : F ≃+* G) : Direction F ≃ Direction G :=
  Equiv.optionCongr e.toEquiv

def lineEquiv (e : F ≃+* G) : Line F ≃ Line G :=
  Equiv.prodCongr (directionEquiv e) e.toEquiv

@[simp] theorem lineEquiv_fst (e : F ≃+* G) (l : Line F) :
    (lineEquiv e l).1 = directionEquiv e l.1 := rfl

@[simp] theorem lineEquiv_snd (e : F ≃+* G) (l : Line F) :
    (lineEquiv e l).2 = e l.2 := rfl

@[simp] theorem lineEval_transport (e : F ≃+* G) (d : Direction F) (p : Point F) :
    lineEval (directionEquiv e d) (pointEquiv e p) = e (lineEval d p) := by
  cases d <;> simp [directionEquiv, pointEquiv, lineEval]

@[simp] theorem onLine_transport (e : F ≃+* G) (p : Point F) (l : Line F) :
    OnLine (pointEquiv e p) (lineEquiv e l) ↔ OnLine p l := by
  simp [OnLine]

variable [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]

def mapLines (e : F ≃+* G) (D : Finset (Line F)) : Finset (Line G) :=
  D.map (lineEquiv e).toEmbedding

def mapPoints (e : F ≃+* G) (U : Finset (Point F)) : Finset (Point G) :=
  U.map (pointEquiv e).toEmbedding

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G] in
@[simp] theorem card_mapLines (e : F ≃+* G) (D : Finset (Line F)) :
    (mapLines e D).card = D.card := Finset.card_map _

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G] in
@[simp] theorem card_mapPoints (e : F ≃+* G) (U : Finset (Point F)) :
    (mapPoints e U).card = U.card := Finset.card_map _

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G] in
@[simp] theorem mem_mapLines (e : F ≃+* G) (D : Finset (Line F)) (l : Line F) :
    lineEquiv e l ∈ mapLines e D ↔ l ∈ D := by simp [mapLines]

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G] in
@[simp] theorem mem_mapPoints (e : F ≃+* G) (U : Finset (Point F)) (p : Point F) :
    pointEquiv e p ∈ mapPoints e U ↔ p ∈ U := by simp [mapPoints]

omit [DecidableEq F] [DecidableEq G] in
@[simp] theorem cardinal_field (e : F ≃+* G) : Fintype.card G = Fintype.card F :=
  (Fintype.card_congr e.toEquiv).symm

omit [Fintype F] [Fintype G] in
theorem direction_fiber_card (e : F ≃+* G) (D : Finset (Line F))
    (d : Direction F) :
    ((mapLines e D).filter fun l => l.1 = directionEquiv e d).card =
      (D.filter fun l => l.1 = d).card := by
  rw [mapLines, Finset.filter_map, Finset.card_map]
  congr 1
  ext l
  simp

omit [Fintype F] [Fintype G] in
@[simp] theorem isDeletionSet_transport (e : F ≃+* G) (D : Finset (Line F)) (k : ℕ) :
    IsDeletionSet k (mapLines e D) ↔ IsDeletionSet k D := by
  constructor
  · intro h d
    simpa only [direction_fiber_card] using h (directionEquiv e d)
  · intro h d
    obtain ⟨d, rfl⟩ := (directionEquiv e).surjective d
    simpa only [direction_fiber_card] using h d

omit [Fintype F] [Fintype G] in
@[simp] theorem deletionMultiplicity_transport (e : F ≃+* G)
    (D : Finset (Line F)) (p : Point F) :
    deletionMultiplicity (mapLines e D) (pointEquiv e p) = deletionMultiplicity D p := by
  rw [deletionMultiplicity, mapLines, Finset.filter_map, Finset.card_map]
  congr 1
  ext l
  simp

@[simp] theorem uncovered_mem_transport (e : F ≃+* G)
    (D : Finset (Line F)) (p : Point F) :
    pointEquiv e p ∈ uncoveredBy (mapLines e D) ↔ p ∈ uncoveredBy D := by
  simp only [uncoveredBy, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h l hl hon
    exact h (lineEquiv e l) ((mem_mapLines e D l).2 hl)
      ((onLine_transport e p l).2 hon)
  · intro h l hl hon
    obtain ⟨l, rfl⟩ := (lineEquiv e).surjective l
    exact h l ((mem_mapLines e D l).1 hl) ((onLine_transport e p l).1 hon)

@[simp] theorem uncoveredBy_transport (e : F ≃+* G) (D : Finset (Line F)) :
    uncoveredBy (mapLines e D) = mapPoints e (uncoveredBy D) := by
  ext p
  obtain ⟨p, rfl⟩ := (pointEquiv e).surjective p
  simp

@[simp] theorem linePoints_transport (e : F ≃+* G) (l : Line F) :
    linePoints (lineEquiv e l) = mapPoints e (linePoints l) := by
  ext p
  obtain ⟨p, rfl⟩ := (pointEquiv e).surjective p
  simp [linePoints]

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G] in
@[simp] theorem lineEquiv_symm (e : F ≃+* G) :
    lineEquiv e.symm = (lineEquiv e).symm := rfl

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G] in
@[simp] theorem pointEquiv_symm (e : F ≃+* G) :
    pointEquiv e.symm = (pointEquiv e).symm := rfl

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G] in
@[simp] theorem mapLines_symm (e : F ≃+* G) (D : Finset (Line F)) :
    mapLines e.symm (mapLines e D) = D := by
  ext l
  simp [mapLines]

def deletionEquiv (e : F ≃+* G) (k : ℕ) : DeletionSet F k ≃ DeletionSet G k where
  toFun D := ⟨mapLines e D.val, (isDeletionSet_transport e D.val k).2 D.property⟩
  invFun D := ⟨mapLines e.symm D.val, (isDeletionSet_transport e.symm D.val k).2 D.property⟩
  left_inv D := Subtype.ext (mapLines_symm e D.val)
  right_inv D := Subtype.ext (mapLines_symm e.symm D.val)

@[simp] theorem deletionEquiv_val (e : F ≃+* G) (k : ℕ) (D : DeletionSet F k) :
    (deletionEquiv e k D).val = mapLines e D.val := rfl

@[simp] theorem uniformDeletionMass_transport (e : F ≃+* G) (k : ℕ) :
    uniformDeletionMass (F := G) k = uniformDeletionMass (F := F) k := by
  unfold uniformDeletionMass
  rw [Fintype.card_congr (deletionEquiv e k)]

@[simp] theorem empiricalMultiplicityMass_transport (e : F ≃+* G)
    (D : Finset (Line F)) (n : ℕ) :
    empiricalMultiplicityMass (mapLines e D) n = empiricalMultiplicityMass D n := by
  have h : (Finset.univ.filter fun p : Point G =>
      deletionMultiplicity (mapLines e D) p = n) =
      mapPoints e (Finset.univ.filter fun p : Point F => deletionMultiplicity D p = n) := by
    ext p
    obtain ⟨p, rfl⟩ := (pointEquiv e).surjective p
    simp
  simp only [empiricalMultiplicityMass, h, card_mapPoints, cardinal_field e]

@[simp] theorem deletionMultiplicityTV_transport (e : F ≃+* G)
    (D : Finset (Line F)) (k : ℕ) :
    deletionMultiplicityTV k (mapLines e D) = deletionMultiplicityTV k D := by
  simp only [deletionMultiplicityTV, empiricalMultiplicityMass_transport]

omit [Fintype F] [Fintype G] in
@[simp] theorem mapPoints_inter (e : F ≃+* G) (U V : Finset (Point F)) :
    mapPoints e (U ∩ V) = mapPoints e U ∩ mapPoints e V := Finset.map_inter _ _

@[simp] theorem occupancy_card_transport (e : F ≃+* G)
    (D : Finset (Line F)) (l : Line F) :
    (linePoints (lineEquiv e l) ∩ uncoveredBy (mapLines e D)).card =
      (linePoints l ∩ uncoveredBy D).card := by
  rw [linePoints_transport, uncoveredBy_transport, ← mapPoints_inter, card_mapPoints]

@[simp] theorem exceptionalOccupancyLines_transport (e : F ≃+* G)
    (D : Finset (Line F)) (k : ℕ) (lam : ℝ) :
    exceptionalOccupancyLines k lam (mapLines e D) =
      mapLines e (exceptionalOccupancyLines k lam D) := by
  ext l
  obtain ⟨l, rfl⟩ := (lineEquiv e).surjective l
  simp only [mem_mapLines, exceptionalOccupancyLines, Finset.mem_filter,
    Finset.mem_univ, true_and, mem_mapLines, occupancy_card_transport, cardinal_field e]

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G] in
@[simp] theorem coversPoints_transport (e : F ≃+* G)
    (C : Finset (Line F)) (U : Finset (Point F)) :
    CoversPoints (mapLines e C) (mapPoints e U) ↔ CoversPoints C U := by
  constructor
  · intro h p hp
    obtain ⟨l, hl, hon⟩ := h (pointEquiv e p) ((mem_mapPoints e U p).2 hp)
    obtain ⟨l, rfl⟩ := (lineEquiv e).surjective l
    exact ⟨l, (mem_mapLines e C l).1 hl, (onLine_transport e p l).1 hon⟩
  · intro h p hp
    obtain ⟨p, rfl⟩ := (pointEquiv e).surjective p
    obtain ⟨l, hl, hon⟩ := h p ((mem_mapPoints e U p).1 hp)
    exact ⟨lineEquiv e l, (mem_mapLines e C l).2 hl, (onLine_transport e p l).2 hon⟩

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G] in
@[simp] theorem disjoint_mapLines (e : F ≃+* G) (C D : Finset (Line F)) :
    Disjoint (mapLines e C) (mapLines e D) ↔ Disjoint C D := by
  exact Finset.disjoint_map (lineEquiv e).toEmbedding

theorem badCoreCover_map (e : F ≃+* G) (D : Finset (Line F)) (δ : ℝ)
    (h : BadCoreCover δ D) : BadCoreCover δ (mapLines e D) := by
  obtain ⟨C, hdisj, hsize, hcover, hmiss⟩ := h
  refine ⟨mapLines e C, (disjoint_mapLines e C D).2 hdisj, ?_, ?_, ?_⟩
  · simpa only [card_mapLines, cardinal_field e] using hsize
  · rw [uncoveredBy_transport]
    exact (coversPoints_transport e C (uncoveredBy D)).2 hcover
  · simpa only [uncoveredBy_transport, card_mapPoints, cardinal_field e] using hmiss

@[simp] theorem badCoreCover_transport (e : F ≃+* G) (D : Finset (Line F)) (δ : ℝ) :
    BadCoreCover δ (mapLines e D) ↔ BadCoreCover δ D := by
  constructor
  · intro h
    simpa only [mapLines_symm] using badCoreCover_map e.symm (mapLines e D) δ h
  · exact badCoreCover_map e D δ

def mapLaw (e : F ≃+* G) {k : ℕ} (Q : PMF (DeletionSet F k)) :
    PMF (DeletionSet G k) := Q.map (deletionEquiv e k)

@[simp] theorem mapLaw_apply (e : F ≃+* G) {k : ℕ}
    (Q : PMF (DeletionSet F k)) (D : DeletionSet F k) :
    mapLaw e Q (deletionEquiv e k D) = Q D := by
  classical
  rw [mapLaw, PMF.map_apply]
  have hterm (a : DeletionSet F k) :
      (if deletionEquiv e k D = deletionEquiv e k a then Q a else 0) =
        (if a = D then Q a else 0) := by
    by_cases ha : a = D
    · subst a
      simp
    · have hne : deletionEquiv e k D ≠ deletionEquiv e k a :=
        fun h => ha ((deletionEquiv e k).injective h).symm
      simp [ha, hne]
  calc
    (∑' a, if deletionEquiv e k D = deletionEquiv e k a then Q a else 0) =
        ∑' a, if a = D then Q a else 0 := tsum_congr hterm
    _ = Q D := by simp

@[simp] theorem deletionDominated_transport (e : F ≃+* G) {k : ℕ}
    (Q : PMF (DeletionSet F k)) (K : ℝ) :
    DeletionDominated k K (mapLaw e Q) ↔ DeletionDominated k K Q := by
  constructor
  · intro h D
    simpa only [mapLaw_apply, cardinal_field e, uniformDeletionMass_transport e]
      using h (deletionEquiv e k D)
  · intro h D
    obtain ⟨D, rfl⟩ := (deletionEquiv e k).surjective D
    simpa only [mapLaw_apply, cardinal_field e, uniformDeletionMass_transport e] using h D

theorem deletionEventProbability_mapLaw (e : F ≃+* G) {k : ℕ}
    (Q : PMF (DeletionSet F k)) (E : DeletionSet G k → Prop) :
    deletionEventProbability (mapLaw e Q) E =
      deletionEventProbability Q (fun D => E (deletionEquiv e k D)) := by
  classical
  unfold deletionEventProbability
  rw [← (deletionEquiv e k).sum_comp
    (fun D => if E D then (mapLaw e Q D).toReal else 0)]
  simp only [mapLaw_apply]

theorem multiplicity_failure_probability_transport (e : F ≃+* G) {k : ℕ}
    (Q : PMF (DeletionSet F k)) (τ : ℝ) :
    deletionEventProbability (mapLaw e Q) (fun D => τ ≤ deletionMultiplicityTV k D.val) =
      deletionEventProbability Q (fun D => τ ≤ deletionMultiplicityTV k D.val) := by
  rw [deletionEventProbability_mapLaw]
  simp only [deletionEquiv_val, deletionMultiplicityTV_transport]

theorem occupancy_failure_probability_transport (e : F ≃+* G) {k : ℕ}
    (Q : PMF (DeletionSet F k)) (lam η : ℝ) :
    deletionEventProbability (mapLaw e Q) (fun D => η * (Fintype.card G : ℝ) ≤
      ((exceptionalOccupancyLines k lam D.val).card : ℝ)) =
    deletionEventProbability Q (fun D => η * (Fintype.card F : ℝ) ≤
      ((exceptionalOccupancyLines k lam D.val).card : ℝ)) := by
  rw [deletionEventProbability_mapLaw]
  simp only [deletionEquiv_val, exceptionalOccupancyLines_transport,
    card_mapLines, cardinal_field e]

theorem core_cover_failure_probability_transport (e : F ≃+* G) {k : ℕ}
    (Q : PMF (DeletionSet F k)) (δ : ℝ) :
    deletionEventProbability (mapLaw e Q) (fun D => BadCoreCover δ D.val) =
      deletionEventProbability Q (fun D => BadCoreCover δ D.val) := by
  rw [deletionEventProbability_mapLaw]
  simp only [deletionEquiv_val, badCoreCover_transport]

theorem same_order_deletion_transport (hcard : Fintype.card F = Fintype.card G)
    {k : ℕ} (Q : PMF (DeletionSet F k)) :
    ∃ Q' : PMF (DeletionSet G k),
      (∀ K : ℝ, DeletionDominated k K Q' ↔ DeletionDominated k K Q) ∧
      (∀ τ : ℝ, deletionEventProbability Q' (fun D => τ ≤ deletionMultiplicityTV k D.val) =
        deletionEventProbability Q (fun D => τ ≤ deletionMultiplicityTV k D.val)) ∧
      (∀ lam η : ℝ, deletionEventProbability Q' (fun D => η * (Fintype.card G : ℝ) ≤
          ((exceptionalOccupancyLines k lam D.val).card : ℝ)) =
        deletionEventProbability Q (fun D => η * (Fintype.card F : ℝ) ≤
          ((exceptionalOccupancyLines k lam D.val).card : ℝ))) ∧
      (∀ δ : ℝ, deletionEventProbability Q' (fun D => BadCoreCover δ D.val) =
        deletionEventProbability Q (fun D => BadCoreCover δ D.val)) := by
  let e : F ≃+* G := FiniteField.ringEquivOfCardEq hcard
  exact ⟨mapLaw e Q, deletionDominated_transport e Q,
    multiplicity_failure_probability_transport e Q,
    occupancy_failure_probability_transport e Q,
    core_cover_failure_probability_transport e Q⟩

end Balanced.FieldTransport

end

end OAI
