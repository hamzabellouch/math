import OAI.Algebra.DepthFive.Pairings

namespace OAI

namespace Problem335.Pairings

open scoped BigOperators

noncomputable section

/-- A signed coordinate in every layer, as used by the mixed IMM operator. -/
def layerShift {ι α : Type*} [Fintype ι]
    (sign : ι → ℤ) (coordinate : ι → α) : (ι × α) →₀ ℤ :=
  ∑ i, Finsupp.single (i, coordinate i) (sign i)

@[simp]
theorem layerShift_apply {ι α : Type*} [Fintype ι] [DecidableEq α]
    (sign : ι → ℤ) (coordinate : ι → α) (i : ι) (a : α) :
    layerShift sign coordinate (i, a) = if coordinate i = a then sign i else 0 := by
  classical
  simp [layerShift, Finsupp.single_apply, Prod.mk.injEq, ite_and]

/-- Nonzero signed layer coordinates determine the entire coordinate sequence. -/
theorem layerShift_injective {ι α : Type*} [Fintype ι]
    (sign : ι → ℤ) (hsign : ∀ i, sign i ≠ 0) :
    Function.Injective (layerShift (α := α) sign) := by
  classical
  intro x y h
  funext i
  by_contra hxy
  have hi := congrArg (fun z : (ι × α) →₀ ℤ => z (i, x i)) h
  simp [layerShift_apply, Ne.symm hxy, hsign i] at hi

/-- A common nonzero signed coefficient does not change the pairing classification. -/
theorem weighted_coordinate_difference_eq_iff {α : Type*}
    (z : ℤ) (hz : z ≠ 0) (p q r s : α) :
    (Finsupp.single p z - Finsupp.single q z =
      Finsupp.single r z - Finsupp.single s z) ↔
    (p = q ∧ r = s) ∨ (p = r ∧ q = s) := by
  have hs (a : α) : Finsupp.single a z = z • Finsupp.single a (1 : ℤ) := by
    simp
  rw [hs p, hs q, hs r, hs s, ← smul_sub, ← smul_sub,
    smul_right_inj hz, coordinate_difference_eq_iff]

/-- Restrict a finitely supported coordinate vector to one matrix layer. -/
def layerProjection {ι α : Type*} (i : ι) : ((ι × α) →₀ ℤ) →+ (α →₀ ℤ) :=
  Finsupp.comapDomain.addMonoidHom (f := fun a : α => (i, a))
    (fun _ _ h => congrArg Prod.snd h)

@[simp]
theorem layerProjection_layerShift {ι α : Type*} [Fintype ι]
    (sign : ι → ℤ) (coordinate : ι → α) (i : ι) :
    layerProjection i (layerShift sign coordinate) =
      Finsupp.single (coordinate i) (sign i) := by
  classical
  ext a
  simp [layerProjection, Finsupp.comapDomain.addMonoidHom,
    Finsupp.comapDomain_apply, Finsupp.single_apply]

/-- The four-shift compatibility condition holds independently in every layer. -/
theorem layerShift_difference_eq_iff {ι α : Type*} [Fintype ι]
    (sign : ι → ℤ) (hsign : ∀ i, sign i ≠ 0) (p q r s : ι → α) :
    (layerShift sign p - layerShift sign q = layerShift sign r - layerShift sign s) ↔
    ∀ i, (p i = q i ∧ r i = s i) ∨ (p i = r i ∧ q i = s i) := by
  classical
  constructor
  · intro h i
    apply (weighted_coordinate_difference_eq_iff (sign i) (hsign i) _ _ _ _).mp
    have hi := congrArg (layerProjection (α := α) i) h
    simpa only [map_sub, layerProjection_layerShift] using hi
  · intro h
    ext ⟨i, a⟩
    rcases h i with ⟨hpq, hrs⟩ | ⟨hpr, hqs⟩
    · simp [layerShift_apply, hpq, hrs]
    · simp [layerShift_apply, hpr, hqs]

/-- Edges of a path with at least one edge. -/
def edgeCoordinates {α : Type*} {L : ℕ} (P : Fin (L + 2) → α)
    (i : Fin (L + 1)) : α × α :=
  (P i.castSucc, P i.succ)

/-- The coordinates in all layers determine all vertices of the path. -/
theorem edgeCoordinates_injective {α : Type*} {L : ℕ} :
    Function.Injective (edgeCoordinates (α := α) (L := L)) := by
  intro P Q h
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hzero := congrArg (fun f : Fin (L + 1) → α × α => (f 0).1) h
    simpa [edgeCoordinates] using hzero
  · have hj := congrArg (fun f : Fin (L + 1) → α × α => (f j).2) h
    simpa [edgeCoordinates] using hj

/-- Distinct paths produce distinct signed shifts, regardless of the V/U schedule. -/
theorem pathShift_injective {α : Type*} {L : ℕ}
    (sign : Fin (L + 1) → ℤ) (hsign : ∀ i, sign i ≠ 0) :
    Function.Injective (fun P : Fin (L + 2) → α =>
      layerShift sign (edgeCoordinates P)) :=
  (layerShift_injective sign hsign).comp edgeCoordinates_injective

end
end Problem335.Pairings

end OAI
