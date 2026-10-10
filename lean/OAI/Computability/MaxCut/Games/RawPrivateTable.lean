import Mathlib
import OAI.Computability.MaxCut.Games.RawPartnerTarget

namespace OAI

/-! The private Fourier table is defined from displayed data alone. Compatibility
with every hidden extension follows from the proved canonical locality theorem. -/

namespace MaxCutGames.Soundness.RawPrivateTable
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open PartnerProjection RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Id Name : Type}

abbrev Extension (k : Nat) (Id : Type) := (Fin k → Id) × (Fin k → Slot)

def displayed (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) : Fin k → Sum Id Name :=
  fun j => if j ∈ J then
    Sum.inr (names (occ j) (ConcreteExtraction.slotIndex (slot j)))
  else Sum.inl (occ j)

theorem full_occurrence_eq_of_displayed_eq
    {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    {occ occ' : Fin k → Id} {slot slot' : Fin k → Slot}
    (h : displayed J names occ slot = displayed J names occ' slot')
    (j : Fin k) (hj : j ∉ J) : occ j = occ' j := by
  simpa [displayed, hj] using congrFun h j

theorem single_name_eq_of_displayed_eq
    {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    {occ occ' : Fin k → Id} {slot slot' : Fin k → Slot}
    (h : displayed J names occ slot = displayed J names occ' slot')
    (j : Fin k) (hj : j ∈ J) :
    names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j)) := by
  simpa [displayed, hj] using congrFun h j

theorem displayed_eq_iff (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot) :
    displayed J names occ slot = displayed J names occ' slot' ↔
      (∀ j, j ∉ J → occ j = occ' j) ∧
      (∀ j, j ∈ J → names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
        names (occ' j) (ConcreteExtraction.slotIndex (slot' j))) := by
  constructor
  · intro h
    exact ⟨fun j hj => full_occurrence_eq_of_displayed_eq h j hj,
      fun j hj => single_name_eq_of_displayed_eq h j hj⟩
  · rintro ⟨hfull, hsingle⟩
    funext j
    by_cases hj : j ∈ J
    · simp [displayed, hj, hsingle j hj]
    · simp [displayed, hj, hfull j hj]

def SupportedV (J : Finset (Fin k)) (names : Id → Fin 3 → Name) : Type :=
  { V : Fin k → Sum Id Name //
      V ∈ Set.range (fun e : Extension k Id => displayed J names e.1 e.2) }

def representative {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    (V : SupportedV J names) : Extension k Id := Classical.choose V.property

theorem representative_display {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    (V : SupportedV J names) :
    displayed J names (representative V).1 (representative V).2 = V.val :=
  Classical.choose_spec V.property

def supported (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) : SupportedV J names :=
  ⟨displayed J names occ slot, ⟨(occ, slot), rfl⟩⟩

variable (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
  {R D C Label : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]
  [DecidableEq Id] [DecidableEq Name]

def projection (occ : Fin k → Id) (slot : Fin k → Slot) :
    ActualHomogeneous.E k →ₗ[F2] RawPoint J :=
  rawProjection (fun j => toBit (rhs (occ j))) J slot

def merge {A : Type} [AddCommGroup A] [Module F2 A]
    (split : R ≃ₗ[F2] D × C) (Z : A →ₗ[F2] D) (X : A →ₗ[F2] C) : A →ₗ[F2] R :=
  split.symm.toLinearMap.comp (Z.prod X)

omit [DecidableEq R] in
theorem merge_comp {A B : Type} [AddCommGroup A] [Module F2 A]
    [AddCommGroup B] [Module F2 B] (split : R ≃ₗ[F2] D × C)
    (Z : B →ₗ[F2] D) (X : B →ₗ[F2] C) (pi : A →ₗ[F2] B) :
    merge split (Z.comp pi) (X.comp pi) = (merge split Z X).comp pi := rfl

def sourceTable (split : R ≃ₗ[F2] D × C)
    (label : ActualCanonical.Data k Name Id R → Label) (occ : Fin k → Id)
    (Z : ActualHomogeneous.E k →ₗ[F2] D) (X : ActualHomogeneous.E k →ₗ[F2] C) : Label :=
  label (ActualCanonical.canonical occ names rhs (merge split Z X))

def privateTable (split : R ≃ₗ[F2] D × C)
    (label : ActualCanonical.Data k Name Id R → Label) (V : SupportedV J names)
    (Z : RawPoint J →ₗ[F2] D) (X : RawPoint J →ₗ[F2] C) : Label :=
  sourceTable names rhs split label (representative V).1
    (Z.comp (projection J rhs (representative V).1 (representative V).2))
    (X.comp (projection J rhs (representative V).1 (representative V).2))

theorem canonical_same_display (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (Y : RawPoint J →ₗ[F2] R)
    (h : displayed J names occ slot = displayed J names occ' slot') :
    ActualCanonical.canonical occ names rhs (Y.comp (projection J rhs occ slot)) =
      ActualCanonical.canonical occ' names rhs (Y.comp (projection J rhs occ' slot')) := by
  unfold projection
  rw [rawMap_pullback, rawMap_pullback]
  exact ActualCanonicalPullback.canonical_private_input_locality J R names rhs
    occ occ' slot slot' (gammaOfRawMap J Y)
    (full_occurrence_eq_of_displayed_eq h) (single_name_eq_of_displayed_eq h)

/-- Exact table compatibility with no extension or hidden question supplied to
the private table. The row and column are merged before canonicalization. -/
theorem privateTable_pullback (split : R ≃ₗ[F2] D × C)
    (label : ActualCanonical.Data k Name Id R → Label)
    (occ : Fin k → Id) (slot : Fin k → Slot)
    (Z : RawPoint J →ₗ[F2] D) (X : RawPoint J →ₗ[F2] C) :
    privateTable J names rhs split label (supported J names occ slot) Z X =
      sourceTable names rhs split label occ
        (Z.comp (projection J rhs occ slot)) (X.comp (projection J rhs occ slot)) := by
  unfold privateTable sourceTable
  rw [merge_comp, merge_comp]
  apply congrArg label
  exact canonical_same_display J names rhs _ _ _ _ (merge split Z X)
    (representative_display (supported J names occ slot))

end
end MaxCutGames.Soundness.RawPrivateTable

end OAI
