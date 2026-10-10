import Mathlib
import OAI.Computability.DirectedFeedback.Games.ActualCanonical
import OAI.Computability.DirectedFeedback.Analysis.Deletion

namespace OAI


namespace DFVSGames.Soundness.RawPrivateTable
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
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
end DFVSGames.Soundness.RawPrivateTable


namespace DFVSGames.Decoder.TableKeys

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open scoped BigOperators

universe u v w

section BlockReduction

variable {Name : Type u} {Id : Type v} {R : Type w}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

def slope (a d : R) : (F2 × F2) →ₗ[F2] R :=
  (LinearMap.fst F2 F2 F2).smulRight a +
    (LinearMap.snd F2 F2 F2).smulRight d

omit [DecidableEq R] in
@[simp] theorem slope_apply (a d : R) (x y : F2) :
    slope a d (x, y) = x • a + y • d := rfl

omit [DecidableEq R] in
theorem slope_zero_iff (a d : R) : slope a d = 0 ↔ a = 0 ∧ d = 0 := by
  constructor
  · intro h
    have hfirst := congrArg (fun f : (F2 × F2) →ₗ[F2] R => f (1, 0)) h
    have hsecond := congrArg (fun f : (F2 × F2) →ₗ[F2] R => f (0, 1)) h
    exact ⟨by simpa using hfirst, by simpa using hsecond⟩
  · rintro ⟨rfl, rfl⟩
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp [slope]

omit [DecidableEq R] in

theorem slope_injective (a d : R) (ha : a ≠ 0) (hd : d ≠ 0) (had : a ≠ d) :
    Function.Injective (slope a d) := by
  have hzero : ∀ p, slope a d p = 0 → p = 0 := by
    rintro ⟨x, y⟩ h
    rcases scalar_cases x with rfl | rfl <;>
      rcases scalar_cases y with rfl | rfl
    · rfl
    · exact False.elim (hd (by simpa using h))
    · exact False.elim (ha (by simpa using h))
    · have heq : a + d = 0 := by simpa using h
      have hc := congrArg (fun z : R => z + d) heq
      have had' : a = d := by
        simpa only [add_assoc, ActualCanonical.add_self, add_zero, zero_add] using hc
      exact False.elim (had had')
  intro x y hxy
  have hs : slope a d (x + y) = 0 := by
    rw [map_add, hxy, ActualCanonical.add_self]
  have hc := congrArg (fun p : F2 × F2 => p + y) (hzero (x + y) hs)
  simpa only [add_assoc, ActualCanonical.add_self, add_zero, zero_add] using hc

def freeTriple (a d : R) : Fin 3 → R := ![a, d, 0]

def reduceBlock (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) (a d : R) : R × ActualCanonical.Record Name Id R :=
  (rhs e • ActualCanonical.pivot (freeTriple a d),
    ActualCanonical.record names e (freeTriple a d))

@[simp] theorem reduceBlock_zero (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) : reduceBlock names rhs e (0 : R) 0 = (0, .blank) := by
  simp [reduceBlock, freeTriple, ActualCanonical.pivot, ActualCanonical.record]

theorem reduceBlock_first (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) (a : R) (ha : a ≠ 0) :
    reduceBlock names rhs e a 0 = (0, .single (names e 0) a) := by
  simp [reduceBlock, freeTriple, ActualCanonical.pivot, ActualCanonical.record, ha]

theorem reduceBlock_second (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) (d : R) (hd : d ≠ 0) :
    reduceBlock names rhs e 0 d = (0, .single (names e 1) d) := by
  simp [reduceBlock, freeTriple, ActualCanonical.pivot, ActualCanonical.record,
    Ne.symm hd]

theorem reduceBlock_third (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) (a : R) (ha : a ≠ 0) :
    reduceBlock names rhs e a a = (rhs e • a, .single (names e 2) a) := by
  simp [reduceBlock, freeTriple, ActualCanonical.pivot, ActualCanonical.record, ha]

theorem reduceBlock_full (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) (a d : R) (ha : a ≠ 0) (hd : d ≠ 0) (had : a ≠ d) :
    reduceBlock names rhs e a d = (0, .full e (freeTriple a d)) := by
  simp [reduceBlock, freeTriple, ActualCanonical.pivot, ActualCanonical.record,
    ActualCanonical.normalize, ha, hd, had]
  funext i
  exact add_zero _

omit [DecidableEq R] in

theorem third_intercept_cancels (z a : R) (b : F2) :
    (z + b • a) + b • a = z := by
  rw [add_assoc, ActualCanonical.add_self, add_zero]

theorem third_key_cancels (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) (z a : R) (ha : a ≠ 0) :
    ((z + rhs e • a) + (reduceBlock names rhs e a a).1,
      (reduceBlock names rhs e a a).2) = (z, .single (names e 2) a) := by
  rw [reduceBlock_third names rhs e a ha]
  simp only [third_intercept_cancels]

omit [AddCommGroup R] [Module F2 R] [DecidableEq R] in

theorem full_record_occurrence_injective {e e' : Id} {a a' : Fin 3 → R}
    (h : (ActualCanonical.Record.full e a : ActualCanonical.Record Name Id R) =
      .full e' a') : e = e' := by
  cases h
  rfl

end BlockReduction


variable {Name Id R : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
variable {k : Nat}

abbrev Key (k : Nat) (Name Id R : Type) := ActualCanonical.Data k Name Id R

def key (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (P : ActualHomogeneous.E k →ₗ[F2] R) : Key k Name Id R :=
  ActualCanonical.canonical occ names rhs P

omit [AddCommGroup R] [Module F2 R] [DecidableEq R] in

theorem key_data_ext_iff (a b : Key k Name Id R) :
    a = b ↔ a.1 = b.1 ∧ ∀ j : Fin k, a.2 j = b.2 j := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨hfirst, hrest⟩
    exact Prod.ext hfirst (funext hrest)

theorem key_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (P : ActualHomogeneous.E k →ₗ[F2] R) (c : R) :
    key occ names rhs (P + ActualHomogeneous.tau.smulRight c) =
      ((key occ names rhs P).1 + c, (key occ names rhs P).2) :=
  ActualCanonical.canonical_shift occ names rhs P c

theorem key_shift_free (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (P : ActualHomogeneous.E k →ₗ[F2] R) (c : R)
    (h : key occ names rhs (P + ActualHomogeneous.tau.smulRight c) =
      key occ names rhs P) : c = 0 := by
  rw [key_shift] at h
  have hc := congrArg Prod.fst h
  exact add_left_cancel (hc.trans (add_zero _).symm)

variable [DecidableEq Name] [DecidableEq Id]

theorem projected_key_sharing
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R)
    (h : RawPrivateTable.displayed J names occ slot =
      RawPrivateTable.displayed J names occ' slot') :
    key occ names rhs (Y.comp (RawPrivateTable.projection J rhs occ slot)) =
      key occ' names rhs (Y.comp (RawPrivateTable.projection J rhs occ' slot')) :=
  RawPrivateTable.canonical_same_display J names rhs occ occ' slot slot' Y h

noncomputable def projectedKey (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (Q : RawPrivateTable.SupportedV J names) (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) :
    Key k Name Id R :=
  key (RawPrivateTable.representative Q).1 names rhs
    (Y.comp (RawPrivateTable.projection J rhs (RawPrivateTable.representative Q).1
      (RawPrivateTable.representative Q).2))

theorem projectedKey_pullback
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) :
    projectedKey J names rhs (RawPrivateTable.supported J names occ slot) Y =
      key occ names rhs (Y.comp (RawPrivateTable.projection J rhs occ slot)) := by
  apply projected_key_sharing
  exact RawPrivateTable.representative_display (RawPrivateTable.supported J names occ slot)


end DFVSGames.Decoder.TableKeys


namespace DFVSGames.Decoder.TableKeys

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness

variable {Name Id R : Type} [AddCommGroup R] [Module F2 R]
variable {k : Nat}

def visibleTau (J : Finset (Fin k)) : RawPartnerTarget.RawPoint J →ₗ[F2] F2 :=
  LinearMap.proj none

theorem projection_surjective (J : Finset (Fin k)) (rhs : Id → F2)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot) :
    Function.Surjective (RawPrivateTable.projection J rhs occ slot) := by
  exact (PartnerMapCoordinates.pointEquiv (fun j => toBit (rhs (occ j))) J).surjective.comp
    ((PartnerLinear.projection_surjective (fun j => toBit (rhs (occ j)))
      (PartnerMapCoordinates.activeOf J) slot).comp
        (PartnerLinear.sourceLinearEquiv (fun j => toBit (rhs (occ j)))).symm.surjective)

theorem projection_preserves_homogeneous (J : Finset (Fin k)) (rhs : Id → F2)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (x : ActualHomogeneous.E k) :
    visibleTau J (RawPrivateTable.projection J rhs occ slot x) = ActualHomogeneous.tau x := by
  change ofBit (toBit x.1) = x.1
  exact ofBit_toBit _

theorem visible_table_unique (J : Finset (Fin k)) (rhs : Id → F2)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (Y Z : RawPartnerTarget.RawPoint J →ₗ[F2] R)
    (h : Y.comp (RawPrivateTable.projection J rhs occ slot) =
      Z.comp (RawPrivateTable.projection J rhs occ slot)) : Y = Z := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := projection_surjective J rhs occ slot y
  exact congrArg (fun P : ActualHomogeneous.E k →ₗ[F2] R => P x) h

theorem pullback_shift (J : Finset (Fin k)) (rhs : Id → F2)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) (c : R) :
    (Y + (visibleTau J).smulRight c).comp (RawPrivateTable.projection J rhs occ slot) =
      Y.comp (RawPrivateTable.projection J rhs occ slot) +
        ActualHomogeneous.tau.smulRight c := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
    projection_preserves_homogeneous]

variable [DecidableEq Name] [DecidableEq Id] [DecidableEq R]

omit [DecidableEq Name] [DecidableEq Id] in

theorem projectedKey_shift (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (Q : RawPrivateTable.SupportedV J names)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) (c : R) :
    projectedKey J names rhs Q (Y + (visibleTau J).smulRight c) =
      ((projectedKey J names rhs Q Y).1 + c, (projectedKey J names rhs Q Y).2) := by
  unfold projectedKey
  rw [pullback_shift, key_shift]

end DFVSGames.Decoder.TableKeys


namespace DFVSGames.Decoder.AdviceExperiment

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness

noncomputable section

variable (k : Nat) (Id K W R : Type)
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup W] [Module F2 W]
variable [AddCommGroup R] [Module F2 R]

structure FullAdvice where
  occurrences : Fin k → Id
  rowMap : K →ₗ[F2] R
  complement : ActualHomogeneous.E k →ₗ[F2] W
  rows : ActualHomogeneous.E k →ₗ[F2] R

structure Draw where
  singletons : Finset (Fin k)
  occurrences : Fin k → Id
  positions : Fin k → PartnerProjection.Slot
  rowMap : K →ₗ[F2] R
  hiddenMatrix : RawPartnerTarget.RawPoint singletons →ₗ[F2] K
  complement : RawPartnerTarget.RawPoint singletons →ₗ[F2] W

variable {k Id K W R}

variable {Name : Type} (names : Id → Fin 3 → Name)

structure ProjectedAdvice (J : Finset (Fin k)) where
  question : RawPrivateTable.SupportedV J names
  rowMap : K →ₗ[F2] R
  complement : RawPartnerTarget.RawPoint J →ₗ[F2] W
  rows : RawPartnerTarget.RawPoint J →ₗ[F2] R

variable (rhs : Id → F2)

def projection (d : Draw k Id K W R) :
    ActualHomogeneous.E k →ₗ[F2] RawPartnerTarget.RawPoint d.singletons :=
  RawPrivateTable.projection d.singletons rhs d.occurrences d.positions

def leftObservation (d : Draw k Id K W R) : FullAdvice k Id K W R where
  occurrences := d.occurrences
  rowMap := d.rowMap
  complement := d.complement.comp (projection rhs d)
  rows := (d.rowMap.comp d.hiddenMatrix).comp (projection rhs d)

def rightObservation (d : Draw k Id K W R) :
    (J : Finset (Fin k)) × ProjectedAdvice (K := K) (W := W) (R := R) names J :=
  ⟨d.singletons, {
    question := RawPrivateTable.supported d.singletons names d.occurrences d.positions
    rowMap := d.rowMap
    complement := d.complement
    rows := d.rowMap.comp d.hiddenMatrix }⟩

def paddedMatrix (d : Draw k Id K W R) : ActualHomogeneous.E k →ₗ[F2] K :=
  d.hiddenMatrix.comp (projection rhs d)

def paddedComplement (d : Draw k Id K W R) : ActualHomogeneous.E k →ₗ[F2] W :=
  d.complement.comp (projection rhs d)

theorem left_rows_eq (d : Draw k Id K W R) :
    (leftObservation rhs d).rows = d.rowMap.comp (paddedMatrix rhs d) := rfl

theorem left_rows_attainable (d : Draw k Id K W R) :
    ∃ M : ActualHomogeneous.E k →ₗ[F2] K,
      (leftObservation rhs d).rowMap.comp M = (leftObservation rhs d).rows :=
  ⟨paddedMatrix rhs d, rfl⟩

theorem right_rows_attainable (d : Draw k Id K W R) :
    ∃ M : RawPartnerTarget.RawPoint d.singletons →ₗ[F2] K,
      d.rowMap.comp M = (rightObservation names d).2.rows :=
  ⟨d.hiddenMatrix, rfl⟩

def changeHidden (d : Draw k Id K W R)
    (N : RawPartnerTarget.RawPoint d.singletons →ₗ[F2] d.rowMap.ker) : Draw k Id K W R :=
  { d with hiddenMatrix := AdviceFibers.assemble d.rowMap d.hiddenMatrix N }

theorem leftObservation_changeHidden (d : Draw k Id K W R)
    (N : RawPartnerTarget.RawPoint d.singletons →ₗ[F2] d.rowMap.ker) :
    leftObservation rhs (changeHidden d N) = leftObservation rhs d := by
  simp only [leftObservation, changeHidden, projection, AdviceFibers.observed_assemble]

theorem rightObservation_changeHidden (d : Draw k Id K W R)
    (N : RawPartnerTarget.RawPoint d.singletons →ₗ[F2] d.rowMap.ker) :
    rightObservation names (changeHidden d N) = rightObservation names d := by
  simp only [rightObservation, changeHidden, AdviceFibers.observed_assemble]

theorem selectedWitness_changeHidden {Witness : Type*}
    (choose : FullAdvice k Id K W R → Witness) (d : Draw k Id K W R)
    (N : RawPartnerTarget.RawPoint d.singletons →ₗ[F2] d.rowMap.ker) :
    choose (leftObservation rhs (changeHidden d N)) = choose (leftObservation rhs d) := by
  rw [leftObservation_changeHidden]

theorem projection_actual_answer (d : Draw k Id K W R)
    (z : ActualHomogeneous.E k) (hz : ActualHomogeneous.tau z = 1) :
    TableKeys.visibleTau d.singletons (projection rhs d z) = 1 := by
  rw [projection, TableKeys.projection_preserves_homogeneous, hz]

end
end DFVSGames.Decoder.AdviceExperiment


namespace DFVSGames.Clean.AdviceImageLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Soundness.ConditionalIncidences
open DFVSGames.Soundness.PartnerMapCoordinates
open DFVSGames.Foundations.Games

noncomputable section

attribute [local instance] Classical.propDecidable

variable {K S W : Type} [AddCommGroup K] [Module F2 K]
  [AddCommGroup S] [Module F2 S]

def rangePoint (A : K →ₗ[F2] S) (m : K) : A.range :=
  ⟨A m, ⟨m, rfl⟩⟩

def selectedLift (A : K →ₗ[F2] S) (z : A.range) : K :=
  Classical.choose z.property

theorem selectedLift_spec (A : K →ₗ[F2] S) (z : A.range) :
    A (selectedLift A z) = (z : S) :=
  Classical.choose_spec z.property

theorem rangePoint_lift_add_kernel (A : K →ₗ[F2] S) (z : A.range) (k : A.ker) :
    rangePoint A (selectedLift A z + (k : K)) = z := by
  apply Subtype.ext
  change A (selectedLift A z + (k : K)) = (z : S)
  rw [map_add, selectedLift_spec, k.property, add_zero]

def imageKernelEquiv (A : K →ₗ[F2] S) : K ≃ A.range × A.ker where
  toFun m := (rangePoint A m,
    ⟨m - selectedLift A (rangePoint A m), by
      change A (m - selectedLift A (rangePoint A m)) = 0
      rw [map_sub, selectedLift_spec]
      exact sub_self _⟩)
  invFun p := selectedLift A p.1 + (p.2 : K)
  left_inv m := by
    change selectedLift A (rangePoint A m) + (m - selectedLift A (rangePoint A m)) = m
    rw [add_comm, sub_add_cancel]
  right_inv p := by
    apply Prod.ext
    · exact rangePoint_lift_add_kernel A p.1 p.2
    · apply Subtype.ext
      change selectedLift A p.1 + (p.2 : K) -
        selectedLift A (rangePoint A (selectedLift A p.1 + (p.2 : K))) = (p.2 : K)
      rw [rangePoint_lift_add_kernel]
      exact add_sub_cancel_left _ _

def columnImage (A : K →ₗ[F2] S) (column : W × K) : W × A.range :=
  (column.1, rangePoint A column.2)

def columnSplitEquiv (A : K →ₗ[F2] S) : (W × K) ≃ (W × A.range) × A.ker :=
  (Equiv.prodCongr (Equiv.refl W) (imageKernelEquiv A)).trans
    (Equiv.prodAssoc W A.range A.ker).symm

def visibleCoefficients {I : Type} (A : K →ₗ[F2] S)
    (columns : I → W × K) : I → W × A.range :=
  fun i => columnImage A (columns i)

def coefficientsSplitEquiv (I : Type) (A : K →ₗ[F2] S) :
    (I → W × K) ≃ (I → W × A.range) × (I → A.ker) :=
  (Equiv.piCongrRight fun _ : I => columnSplitEquiv (W := W) A).trans
    (Equiv.arrowProdEquivProdArrow I (fun _ => W × A.range) (fun _ => A.ker))

instance rangeFintype [Fintype S] (A : K →ₗ[F2] S) : Fintype A.range :=
  Fintype.ofFinite _

instance kernelFintype [Fintype K] (A : K →ₗ[F2] S) : Fintype A.ker :=
  Fintype.ofFinite _

theorem uniform_visible_coefficients {I : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) (F : (I → W × A.range) → ℝ) :
    (𝔼 columns : I → W × K, F (visibleCoefficients A columns)) =
      𝔼 visible : I → W × A.range, F visible := by
  calc
    (𝔼 columns : I → W × K, F (visibleCoefficients A columns)) =
        𝔼 pieces : (I → W × A.range) × (I → A.ker), F pieces.1 :=
      Fintype.expect_equiv (coefficientsSplitEquiv I A) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (I → W × A.range))
          (Finset.univ : Finset (I → A.ker)) (fun pieces => F pieces.1))

theorem uniform_coordinate_product {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    (f : I → E → ℝ) :
    (𝔼 columns : I → E, ∏ i, f i (columns i)) = ∏ i, 𝔼 e : E, f i e := by
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_pi, Nat.cast_prod]
  exact (Finset.prod_div_distrib _ _).symm

theorem visible_coefficient_product {I : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) (f : I → W × A.range → ℝ) :
    (𝔼 columns : I → W × K, ∏ i, f i (columnImage A (columns i))) =
      ∏ i, 𝔼 e : W × A.range, f i e := by
  exact (uniform_visible_coefficients A (fun visible => ∏ i, f i (visible i))).trans
    (uniform_coordinate_product f)

theorem uniform_pushforward_of_expect {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    [Nonempty Ω] [Nonempty Γ] (f : Ω → Γ)
    (h : ∀ F : Γ → ℝ, (𝔼 x : Ω, F (f x)) = 𝔼 y : Γ, F y) :
    (FiniteDistribution.uniform Ω).pushforward f = FiniteDistribution.uniform Γ := by
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  have he : (FiniteDistribution.uniform Ω).expectation
        (fun x => if f x = y then 1 else 0) =
      (FiniteDistribution.uniform Γ).expectation (fun z => if z = y then 1 else 0) := by
    simpa only [FiniteDistribution.expectation_uniform,
      ← Fintype.expect_eq_sum_div_card] using h (fun z => if z = y then 1 else 0)
  calc
    _ = (FiniteDistribution.uniform Ω).expectation
        (fun x => if f x = y then 1 else 0) := by
      simp [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]
    _ = _ := he
    _ = _ := by simp [FiniteDistribution.expectation, mul_ite]

theorem visible_coefficients_pushforward {I : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [Nonempty W] [Fintype K] [Fintype S] (A : K →ₗ[F2] S) :
    (FiniteDistribution.uniform (I → W × K)).pushforward (visibleCoefficients A) =
      FiniteDistribution.uniform (I → W × A.range) :=
  uniform_pushforward_of_expect (visibleCoefficients A) (uniform_visible_coefficients A)

theorem visible_card_le [Fintype W] [Fintype K] [Fintype S] (A : K →ₗ[F2] S) :
    Fintype.card (W × A.range) ≤ Fintype.card W * Fintype.card S := by
  rw [Fintype.card_prod]
  exact Nat.mul_le_mul_left _
    (Fintype.card_le_of_injective (fun z : A.range => (z : S)) Subtype.val_injective)

theorem visible_card_binary_le [Fintype K] (w r : Nat)
    (A : K →ₗ[F2] (Fin r → F2)) :
    Fintype.card ((Fin w → F2) × A.range) ≤ 2 ^ (w + r) := by
  calc
    Fintype.card ((Fin w → F2) × A.range) ≤
        Fintype.card (Fin w → F2) * Fintype.card (Fin r → F2) :=
      visible_card_le A
    _ = 2 ^ (w + r) := by simp [F2, pow_add]


variable {P : Type} [Fintype P] [DecidableEq P]
  [AddCommGroup W] [Module F2 W]
  (rhs : P → Bool) (J : Finset P)

abbrev PartnerSpace := DFVSGames.Soundness.PartnerProjection.PartnerPoint rhs (activeOf J)

theorem coefficients_comp (A : K →ₗ[F2] S) (M : PartnerSpace rhs J →ₗ[F2] K) :
    coefficients rhs J S (A.comp M) = fun i => A (coefficients rhs J K M i) := by
  funext i
  simp [coefficients, mapEquiv, LinearMap.comp_apply]

def actualVisibleCoefficients (A : K →ₗ[F2] S)
    (maps : (PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K)) :
    RawSlot J → W × A.range :=
  fun i => (coefficients rhs J W maps.1 i, rangePoint A (coefficients rhs J K maps.2 i))

theorem actualVisibleCoefficients_second (A : K →ₗ[F2] S)
    (T : PartnerSpace rhs J →ₗ[F2] W) (M : PartnerSpace rhs J →ₗ[F2] K)
    (i : RawSlot J) :
    ((actualVisibleCoefficients rhs J A (T, M) i).2 : S) =
      coefficients rhs J S (A.comp M) i := by
  rw [coefficients_comp]
  rfl

def actualMapPairEquiv :
    ((PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K)) ≃
      (RawSlot J → W × K) :=
  (Equiv.prodCongr (mapEquiv rhs J W).symm.toEquiv (mapEquiv rhs J K).symm.toEquiv).trans
    (Equiv.arrowProdEquivProdArrow (RawSlot J) (fun _ => W) (fun _ => K)).symm

theorem actual_maps_visible_uniform [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) (F : (RawSlot J → W × A.range) → ℝ) :
    (𝔼 maps : (PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K),
        F (actualVisibleCoefficients rhs J A maps)) =
      𝔼 gamma : RawSlot J → W × A.range, F gamma := by
  calc
    (𝔼 maps : (PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K),
        F (actualVisibleCoefficients rhs J A maps)) =
        𝔼 columns : RawSlot J → W × K, F (visibleCoefficients A columns) :=
      Fintype.expect_equiv (actualMapPairEquiv rhs J) _ _ (fun _ => rfl)
    _ = _ := uniform_visible_coefficients A F

theorem actual_maps_visible_product [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) (f : RawSlot J → W × A.range → ℝ) :
    (𝔼 maps : (PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K),
        ∏ i, f i (actualVisibleCoefficients rhs J A maps i)) =
      ∏ i, 𝔼 e : W × A.range, f i e := by
  exact (actual_maps_visible_uniform rhs J A (fun gamma => ∏ i, f i (gamma i))).trans
    (uniform_coordinate_product f)

theorem actual_maps_visible_pushforward [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) :
    (FiniteDistribution.uniform
        ((PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K))).pushforward
        (actualVisibleCoefficients rhs J A) =
      FiniteDistribution.uniform (RawSlot J → W × A.range) :=
  uniform_pushforward_of_expect (actualVisibleCoefficients rhs J A)
    (actual_maps_visible_uniform rhs J A)


end

end DFVSGames.Clean.AdviceImageLaw

end OAI
