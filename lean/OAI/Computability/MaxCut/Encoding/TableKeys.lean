import Mathlib
import OAI.Computability.MaxCut.Encoding.AdviceFibers
import OAI.Computability.MaxCut.Games.RawPrivateTable

namespace OAI

/-!
# Exact affine-table keys for the v2 outer questions

The retained data has one entry at every original block position.  A full entry
contains the equation *occurrence ID*, a singleton entry contains the actual
variable ID, and the first component is the entire reduced affine intercept.
The common coefficient-normalization implementation below is independent of
every latent-gadget existence or inverse theorem.

The explicit binary slope cases justify its use for the v2 rank-zero, rank-one,
and rank-two rule.  In particular, the third-position pullback adds the parity
intercept twice, so exact sharing preserves the intercept as well as the slopes.
-/

namespace MaxCutGames.Decoder.TableKeys

section

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open scoped BigOperators

universe u v w

section BlockReduction

variable {Name : Type u} {Id : Type v} {R : Type w}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

/-- The free-coordinate block slope `(x,y) ↦ x • a + y • d`. -/
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
/-- Over the binary field, the remaining case really is a rank-two slope:
the two-coordinate map is injective, rather than merely syntactically full. -/
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

/-- A single block's intercept correction and tagged retained record. -/
def reduceBlock (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) (a d : R) : R × ActualCanonical.Record Name Id R :=
  (rhs e • ActualCanonical.pivot (freeTriple a d),
    ActualCanonical.record names e (freeTriple a d))

@[simp] theorem reduceBlock_zero (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) : reduceBlock names rhs e (0 : R) 0 = (0, .blank) := by
  simp [reduceBlock, freeTriple, ActualCanonical.pivot, ActualCanonical.record]

/-- The first rank-one direction uses the actual first variable. -/
theorem reduceBlock_first (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) (a : R) (ha : a ≠ 0) :
    reduceBlock names rhs e a 0 = (0, .single (names e 0) a) := by
  simp [reduceBlock, freeTriple, ActualCanonical.pivot, ActualCanonical.record, ha]

/-- The second rank-one direction uses the actual second variable. -/
theorem reduceBlock_second (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) (d : R) (hd : d ≠ 0) :
    reduceBlock names rhs e 0 d = (0, .single (names e 1) d) := by
  simp [reduceBlock, freeTriple, ActualCanonical.pivot, ActualCanonical.record,
    Ne.symm hd]

/-- The third rank-one direction uses the actual third bit and adjusts the
homogeneous intercept by the parity bit times the nonzero slope. -/
theorem reduceBlock_third (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) (a : R) (ha : a ≠ 0) :
    reduceBlock names rhs e a a = (rhs e • a, .single (names e 2) a) := by
  simp [reduceBlock, freeTriple, ActualCanonical.pivot, ActualCanonical.record, ha]

/-- A genuine rank-two block retains its occurrence ID and both ordered slopes. -/
theorem reduceBlock_full (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (e : Id) (a d : R) (ha : a ≠ 0) (hd : d ≠ 0) (had : a ≠ d) :
    reduceBlock names rhs e a d = (0, .full e (freeTriple a d)) := by
  simp [reduceBlock, freeTriple, ActualCanonical.pivot, ActualCanonical.record,
    ActualCanonical.normalize, ha, hd, had]
  funext i
  exact add_zero _

omit [DecidableEq R] in
/-- Pulling an actual third-bit table back adds `b • a` to its intercept;
reducing the rank-one slope adds exactly the same quantity a second time. -/
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
/-- The reduced representation never merges two distinct occurrence IDs in
the full-block case. -/
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
/-- Key equality includes the affine intercept and every original position. -/
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

/-- Translation of the entire reduced affine table is a free action. -/
theorem key_shift_free (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (P : ActualHomogeneous.E k →ₗ[F2] R) (c : R)
    (h : key occ names rhs (P + ActualHomogeneous.tau.smulRight c) =
      key occ names rhs P) : c = 0 := by
  rw [key_shift] at h
  have hc := congrArg Prod.fst h
  exact add_left_cancel (hc.trans (add_zero _).symm)

variable [DecidableEq Name] [DecidableEq Id]

/-- Every displayed singleton is its actual bit, including the affine parity
intercept in position three.  Hidden occurrence IDs are forgotten precisely
at singleton positions and retained at full positions. -/
theorem projected_key_sharing
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R)
    (h : RawPrivateTable.displayed J names occ slot =
      RawPrivateTable.displayed J names occ' slot') :
    key occ names rhs (Y.comp (RawPrivateTable.projection J rhs occ slot)) =
      key occ' names rhs (Y.comp (RawPrivateTable.projection J rhs occ' slot')) :=
  RawPrivateTable.canonical_same_display J names rhs occ occ' slot slot' Y h

/-- The reduced table attached to visible data is independent of the compatible
full question used to realize it.  This is equality of the entire key. -/
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

end

/-! Surjective affine-coordinate projection and uniqueness of visible tables. -/

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness

variable {Name Id R : Type} [AddCommGroup R] [Module F2 R]
variable {k : Nat}

/-- Read the shared homogeneous coordinate in the visible coordinate system. -/
def visibleTau (J : Finset (Fin k)) : RawPartnerTarget.RawPoint J →ₗ[F2] F2 :=
  LinearMap.proj none

/-- Every visible valid answer extends to an answer of each compatible full
question.  This proves surjectivity of the actual affine-coordinate projection. -/
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

/-- Equality after pullback is equality of the entire visible linear extension,
so no affine intercept or hidden coefficient can be lost by sharing. -/
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
/-- Constant translation commutes with exact sharing at the level of whole
reduced keys, including the removed alphabet component of the intercept. -/
theorem projectedKey_shift (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (Q : RawPrivateTable.SupportedV J names)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) (c : R) :
    projectedKey J names rhs Q (Y + (visibleTau J).smulRight c) =
      ((projectedKey J names rhs Q Y).1 + c, (projectedKey J names rhs Q Y).2) := by
  unfold projectedKey
  rw [pullback_shift, key_shift]

end MaxCutGames.Decoder.TableKeys

/-!
The concrete observation maps of the v2 projected-advice experiment.

The full hidden draw contains the equation occurrence IDs, singleton positions,
projection choices, public row map, and the two sampled tables. The observations
are precisely `(U,A,Tπ,AMπ)` and `(O,A,T,AM)`. The hidden matrix is absent from
both observation types. Changing its kernel-valued part preserves both inputs
and hence every deterministic witness or strategy chosen from those inputs.
-/

namespace MaxCutGames.Decoder.AdviceExperiment

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness

noncomputable section

variable (k : Nat) (Id K W R : Type)
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup W] [Module F2 W]
variable [AddCommGroup R] [Module F2 R]

/-- The first prover's entire information; no singleton-choice or private
matrix field is present. -/
structure FullAdvice where
  occurrences : Fin k → Id
  rowMap : K →ₗ[F2] R
  complement : ActualHomogeneous.E k →ₗ[F2] W
  rows : ActualHomogeneous.E k →ₗ[F2] R

/-- The actual draw before forgetting the hidden projection and private map. -/
structure Draw where
  singletons : Finset (Fin k)
  occurrences : Fin k → Id
  positions : Fin k → PartnerProjection.Slot
  rowMap : K →ₗ[F2] R
  hiddenMatrix : RawPartnerTarget.RawPoint singletons →ₗ[F2] K
  complement : RawPartnerTarget.RawPoint singletons →ₗ[F2] W

variable {k Id K W R}

variable {Name : Type} (names : Id → Fin 3 → Name)

/-- The second prover sees actual equation/variable tags, retaining ordered
block positions but omitting every hidden singleton occurrence ID. -/
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

/-- The same full sampled table used in the unconditional variation comparison.
Its projection choices have not been supplied as extra compared coordinates. -/
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

/-- Replace the entire hidden matrix once, consistently across all overlapping
column events; the row advice remains fixed. -/
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

/-- A selected affine witness is fixed by the first player's observation,
before any hidden matrix on its row fiber is sampled. -/
theorem selectedWitness_changeHidden {Witness : Type*}
    (choose : FullAdvice k Id K W R → Witness) (d : Draw k Id K W R)
    (N : RawPartnerTarget.RawPoint d.singletons →ₗ[F2] d.rowMap.ker) :
    choose (leftObservation rhs (changeHidden d N)) = choose (leftObservation rhs d) := by
  rw [leftObservation_changeHidden]

/-- Every projected answer keeps the actual homogeneous bit. -/
theorem projection_actual_answer (d : Draw k Id K W R)
    (z : ActualHomogeneous.E k) (hz : ActualHomogeneous.tau z = 1) :
    TableKeys.visibleTau d.singletons (projection rhs d z) = 1 := by
  rw [projection, TableKeys.projection_preserves_homogeneous, hz]

end
end MaxCutGames.Decoder.AdviceExperiment

end OAI
