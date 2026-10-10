import Mathlib.Algebra.Module.LinearMap.DivisionRing
import OAI.Computability.UniqueGames.Decoding.AdviceFibersLemmas
import OAI.Computability.UniqueGames.Decoding.PrivateStrategyLemmas
import OAI.Computability.UniqueGames.Decoding.TableKeysGame
import OAI.Computability.UniqueGames.Inverse.RowErasureLemmas
import OAI.Computability.UniqueGames.Reduction.ActualCanonicalLemmas
import OAI.Computability.UniqueGames.Reduction.EncodingLemmas
import OAI.Computability.UniqueGames.Soundness.RawPrivateTable

namespace OAI

section

/-!
# Exact affine-table keys for outer questions

The retained data has one entry at every original block position.  A full entry
contains the equation *occurrence ID*, a singleton entry contains the actual
variable ID, and the first component is the entire reduced affine intercept.
The common coefficient-normalization implementation below is independent of
every latent-gadget existence or inverse theorem.

The explicit binary slope cases justify its use for the rank-zero, rank-one,
and rank-two rule.  In particular, the third-position pullback adds the parity
intercept twice, so exact sharing preserves the intercept as well as the slopes.
-/

namespace UniqueGamesTheorem.Decoder.TableKeys

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
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

section ExactKeys

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

end ExactKeys

end UniqueGamesTheorem.Decoder.TableKeys

end

section

namespace UniqueGamesTheorem.Decoder.TableKeys

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness

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

end UniqueGamesTheorem.Decoder.TableKeys

end

section

/-!
The concrete observation maps of the projected-advice experiment.

The full hidden draw contains the equation occurrence IDs, singleton positions,
projection choices, public row map, and the two sampled tables. The observations
are precisely `(U,A,Tπ,AMπ)` and `(O,A,T,AM)`. The hidden matrix is absent from
both observation types. Changing its kernel-valued part preserves both inputs
and hence every deterministic witness or strategy chosen from those inputs.
-/

namespace UniqueGamesTheorem.Decoder.AdviceExperiment

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness

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
end UniqueGamesTheorem.Decoder.AdviceExperiment

end

section

namespace UniqueGamesTheorem.Decoder.TableKeys

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction

variable {R : Type*} [AddCommGroup R] [Module F2 R] [DecidableEq R]

omit [DecidableEq R] in
theorem slope_rank_zero : Module.finrank F2 (slope (0 : R) 0).range = 0 := by
  rw [(slope_zero_iff 0 0).mpr ⟨rfl, rfl⟩]
  simp

omit [DecidableEq R] in
theorem slope_rank_first (a : R) (ha : a ≠ 0) :
    Module.finrank F2 (slope a 0).range = 1 := by
  have hf : (LinearMap.fst F2 F2 F2) ≠ 0 := by
    intro h
    have hh := LinearMap.congr_fun h (1, 0)
    simp at hh
  have heq : slope a 0 = (LinearMap.fst F2 F2 F2).smulRight a := by
    apply LinearMap.ext
    intro x
    simp [slope]
  rw [heq, LinearMap.range_smulRight_apply hf]
  exact finrank_span_singleton ha

omit [DecidableEq R] in
theorem slope_rank_second (a : R) (ha : a ≠ 0) :
    Module.finrank F2 (slope 0 a).range = 1 := by
  have hf : (LinearMap.snd F2 F2 F2) ≠ 0 := by
    intro h
    have hh := LinearMap.congr_fun h (0, 1)
    simp at hh
  have heq : slope 0 a = (LinearMap.snd F2 F2 F2).smulRight a := by
    apply LinearMap.ext
    intro x
    simp [slope]
  rw [heq, LinearMap.range_smulRight_apply hf]
  exact finrank_span_singleton ha

omit [DecidableEq R] in
theorem slope_rank_third (a : R) (ha : a ≠ 0) :
    Module.finrank F2 (slope a a).range = 1 := by
  let ell := LinearMap.fst F2 F2 F2 + LinearMap.snd F2 F2 F2
  have hf : ell ≠ 0 := by
    intro h
    have hh := LinearMap.congr_fun h (1, 0)
    simp [ell] at hh
  have heq : slope a a = ell.smulRight a := by
    apply LinearMap.ext
    intro x
    simp [slope, ell, add_smul]
  rw [heq, LinearMap.range_smulRight_apply hf]
  exact finrank_span_singleton ha

omit [DecidableEq R] in
theorem slope_rank_two (a d : R) (ha : a ≠ 0) (hd : d ≠ 0) (had : a ≠ d) :
    Module.finrank F2 (slope a d).range = 2 := by
  have h := LinearMap.finrank_range_of_inj (slope_injective a d ha hd had)
  simpa [Module.finrank_prod] using h

/-- These cases exhaust all slopes; no unexamined binary rank-one direction
can accidentally be retained as a full equation block. -/
theorem slope_rank_one_iff (a d : R) :
    Module.finrank F2 (slope a d).range = 1 ↔
      (a ≠ 0 ∧ d = 0) ∨ (a = 0 ∧ d ≠ 0) ∨ (a = d ∧ a ≠ 0) := by
  by_cases ha : a = 0
  · subst a
    by_cases hd : d = 0
    · subst d
      simp [slope_rank_zero]
    · simp [hd, slope_rank_second d hd]
  · by_cases hd : d = 0
    · subst d
      simp [ha, slope_rank_first a ha]
    · by_cases had : a = d
      · subst d
        simp [ha, slope_rank_third a ha]
      · simp [ha, hd, had, slope_rank_two a d ha hd had]

end UniqueGamesTheorem.Decoder.TableKeys

end

section

/-!
Restore actual orbit labels as a total function of the entire reduced key.
The arbitrary value at unrealized orbit bodies is used only to make this
function total; every table queried by the verifier and by the sparse
experiment is proved to be an actual realization.  Folding holds even for
the total extension, because the removed intercept is always restored.
-/

namespace UniqueGamesTheorem.Decoder.TableKeysRestoration

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

section OrbitExtension

variable {Q T : Type} {s d : Nat}

def extendedLabel (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (body : Vector d × T) : Alphabet s :=
  if h : ∃ q, ActualOrbit.body can q = body then label ⟨body, h⟩ else 0

theorem extendedLabel_actual (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (q : Q) :
    extendedLabel can label (ActualOrbit.body can q) = label (ActualOrbit.vertex can q) := by
  rw [extendedLabel, dite_eq_left ⟨q, rfl⟩]
  rfl

/-- Restore the full affine intercept after labeling the orbit body. -/
def restoredData (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (D : Ambient s d × T) : Alphabet s :=
  extendedLabel can label (D.1.2, D.2) + D.1.1

theorem restoredData_actual (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (q : Q) :
    restoredData can label (can q) = ActualOrbit.unfold can label q := by
  change extendedLabel can label (ActualOrbit.body can q) + ActualOrbit.offset can q = _
  rw [extendedLabel_actual]
  rfl

theorem restoredData_shift (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (D : Ambient s d × T) (c : Alphabet s) :
    restoredData can label (D.1 + (c, 0), D.2) = restoredData can label D + c := by
  simp only [restoredData, Prod.fst_add, Prod.snd_add, add_zero]
  exact (add_assoc _ _ _).symm

end OrbitExtension

/-- The actual verifier labeling, viewed as a function of exact affine keys. -/
def keyAnswer (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (D : TableKeys.Key k (Fin S.variables) (Fin S.occurrences) (Ambient s d)) : Alphabet s :=
  restoredData (TableKeysGame.canonical S k s d)
    (TableKeysGame.vertexLabel S k s d labeling) D

theorem keyAnswer_actual (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (q : TableKeysGame.Query S k s d) :
    keyAnswer S k s d labeling (TableKeysGame.canonical S k s d q) =
      TableKeysGame.unfolded S k s d labeling q :=
  restoredData_actual _ _ q

theorem keyAnswer_shift (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (D : TableKeys.Key k (Fin S.variables) (Fin S.occurrences) (Ambient s d))
    (c : Alphabet s) :
    keyAnswer S k s d labeling (D.1 + (c, 0), D.2) = keyAnswer S k s d labeling D + c :=
  restoredData_shift _ _ D c

def projectedAnswer (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k))
    (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) : Alphabet s :=
  keyAnswer S k s d labeling
    (TableKeys.projectedKey J (ActualGame.names S) (ActualGame.rhs S) O Y)

/-- No extra consistency predicate: projected answers equal full-query answers
for every table and every compatible hidden extension. -/
theorem projectedAnswer_pullback (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) :
    projectedAnswer S k s d labeling J
        (RawPrivateTable.supported J (ActualGame.names S) occ slot) Y =
      TableKeysGame.unfolded S k s d labeling
        (occ, Y.comp (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) := by
  unfold projectedAnswer
  rw [TableKeys.projectedKey_pullback]
  exact keyAnswer_actual S k s d labeling
    (occ, Y.comp (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))

/-- The visible table has the exact same affine folding law, with its genuine
homogeneous coordinate rather than an assumed or reconstructed first bit. -/
theorem projectedAnswer_fold (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) (c : Alphabet s) :
    projectedAnswer S k s d labeling J O
        (Y + (TableKeys.visibleTau J).smulRight (c, (0 : Vector d))) =
      projectedAnswer S k s d labeling J O Y + c := by
  unfold projectedAnswer
  rw [TableKeys.projectedKey_shift, keyAnswer_shift]

end

end UniqueGamesTheorem.Decoder.TableKeysRestoration

end

section

/-!
The private row table obtained from an actual single-orbit labeling.  Its
parameters are only the visible question, public row map, visible row value,
and complement table.  Neither a hidden full question nor a selected affine
witness is supplied to its definition.  Affine target intercepts remain
explicit when the matrix is expressed in private kernel coordinates.
-/

namespace UniqueGamesTheorem.Decoder.TableKeysPrivateRow

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open ActualSource

noncomputable section

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

theorem assemble_prod_shift (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (M₀ : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d) (h : A.ker) :
    (AdviceFibers.assemble A M₀ (N + (TableKeys.visibleTau J).smulRight h)).prod T =
      (AdviceFibers.assemble A M₀ N).prod T +
        (TableKeys.visibleTau J).smulRight ((h : Alphabet s), (0 : Vector d)) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change M₀ x + ((N x : Alphabet s) + TableKeys.visibleTau J x • (h : Alphabet s)) =
      (M₀ x + (N x : Alphabet s)) + TableKeys.visibleTau J x • (h : Alphabet s)
    exact (add_assoc _ _ _).symm
  · change T x = T x + TableKeys.visibleTau J x • (0 : Vector d)
    simp

/-- The right player's actual private table, formed from visible row advice. -/
def rowAnswer (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k))
    (Q : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker) : Alphabet s :=
  TableKeysRestoration.projectedAnswer S k s d labeling J Q
    ((AdviceFibers.assemble A (AdviceFibers.observedBase A rows) N).prod T)

/-- Folding on the hidden kernel is a consequence of the exact key action. -/
theorem rowAnswer_fold (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (Q : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker) (h : A.ker) :
    rowAnswer S labeling J Q A rows T (N + (TableKeys.visibleTau J).smulRight h) =
      rowAnswer S labeling J Q A rows T N + (h : Alphabet s) := by
  unfold rowAnswer
  rw [assemble_prod_shift, TableKeysRestoration.projectedAnswer_fold]

/-- At the actual hidden matrix this row table is exactly the projected table
used by the verifier, with the same complement and the same complete key. -/
theorem rowAnswer_actual (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (Q : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d) :
    rowAnswer S labeling J Q A (AdviceFibers.observe A M) T
        (AdviceFibers.hiddenCoordinate A M) =
      TableKeysRestoration.projectedAnswer S k s d labeling J Q (M.prod T) := by
  have h := (AdviceFibers.observationEquiv A).left_inv M
  change AdviceFibers.assemble A (AdviceFibers.observedBase A (AdviceFibers.observe A M))
      (AdviceFibers.hiddenCoordinate A M) = M at h
  unfold rowAnswer
  rw [h]

/-- This intercept is determined once the visible base and affine witness are
fixed; it is not silently erased when decoding from a row fiber. -/
def targetIntercept (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (z : RawPartnerTarget.RawPoint J) (u : Alphabet s) : Alphabet s :=
  AdviceFibers.observedBase A rows z + u

theorem affine_target_on_row (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)
    (z : RawPartnerTarget.RawPoint J) (u : Alphabet s) :
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows) N z + u =
      (N z : Alphabet s) + targetIntercept J A rows z u :=
  AdviceFibers.assemble_affine_target A (AdviceFibers.observedBase A rows) N z u

end

end UniqueGamesTheorem.Decoder.TableKeysPrivateRow

end

section

/-!
# Decoding an actual transferred column slice

The point `Mstar` used to parametrize a transferred slice is distinct from the
canonical visible row base `observedBase A rows`.  The right strategy uses only
the latter.  Their kernel-valued difference appears solely in the analysis.
The exact quotient equivalence transports uniform slice agreement, including
the affine offset, to the conditional private-decoder theorem.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.TransferredDecoding

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open ActualSource
open PrivateFourier PrivateStrategy
open scoped BigOperators Classical

open UniqueGamesTheorem.Inverse

attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

/-- Equality indicators depend on their propositions, not on the chosen
computable or classical decision procedures. Both deciders are explicit. -/
theorem indicator_congr (P Q : Prop) (dP : Decidable P) (dQ : Decidable Q)
    (h : P ↔ Q) : @ite ℝ P dP 1 0 = @ite ℝ Q dQ 1 0 := by
  cases propext h
  cases Subsingleton.elim dP dQ
  rfl

section Rebase

variable {E K R : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup K] [Module F2 K] [AddCommGroup R] [Module F2 R]

/-- The slice origin, expressed relative to the fixed visible row base. -/
def privateOrigin (A : K →ₗ[F2] R) (rows : AdviceFibers.ObservedRow (E := E) A)
    (Mstar : E →ₗ[F2] K) (hstar : A.comp Mstar = rows.val) : E →ₗ[F2] A.ker :=
  AdviceFibers.kernelDifference A rows.val (AdviceFibers.observedBase A rows)
    (AdviceFibers.observedBase_property A rows) ⟨Mstar, hstar⟩

/-- Rebase the complete quotient parametrization without changing its matrices. -/
theorem assemble_privateOrigin (A : K →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := E) A)
    (Mstar : E →ₗ[F2] K) (hstar : A.comp Mstar = rows.val)
    (Q : Submodule F2 E) (L : (E ⧸ Q) →ₗ[F2] A.ker) :
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows)
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
        (RowErasureSliceQuotient.equiv A Q Mstar L).val := by
  ext x
  change AdviceFibers.observedBase A rows x +
      ((Mstar x - AdviceFibers.observedBase A rows x) + (L (Q.mkQ x) : K)) =
    Mstar x + (L (Q.mkQ x) : K)
  rw [← add_assoc]
  congr 1
  rw [add_comm, sub_add_cancel]

end Rebase

section ActualSlice

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

/-- A default actual projected answer depends only on the displayed positions. -/
def visibleFallback (J : Finset (Fin k)) : ActualAnswer (TableKeys.visibleTau J) :=
  ⟨Pi.single none 1, by simp [TableKeys.visibleTau]⟩

/-- Exact transport from the actual conditional matrix slice to the private
Fourier coordinates.  `targetIntercept` uses the visible base, not `Mstar`. -/
theorem actual_slice_agreement_eq_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (Mstar : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (hstar : A.comp Mstar = rows.val) (Q : Submodule F2 (RawPartnerTarget.RawPoint J))
    [Fintype ((RawPartnerTarget.RawPoint J ⧸ Q) →ₗ[F2] A.ker)]
    [Fintype (RowErasureSliceQuotient.AffineSlice A Q Mstar)]
    (z' : RawPartnerTarget.RawPoint J) (u : Alphabet s) :
    (𝔼 M : RowErasureSliceQuotient.AffineSlice A Q Mstar,
      if TableKeysRestoration.projectedAnswer S k s d labeling J O (M.val.prod T) =
        M.val z' + u then (1 : ℝ) else 0) =
    𝔼 L : (RawPartnerTarget.RawPoint J ⧸ Q) →ₗ[F2] A.ker,
      if TableKeysPrivateRow.rowAnswer S labeling J O A rows T
          (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
        TableKeysPrivateRow.targetIntercept J A rows z' u +
          ((privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' : Alphabet s)
      then (1 : ℝ) else 0 := by
  rw [← RowErasureSliceQuotient.expect_equiv A Q Mstar]
  apply Finset.expect_congr rfl
  intro L _
  rw [← assemble_privateOrigin A rows Mstar hstar Q L]
  change (if TableKeysPrivateRow.rowAnswer S labeling J O A rows T
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) =
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows)
      (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' + u
    then (1 : ℝ) else 0) = _
  rw [TableKeysPrivateRow.affine_target_on_row J A rows
    (privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z' u]
  rw [add_comm (((privateOrigin A rows Mstar hstar + L.comp Q.mkQ) z') : Alphabet s)
    (TableKeysPrivateRow.targetIntercept J A rows z' u)]

/-- Private policies for an actual restored labeling satisfy the conditional
decoding bound on every transferred good slice.  Folding and first-bit
preservation come from their concrete constructions, not additional premises. -/
theorem actual_transferred_decoding (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (Mstar : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (hstar : A.comp Mstar = rows.val)
    (Z : Submodule F2 (ActualHomogeneous.E k)) [Fintype Z]
    (z : ActualHomogeneous.E k) (hz : ActualHomogeneous.tau z = 1)
    (u : Alphabet s) (α : ℝ) (hα : 0 ≤ α) (ℓ r : ℕ)
    (hH : Module.finrank F2 A.ker ≤ ℓ) (hZ : Module.finrank F2 Z ≤ r)
    [Fintype A.ker]
    [Fintype (RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)]
    [Fintype (A.ker →ₗ[F2] RawPartnerTarget.RawPoint J)]
    [Fintype (A.ker →ₗ[F2] Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))]
    [Fintype ((RawPartnerTarget.RawPoint J ⧸
      Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) →ₗ[F2] A.ker)]
    [Fintype (RowErasureSliceQuotient.AffineSlice A
      (Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) Mstar)]
    (hsmall : 1 / (Fintype.card A.ker : ℝ) ≤ α / 8)
    (hagreement : α / 4 ≤
      𝔼 M : RowErasureSliceQuotient.AffineSlice A
          (Z.map (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) Mstar,
        if TableKeysRestoration.projectedAnswer S k s d labeling J
            (RawPrivateTable.supported J (ActualGame.names S) occ slot) (M.val.prod T) =
          M.val (RawPrivateTable.projection J (ActualGame.rhs S) occ slot z) + u
        then (1 : ℝ) else 0) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (ℓ * r) / (2 : ℝ) ^ r ≤
      PrivateStrategy.conditionalAgreement Z z ActualHomogeneous.tau hz
        (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)
        (TableKeysPrivateRow.rowAnswer S labeling J
          (RawPrivateTable.supported J (ActualGame.names S) occ slot) A rows T)
        A.ker.subtype (TableKeys.visibleTau J) (visibleFallback J) := by
  let π := RawPrivateTable.projection J (ActualGame.rhs S) occ slot
  let O := RawPrivateTable.supported J (ActualGame.names S) occ slot
  have hτ : (TableKeys.visibleTau J).comp π = ActualHomogeneous.tau := by
    apply LinearMap.ext
    intro x
    exact TableKeys.projection_preserves_homogeneous J (ActualGame.rhs S) occ slot x
  apply conditionalAgreement_from_slice Z z ActualHomogeneous.tau hz π
    (privateOrigin A rows Mstar hstar)
    (TableKeysPrivateRow.rowAnswer S labeling J O A rows T)
    A.ker.subtype Subtype.val_injective (TableKeys.visibleTau J) (visibleFallback J) hτ
    (TableKeysPrivateRow.rowAnswer_fold S labeling J O A rows T)
    (TableKeysPrivateRow.targetIntercept J A rows (π z) u)
    α hα ℓ r hH hZ hsmall
  apply hagreement.trans_eq
  calc
    _ = _ := actual_slice_agreement_eq_private S labeling J O A rows T Mstar hstar
      (Z.map π) (π z) u
    _ = _ := by
      apply Finset.expect_congr rfl
      intro L _
      exact indicator_congr _ _ _ _ Iff.rfl

end ActualSlice

end UniqueGamesTheorem.Decoder.TransferredDecoding

end

end

end OAI
