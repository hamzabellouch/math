import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Basic.Real.Basic
import OAI.Computability.UniqueGames.Reduction.ActualCanonicalLemmas
import OAI.Computability.UniqueGames.Soundness.ConditionalLocality
import OAI.Computability.UniqueGames.Soundness.LinearMapDensityLemmas
import OAI.Computability.UniqueGames.Soundness.PartnerMapCoordinates

namespace OAI

section

/-! Canonical-row descent for every actual partner linear map. -/

namespace UniqueGamesTheorem.Soundness.ActualCanonicalPullback

open scoped BigOperators
open PartnerProjection PartnerMapCoordinates
open ConditionalIncidences
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction

noncomputable section

variable {k : Nat} (rhsB : Fin k → Bool) (J : Finset (Fin k))
variable (R : Type) [AddCommGroup R] [Module F2 R]

def selectedFree (b : Fin k → F2) (slot : Fin k → Slot)
    (v : ActualHomogeneous.E k) (j : Fin k) : F2 :=
  match slot j with
  | .first => (v.2 j).1
  | .second => (v.2 j).2
  | .third => b j * v.1 + (v.2 j).1 + (v.2 j).2

def ambientCoefficients (gamma : RawCoefficients J R) (slot : Fin k → Slot)
    (j : Fin k) (i : Fin 3) : R :=
  if hj : j ∈ J then
    if i = ConcreteExtraction.slotIndex (slot j) then gamma (some (.inr ⟨j,hj⟩)) else 0
  else if i = 0 then gamma (some (.inl (⟨j,hj⟩,0)))
    else if i = 1 then gamma (some (.inl (⟨j,hj⟩,1))) else 0

def freePullback (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualHomogeneous.E k →ₗ[F2] R :=
  (mapEquiv rhsB J R gamma).comp
    ((PartnerLinear.projection rhsB (activeOf J) slot).comp
      (PartnerLinear.sourceLinearEquiv rhsB).symm.toLinearMap)

theorem ofBit_and (a b : Bool) : ofBit (a && b) = ofBit a * ofBit b := by
  cases a <;> cases b <;> decide

theorem inverse_homogeneous (v : ActualHomogeneous.E k) :
    ofBit (((PartnerLinear.sourceLinearEquiv rhsB).symm v).homogeneous) = v.1 :=
  ofBit_toBit _

theorem inverse_first (v : ActualHomogeneous.E k) (j : Fin k) :
    ofBit ((((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j).first) =
      (v.2 j).1 := ofBit_toBit _

theorem inverse_second (v : ActualHomogeneous.E k) (j : Fin k) :
    ofBit ((((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j).second) =
      (v.2 j).2 := ofBit_toBit _

theorem inverse_retained_free (v : ActualHomogeneous.E k) (j : Fin k)
    (slot : Fin k → Slot) :
    ofBit (retained (slot j)
      (((PartnerLinear.sourceLinearEquiv rhsB).symm v).coordinates j)) =
        selectedFree (fun j => ofBit (rhsB j)) slot v j := by
  unfold selectedFree
  cases hslot : slot j with
  | first => exact ofBit_toBit _
  | second => exact ofBit_toBit _
  | third =>
    change ofBit (((rhsB j && toBit v.1).xor (toBit (v.2 j).1)).xor
      (toBit (v.2 j).2)) = ofBit (rhsB j) * v.1 + (v.2 j).1 + (v.2 j).2
    rw [ofBit_xor, ofBit_xor, ofBit_and, ofBit_toBit, ofBit_toBit, ofBit_toBit]

theorem freePullback_expansion (gamma : RawCoefficients J R)
    (slot : Fin k → Slot) (v : ActualHomogeneous.E k) :
    freePullback rhsB J R gamma slot v =
      v.1 • gamma none +
        (∑ j : PositionOutside J, ((v.2 j.val).1 • gamma (some (.inl (j,0))) +
          (v.2 j.val).2 • gamma (some (.inl (j,1))))) +
        ∑ j : PositionInside J, selectedFree (fun j => ofBit (rhsB j)) slot v j.val •
          gamma (some (.inr j)) := by
  change mapEquiv rhsB J R gamma
    (PartnerLinear.projection rhsB (activeOf J) slot
      ((PartnerLinear.sourceLinearEquiv rhsB).symm v)) = _
  rw [pullback_expansion]
  simp only [inverse_homogeneous, inverse_first, inverse_second, inverse_retained_free]

def outsideInsideEquiv : (PositionOutside J ⊕ PositionInside J) ≃ Fin k where
  toFun j := Sum.elim Subtype.val Subtype.val j
  invFun j := if hj : j ∈ J then Sum.inr ⟨j,hj⟩ else Sum.inl ⟨j,hj⟩
  left_inv j := by
    cases j with
    | inl j => simp [j.property]
    | inr j => simp [j.property]
  right_inv j := by
    by_cases hj : j ∈ J <;> simp [hj]

omit [Module F2 R] in
theorem sum_outside_inside (f : PositionOutside J → R) (g : PositionInside J → R) :
    (∑ j, f j) + (∑ j, g j) =
      ∑ j : Fin k, if hj : j ∈ J then g ⟨j,hj⟩ else f ⟨j,hj⟩ := by
  rw [← (outsideInsideEquiv J).sum_comp]
  rw [Fintype.sum_sum_type]
  congr 1 <;> apply Finset.sum_congr rfl
  · intro j _
    simp [outsideInsideEquiv, j.property]
  · intro j _
    simp [outsideInsideEquiv, j.property]

theorem raw_represents (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualCanonical.Represents (fun j => ofBit (rhsB j)) (gamma none)
      (ambientCoefficients J R gamma slot) (freePullback rhsB J R gamma slot) := by
  intro v
  let f : PositionOutside J → R := fun j =>
    (v.2 j.val).1 • gamma (some (.inl (j,0))) +
      (v.2 j.val).2 • gamma (some (.inl (j,1)))
  let g : PositionInside J → R := fun j =>
    selectedFree (fun j => ofBit (rhsB j)) slot v j.val • gamma (some (.inr j))
  have hs : (∑ j, f j) + (∑ j, g j) =
      ∑ j : Fin k, ((v.2 j).1 • ambientCoefficients J R gamma slot j 0 +
        (v.2 j).2 • ambientCoefficients J R gamma slot j 1 +
        (ofBit (rhsB j) * v.1 + (v.2 j).1 + (v.2 j).2) •
          ambientCoefficients J R gamma slot j 2) := by
    rw [sum_outside_inside]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · cases hslot : slot j <;>
        simp [g, ambientCoefficients, selectedFree, hj, hslot, ConcreteExtraction.slotIndex]
    · simp [f, ambientCoefficients, hj]
  calc
    ActualCanonical.ambientEval _ _ _ v = v.1 • gamma none + ((∑ j, f j) + (∑ j, g j)) :=
      congrArg (fun z : R => v.1 • gamma none + z) hs.symm
    _ = (v.1 • gamma none + (∑ j, f j)) + (∑ j, g j) := (add_assoc _ _ _).symm
    _ = freePullback rhsB J R gamma slot v :=
      (freePullback_expansion rhsB J R gamma slot v).symm

theorem canonical_raw_pullback [DecidableEq R] {Id Name : Type} [DecidableEq Id] [DecidableEq Name]
    (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualCanonical.canonical occ names rhs
      (freePullback (fun j => toBit (rhs (occ j))) J R gamma slot) =
    ActualCanonical.data occ names rhs (gamma none) (ambientCoefficients J R gamma slot) := by
  apply ActualCanonical.canonical_eq_of_extension
  simpa only [ofBit_toBit] using raw_represents (fun j => toBit (rhs (occ j))) J R gamma slot

omit [Module F2 R] in
theorem ambientCoefficients_single (gamma : RawCoefficients J R) (slot : Fin k → Slot)
    (j : Fin k) (hj : j ∈ J) :
    ambientCoefficients J R gamma slot j =
      ActualCanonical.singletonTriple (ConcreteExtraction.slotIndex (slot j))
        (gamma (some (.inr ⟨j,hj⟩))) := by
  funext i
  simp [ambientCoefficients, hj, ActualCanonical.singletonTriple, Pi.single_apply]

omit [Module F2 R] in
theorem ambientCoefficients_full_eq (gamma : RawCoefficients J R)
    (slot slot' : Fin k → Slot) (j : Fin k) (hj : j ∉ J) :
    ambientCoefficients J R gamma slot j = ambientCoefficients J R gamma slot' j := by
  funext i
  simp [ambientCoefficients, hj]

/-- Raw canonical data is determined by the full displayed occurrences and
    retained variable names. Hidden single occurrences and slot indices vanish. -/
theorem raw_data_locality [DecidableEq R] {Id Name : Type}
    (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (gamma : RawCoefficients J R)
    (hfull : ∀ j, j ∉ J → occ j = occ' j)
    (hsingle : ∀ j, j ∈ J → names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j))) :
    ActualCanonical.data occ names rhs (gamma none) (ambientCoefficients J R gamma slot) =
      ActualCanonical.data occ' names rhs (gamma none) (ambientCoefficients J R gamma slot') := by
  apply Prod.ext
  · change gamma none + _ = gamma none + _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ J
    · rw [ambientCoefficients_single J R gamma slot j hj,
        ambientCoefficients_single J R gamma slot' j hj]
      simp only [ActualCanonical.singleton_global_adjustment]
    · rw [hfull j hj, ambientCoefficients_full_eq J R gamma slot slot' j hj]
  · funext j
    change ActualCanonical.record names (occ j) (ambientCoefficients J R gamma slot j) =
      ActualCanonical.record names (occ' j) (ambientCoefficients J R gamma slot' j)
    by_cases hj : j ∈ J
    · rw [ambientCoefficients_single J R gamma slot j hj,
        ambientCoefficients_single J R gamma slot' j hj]
      exact ActualCanonical.singleton_locality names _ _ _ _ _ (hsingle j hj)
    · rw [hfull j hj, ambientCoefficients_full_eq J R gamma slot slot' j hj]

/-- Lemma 6.2 for the actual pullbacks in the shared F₂ coordinate model. -/
theorem canonical_private_input_locality [DecidableEq R]
    {Id Name : Type} [DecidableEq Id] [DecidableEq Name]
    (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (gamma : RawCoefficients J R)
    (hfull : ∀ j, j ∉ J → occ j = occ' j)
    (hsingle : ∀ j, j ∈ J → names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j))) :
    ActualCanonical.canonical occ names rhs
      (freePullback (fun j => toBit (rhs (occ j))) J R gamma slot) =
    ActualCanonical.canonical occ' names rhs
      (freePullback (fun j => toBit (rhs (occ' j))) J R gamma slot') := by
  rw [canonical_raw_pullback, canonical_raw_pullback]
  exact raw_data_locality J R names rhs occ occ' slot slot' gamma hfull hsingle

end
end UniqueGamesTheorem.Soundness.ActualCanonicalPullback

end

section

/-! Exact transport from genuine binary linear maps to the complete private rows
used by the conditional game. -/

namespace UniqueGamesTheorem.Soundness.BinaryRowTransport
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open ConditionalIncidences PartnerMapCoordinates

noncomputable section
attribute [local instance] Classical.propDecidable
variable {Q : Type}

def rowBits (v : Q → F2) : ZeroInformation.Bits Q := fun q => toBit (v q)

theorem rowBits_zero : rowBits (0 : Q → F2) = ZeroInformation.zero := by
  funext q
  change toBit (0 : F2) = false
  decide

theorem rowBits_add (v w : Q → F2) : rowBits (v+w) = ZeroInformation.add (rowBits v) (rowBits w) := by
  funext q
  exact toBit_add _ _

theorem rowBits_smul (b : Bool) (v : Q → F2) :
    rowBits (ofBit b • v) = ZeroInformation.scale (rowBits v) b := by
  cases b <;> funext q <;> simp [rowBits, ZeroInformation.scale, ofBit, toBit]

theorem rowBits_list_sum {P : Type} (xs : List P) (f : P → Q → F2) :
    rowBits (xs.map f |>.sum) = ZeroInformation.rowSum xs (fun j => rowBits (f j)) := by
  induction xs with
  | nil => exact rowBits_zero
  | cons j xs ih =>
    simp only [List.map_cons, List.sum_cons, rowBits_add, ih, ZeroInformation.rowSum, List.foldr_cons]

theorem rowBits_sum {P : Type} [Fintype P] (f : P → Q → F2) :
    rowBits (∑ j, f j) = ZeroInformation.rowSum Finset.univ.toList (fun j => rowBits (f j)) := by
  rw [← Finset.sum_map_toList]
  exact rowBits_list_sum _ _

def rowBitsEquiv : (Q → F2) ≃ ZeroInformation.Bits Q where
  toFun := rowBits
  invFun v := fun q => ofBit (v q)
  left_inv v := by funext q; exact ofBit_toBit _
  right_inv v := by funext q; exact toBit_ofBit _

theorem rowBits_eq_zero (v : Q → F2) : rowBits v = ZeroInformation.zero ↔ v = 0 := by
  rw [← rowBits_zero]
  constructor
  · intro h
    apply (rowBitsEquiv (Q := Q)).injective
    exact h
  · intro h
    rw [h]

def rowCoefficients {P : Type} (J : Finset P) (gamma : RawCoefficients J (Q → F2)) :
    RawCoefficients J (ZeroInformation.Bits Q) := fun slot => rowBits (gamma slot)

theorem zeroSet_rowCoefficients {P : Type} [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (J : Finset P) (gamma : RawCoefficients J (Q → F2)) :
    zeroSet J (rowCoefficients J gamma) = zeroSet J gamma := by
  ext j
  simp only [mem_zeroSet, rowCoefficients]
  apply exists_congr
  intro hj
  change (rowBits (gamma (some (.inr ⟨j,hj⟩))) = ZeroInformation.zero) ↔
    (gamma (some (.inr ⟨j,hj⟩)) = 0)
  exact rowBits_eq_zero _

theorem actual_pullbackRow {k : Nat} [Fintype Q] [DecidableEq Q]
    (rhs : Fin k → Bool) (J : Finset (Fin k))
    (gamma : RawCoefficients J (Q → F2)) (slot : Fin k → PartnerProjection.Slot)
    (x : PartnerProjection.SourcePoint rhs) :
    rowBits (mapEquiv rhs J (Q → F2) gamma
      (PartnerLinear.projection rhs (activeOf J) slot x)) =
    ZeroInformation.pullbackRow Finset.univ.toList (membershipBool J)
      ((rowCoefficients J gamma) none)
      (fullCoefficient J (rowCoefficients J gamma) 0)
      (fullCoefficient J (rowCoefficients J gamma) 1)
      (singleCoefficient J (rowCoefficients J gamma))
      (fun j => ConcreteExtraction.slotIndex (slot j)) x.homogeneous
      (fun j => ConcreteExtraction.tripleCoordinates (x.coordinates j)) := by
  let f : PositionOutside J → Q → F2 := fun j =>
    ofBit (x.coordinates j.val).first • gamma (some (.inl (j,0))) +
      ofBit (x.coordinates j.val).second • gamma (some (.inl (j,1)))
  let g : PositionInside J → Q → F2 := fun j =>
    ofBit (PartnerProjection.retained (slot j.val) (x.coordinates j.val)) • gamma (some (.inr j))
  rw [pullback_expansion]
  change rowBits ((ofBit x.homogeneous • gamma none + ∑ j, f j) + ∑ j, g j) = _
  rw [add_assoc, ActualCanonicalPullback.sum_outside_inside J (Q → F2) f g,
    rowBits_add, rowBits_smul, rowBits_sum]
  unfold ZeroInformation.pullbackRow
  congr 1
  apply ZeroInformation.rowSum_congr
  intro j
  by_cases hj : j ∈ J
  · simp [g, hj, membershipBool, singleCoefficient, rowCoefficients,
      rowBits_smul, ConcreteExtraction.retained_coordinates]
  · simp [f, hj, membershipBool, fullCoefficient, rowCoefficients,
      rowBits_add, rowBits_smul, ConcreteExtraction.tripleCoordinates]

theorem actual_partnerRow {k : Nat} [Fintype Q] [DecidableEq Q]
    (rhs : Fin k → Bool) (J : Finset (Fin k))
    (gamma : RawCoefficients J (Q → F2))
    (y : PartnerProjection.PartnerPoint rhs (activeOf J)) :
    rowBits (mapEquiv rhs J (Q → F2) gamma y) =
    ZeroInformation.partnerRow Finset.univ.toList (membershipBool J)
      ((rowCoefficients J gamma) none)
      (fullCoefficient J (rowCoefficients J gamma) 0)
      (fullCoefficient J (rowCoefficients J gamma) 1)
      (singleCoefficient J (rowCoefficients J gamma)) y.homogeneous
      (fun j => ConcreteExtraction.tripleCoordinates (y.full j)) y.single := by
  let f : PositionOutside J → Q → F2 := fun j =>
    ofBit (y.full j.val).first • gamma (some (.inl (j,0))) +
      ofBit (y.full j.val).second • gamma (some (.inl (j,1)))
  let g : PositionInside J → Q → F2 := fun j =>
    ofBit (y.single j.val) • gamma (some (.inr j))
  rw [mapEquiv_expansion]
  change rowBits ((ofBit y.homogeneous • gamma none + ∑ j, f j) + ∑ j, g j) = _
  rw [add_assoc, ActualCanonicalPullback.sum_outside_inside J (Q → F2) f g,
    rowBits_add, rowBits_smul, rowBits_sum]
  unfold ZeroInformation.partnerRow
  congr 1
  apply ZeroInformation.rowSum_congr
  intro j
  by_cases hj : j ∈ J
  · simp [g, hj, membershipBool, singleCoefficient, rowCoefficients, rowBits_smul]
  · simp [f, hj, membershipBool, fullCoefficient, rowCoefficients,
      rowBits_add, rowBits_smul, ConcreteExtraction.tripleCoordinates]

def rawBitsEquiv {P : Type} (J : Finset P) :
    RawCoefficients J (Q → F2) ≃ RawCoefficients J (ZeroInformation.Bits Q) :=
  Equiv.piCongrRight (fun _ => rowBitsEquiv)

def bitsMapEquiv {P : Type} [Fintype P] [DecidableEq P]
    (rhs : P → Bool) (J : Finset P) :
    RawCoefficients J (ZeroInformation.Bits Q) ≃
      (PartnerProjection.PartnerPoint rhs (activeOf J) →ₗ[F2] (Q → F2)) :=
  (rawBitsEquiv J).symm.trans (mapEquiv rhs J (Q → F2)).toEquiv

/-- Uniform raw bit coefficients are exactly uniform genuine partner row maps. -/
theorem uniform_bit_coefficients_maps {P : Type} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] (rhs : P → Bool) (J : Finset P)
    (H : (PartnerProjection.PartnerPoint rhs (activeOf J) →ₗ[F2] (Q → F2)) → ℝ) :
    (𝔼 gamma : RawCoefficients J (ZeroInformation.Bits Q), H (bitsMapEquiv rhs J gamma)) =
      𝔼 Y, H Y :=
  Fintype.expect_equiv (bitsMapEquiv rhs J) _ H (fun _ => rfl)

end
end UniqueGamesTheorem.Soundness.BinaryRowTransport

end

section

/-! A partner target whose coordinates depend only on the displayed full/single
positions. It does not contain hidden occurrence identities or right-hand sides. -/

namespace UniqueGamesTheorem.Soundness.RawPartnerTarget
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open PartnerProjection PartnerMapCoordinates ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev RawPoint {k : Nat} (J : Finset (Fin k)) := RawSlot J → F2

variable {k : Nat} {R : Type} [AddCommGroup R] [Module F2 R]

def rawProjection (rhsB : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) : ActualHomogeneous.E k →ₗ[F2] RawPoint J :=
  (pointEquiv rhsB J).toLinearMap.comp
    ((PartnerLinear.projection rhsB (activeOf J) slot).comp
      (PartnerLinear.sourceLinearEquiv rhsB).symm.toLinearMap)

def gammaOfRawMap (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] R) :
    RawCoefficients J R := fun s => Y (Pi.single s 1)

theorem rawPoint_decomposition (J : Finset (Fin k)) (v : RawPoint J) :
    (∑ s, v s • Pi.single s (1 : F2)) = v := by
  funext t
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, mul_ite]

theorem rawMap_expansion (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] R)
    (v : RawPoint J) : Y v = ∑ s, v s • gammaOfRawMap J Y s := by
  calc
    Y v = Y (∑ s, v s • Pi.single s (1 : F2)) :=
      congrArg Y (rawPoint_decomposition J v).symm
    _ = _ := by simp [gammaOfRawMap]

theorem rawMap_on_partner (rhsB : Fin k → Bool) (J : Finset (Fin k))
    (Y : RawPoint J →ₗ[F2] R) (y : PartnerPoint rhsB (activeOf J)) :
    Y (pointEquiv rhsB J y) = mapEquiv rhsB J R (gammaOfRawMap J Y) y := by
  rw [mapEquiv_apply]
  exact rawMap_expansion J Y (pointEquiv rhsB J y)

theorem rawMap_pullback (rhsB : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (Y : RawPoint J →ₗ[F2] R) :
    Y.comp (rawProjection rhsB J slot) =
      ActualCanonicalPullback.freePullback rhsB J R (gammaOfRawMap J Y) slot := by
  apply LinearMap.ext
  intro x
  change Y (pointEquiv rhsB J
      (PartnerLinear.projection rhsB (activeOf J) slot
        ((PartnerLinear.sourceLinearEquiv rhsB).symm x))) =
    mapEquiv rhsB J R (gammaOfRawMap J Y)
      (PartnerLinear.projection rhsB (activeOf J) slot
        ((PartnerLinear.sourceLinearEquiv rhsB).symm x))
  exact rawMap_on_partner rhsB J Y _

end
end UniqueGamesTheorem.Soundness.RawPartnerTarget

end

section

/-! Local extraction of the genuine linear row maps from complete supplied inputs. -/

namespace UniqueGamesTheorem.Soundness.ActualInputRows
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open ConditionalIncidences PartnerMapCoordinates RawPartnerTarget BinaryRowTransport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Q Id Name : Type}

def restrictedFirst (rhs : Id → Bool)
    (qa : ZeroInformation.FirstInput (Fin k) Q Id) (x : ActualHomogeneous.E k) : Q → F2 :=
  let p := (PartnerLinear.sourceLinearEquiv (fun j => rhs (qa.question j))).symm x
  fun q => ofBit (qa.row p.homogeneous
    (fun j => ConcreteExtraction.tripleCoordinates (p.coordinates j)) q)

def firstMap (rhs : Id → Bool) (qa : ZeroInformation.FirstInput (Fin k) Q Id) :
    ActualHomogeneous.E k →ₗ[F2] (Q → F2) :=
  if h : ∃ Z : ActualHomogeneous.E k →ₗ[F2] (Q → F2),
    ∀ x, Z x = restrictedFirst rhs qa x then Classical.choose h else 0

theorem firstMap_eq (rhs : Id → Bool) (qa : ZeroInformation.FirstInput (Fin k) Q Id)
    (Z : ActualHomogeneous.E k →ₗ[F2] (Q → F2))
    (hZ : ∀ x, restrictedFirst rhs qa x = Z x) : firstMap rhs qa = Z := by
  have h : ∃ W : ActualHomogeneous.E k →ₗ[F2] (Q → F2),
      ∀ x, W x = restrictedFirst rhs qa x := ⟨Z, fun x => (hZ x).symm⟩
  unfold firstMap
  rw [dite_eq_left h]
  exact LinearMap.ext (fun x => (Classical.choose_spec h x).trans (hZ x))

def restrictedSecond (J : Finset (Fin k))
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name) (v : RawPoint J) : Q → F2 :=
  let y := (pointEquiv (fun _ : Fin k => false) J).symm v
  fun q => ofBit (qb.row y.homogeneous
    (fun j => ConcreteExtraction.tripleCoordinates (y.full j)) y.single q)

def secondMap (J : Finset (Fin k))
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name) : RawPoint J →ₗ[F2] (Q → F2) :=
  if h : ∃ Y : RawPoint J →ₗ[F2] (Q → F2),
    ∀ v, Y v = restrictedSecond J qb v then Classical.choose h else 0

theorem secondMap_eq (J : Finset (Fin k))
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name) (Y : RawPoint J →ₗ[F2] (Q → F2))
    (hY : ∀ v, restrictedSecond J qb v = Y v) : secondMap J qb = Y := by
  have h : ∃ W : RawPoint J →ₗ[F2] (Q → F2),
      ∀ v, W v = restrictedSecond J qb v := ⟨Y, fun v => (hY v).symm⟩
  unfold secondMap
  rw [dite_eq_left h]
  exact LinearMap.ext (fun v => (Classical.choose_spec h v).trans (hY v))

/-- The first player's extraction on the actual sampled input equals `Y π`.
There is no assumption that an arbitrary input row is linear. -/
theorem firstMap_actual [Fintype Q] [DecidableEq Q]
    (J : Finset (Fin k)) (rhs : Id → Bool) (occ : Fin k → Id)
    (slot : Fin k → PartnerProjection.Slot) (Y : RawPoint J →ₗ[F2] (Q → F2)) :
    firstMap rhs (actualFirst J (rowCoefficients J (gammaOfRawMap J Y))
      (fun j => (occ j, ConcreteExtraction.slotIndex (slot j)))) =
      Y.comp (rawProjection (fun j => rhs (occ j)) J slot) := by
  apply firstMap_eq
  intro x
  let p := (PartnerLinear.sourceLinearEquiv (fun j => rhs (occ j))).symm x
  have h := actual_pullbackRow (fun j => rhs (occ j)) J (gammaOfRawMap J Y) slot p
  rw [← rawMap_on_partner (fun j => rhs (occ j)) J Y] at h
  funext q
  have he := congrArg ofBit (congrFun h q).symm
  simp only [rowBits, ofBit_toBit, restrictedFirst, actualFirst,
    ZeroInformation.firstInput, rawProjection, p, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap] at he ⊢
  convert he using 1
  congr 5

/-- The second player's extraction equals the genuine supplied raw target map. -/
theorem secondMap_actual [Fintype Q] [DecidableEq Q]
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (draw : Draw (Fin k) Id)
    (Y : RawPoint J →ₗ[F2] (Q → F2)) :
    secondMap J (actualSecond J names (rowCoefficients J (gammaOfRawMap J Y)) draw) = Y := by
  apply secondMap_eq
  intro v
  let y := (pointEquiv (fun _ : Fin k => false) J).symm v
  have h := actual_partnerRow (fun _ : Fin k => false) J (gammaOfRawMap J Y) y
  rw [← rawMap_on_partner (fun _ : Fin k => false) J Y] at h
  have hy : pointEquiv (fun _ : Fin k => false) J y = v :=
    (pointEquiv (fun _ : Fin k => false) J).apply_symm_apply v
  rw [hy] at h
  funext q
  have he := congrArg ofBit (congrFun h q).symm
  simpa only [rowBits, ofBit_toBit, restrictedSecond, actualSecond,
    ZeroInformation.secondInput, y] using he

end
end UniqueGamesTheorem.Soundness.ActualInputRows

end

section

/-! Exact uniform sampling of linear maps on the common private coordinate target. -/

namespace UniqueGamesTheorem.Soundness.RawMapLaw
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open ConditionalIncidences PartnerMapCoordinates RawPartnerTarget BinaryRowTransport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} (J : Finset (Fin k)) (R : Type) [AddCommGroup R] [Module F2 R]

def rawMap (gamma : RawCoefficients J R) : RawPoint J →ₗ[F2] R :=
  (mapEquiv (fun _ : Fin k => false) J R gamma).comp
    (pointEquiv (fun _ : Fin k => false) J).symm.toLinearMap

theorem coefficients_rawMap (gamma : RawCoefficients J R) :
    gammaOfRawMap J (rawMap J R gamma) = gamma := by
  apply (mapEquiv (fun _ : Fin k => false) J R).injective
  apply LinearMap.ext
  intro y
  rw [← rawMap_on_partner]
  change mapEquiv (fun _ : Fin k => false) J R gamma
    ((pointEquiv (fun _ : Fin k => false) J).symm
      (pointEquiv (fun _ : Fin k => false) J y)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem rawMap_coefficients (Y : RawPoint J →ₗ[F2] R) :
    rawMap J R (gammaOfRawMap J Y) = Y := by
  apply LinearMap.ext
  intro v
  have h := rawMap_on_partner (fun _ : Fin k => false) J Y
    ((pointEquiv (fun _ : Fin k => false) J).symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

def rawMapEquiv : RawCoefficients J R ≃ (RawPoint J →ₗ[F2] R) where
  toFun := rawMap J R
  invFun := gammaOfRawMap J
  left_inv := coefficients_rawMap J R
  right_inv := rawMap_coefficients J R

instance rawMapsFintype [Fintype R] : Fintype (RawPoint J →ₗ[F2] R) := by
  classical
  exact Fintype.ofEquiv (RawCoefficients J R) (rawMapEquiv J R)

def bitsRawMapEquiv {Q : Type} : RawCoefficients J (ZeroInformation.Bits Q) ≃
    (RawPoint J →ₗ[F2] (Q → F2)) :=
  (rawBitsEquiv J).symm.trans (rawMapEquiv J (Q → F2))

theorem bits_coefficients {Q : Type} (gamma : RawCoefficients J (ZeroInformation.Bits Q)) :
    rowCoefficients J (gammaOfRawMap J (bitsRawMapEquiv J gamma)) = gamma := by
  change (rawBitsEquiv J) (gammaOfRawMap J (rawMap J (Q → F2) ((rawBitsEquiv J).symm gamma))) = gamma
  rw [coefficients_rawMap, Equiv.apply_symm_apply]

/-- This equality counts every raw coefficient and every genuine row map once. -/
theorem uniform_bits_rawMaps {Q : Type} [Fintype Q] [DecidableEq Q]
    (H : (RawPoint J →ₗ[F2] (Q → F2)) → ℝ) :
    (𝔼 gamma : RawCoefficients J (ZeroInformation.Bits Q), H (bitsRawMapEquiv J gamma)) =
      𝔼 Y, H Y :=
  Fintype.expect_equiv (bitsRawMapEquiv J) _ H (fun _ => rfl)

end
end UniqueGamesTheorem.Soundness.RawMapLaw

end

end OAI
