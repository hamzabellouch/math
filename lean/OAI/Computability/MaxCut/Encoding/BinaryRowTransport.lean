import Mathlib
import OAI.Computability.MaxCut.Games.RawPartnerTarget

namespace OAI

/-! Exact transport from genuine binary linear maps to the complete private rows
used by the conditional game. -/

namespace MaxCutGames.Soundness.BinaryRowTransport
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
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
end MaxCutGames.Soundness.BinaryRowTransport

end OAI
