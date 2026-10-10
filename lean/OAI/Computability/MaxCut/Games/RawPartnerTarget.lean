import Mathlib
import OAI.Computability.MaxCut.Games.IncidenceExtraction

namespace OAI

noncomputable section

/-! A partner target whose coordinates depend only on the displayed full/single
positions. It does not contain hidden occurrence identities or right-hand sides. -/

namespace MaxCutGames.Soundness.RawPartnerTarget
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open PartnerProjection PartnerMapCoordinates ConditionalIncidences

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

end MaxCutGames.Soundness.RawPartnerTarget

/-!
# Complete local private inputs after fixing H

The constructors here consume only the appropriate zero-set question tuple:
occurrences for the first player, names for the second. A single reference sample
from the positive observation fibre is fixed once as part of H-dependent advice.
It supplies arbitrary padding at hidden positions and never depends on the actual
remaining sample. The reconstruction theorems prove equality of the complete
question-plus-row input, and the row maps restrict to the actual equation spaces
as shown in `ZeroInformation.supplied_map_pullback`.
-/

namespace MaxCutGames.Soundness.ConditionalIncidences

instance zeroBits (R : Type) : Zero (ZeroInformation.Bits R) :=
  ⟨ZeroInformation.zero⟩

def membershipBool {P : Type} [DecidableEq P] (J : Finset P) : P → Bool :=
  fun j => decide (j ∈ J)

def fullCoefficient {P R : Type} [DecidableEq P] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) (i : Fin 2) :
    P → ZeroInformation.Bits R :=
  fun j => if hj : j ∉ J then gamma (some (.inl (⟨j, hj⟩, i))) else ZeroInformation.zero

def singleCoefficient {P R : Type} [DecidableEq P] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) : P → ZeroInformation.Bits R :=
  fun j => if hj : j ∈ J then gamma (some (.inr ⟨j, hj⟩)) else ZeroInformation.zero

def fillHidden {P X : Type} [DecidableEq P] (K : Finset P)
    (fallback : P → X) (inside : PositionInside K → X) : P → X :=
  fun j => if hj : j ∈ K then inside ⟨j, hj⟩ else fallback j

theorem singleCoefficient_zero {P R : Type} [DecidableEq P]
    [Fintype R] [DecidableEq R] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) (j : P)
    (hj : j ∈ zeroSet J gamma) : singleCoefficient J gamma j = ZeroInformation.zero := by
  obtain ⟨hjJ, hz⟩ := (mem_zeroSet J gamma j).mp hj
  change gamma (some (.inr ⟨j, hjJ⟩)) = ZeroInformation.zero at hz
  simpa only [singleCoefficient, hjJ, ↓reduceDIte] using hz

theorem zeroSet_subset {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) : zeroSet J gamma ⊆ J := by
  intro j hj
  exact ((mem_zeroSet J gamma j).mp hj).choose

variable {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  (J : Finset P) (name : O → Fin 3 → N)
  (gamma : RawCoefficients J (ZeroInformation.Bits R))
  (observed : PositionOutside (zeroSet J gamma) → O × N)

def actualFirst (sample : Draw P O) : ZeroInformation.FirstInput P R O :=
  ZeroInformation.firstInput Finset.univ.toList (membershipBool J) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (sample j).1) (fun j => (sample j).2)

def actualSecond (sample : Draw P O) : ZeroInformation.SecondInput P R O N :=
  ZeroInformation.secondInput Finset.univ.toList (membershipBool J) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (sample j).1) (fun j => name (sample j).1 (sample j).2)

def localFirstFromH (reference : RawObservationFibre J name gamma observed)
    (insideOccurrences : PositionInside (zeroSet J gamma) → O) :
    ZeroInformation.FirstInput P R O :=
  ZeroInformation.reconstructFirst Finset.univ.toList
    (membershipBool J) (membershipBool (zeroSet J gamma)) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    name
    (fillHidden (zeroSet J gamma) (fun j => (reference.val.2 j).1) insideOccurrences)
    (fun j => (reference.val.2 j).1)
    (fun j => name (reference.val.2 j).1 (reference.val.2 j).2)

def localSecondFromH (reference : RawObservationFibre J name gamma observed)
    (insideNames : PositionInside (zeroSet J gamma) → N) :
    ZeroInformation.SecondInput P R O N :=
  ZeroInformation.reconstructSecond Finset.univ.toList
    (membershipBool J) (membershipBool (zeroSet J gamma)) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (reference.val.2 j).1)
    (fillHidden (zeroSet J gamma)
      (fun j => name (reference.val.2 j).1 (reference.val.2 j).2) insideNames)
    (fun j => name (reference.val.2 j).1 (reference.val.2 j).2)

omit [DecidableEq R] in
theorem localFirstFromH_question_inside
    (reference : RawObservationFibre J name gamma observed)
    (insideOccurrences : PositionInside (zeroSet J gamma) → O)
    (j : PositionInside (zeroSet J gamma)) :
    (localFirstFromH J name gamma observed reference insideOccurrences).question j.val =
      insideOccurrences j := by
  simp [localFirstFromH, ZeroInformation.reconstructFirst, ZeroInformation.firstInput,
    ZeroInformation.reconstructQuestion, fillHidden, membershipBool, j.property]

omit [DecidableEq R] in
theorem localSecondFromH_question_inside
    (reference : RawObservationFibre J name gamma observed)
    (insideNames : PositionInside (zeroSet J gamma) → N)
    (j : PositionInside (zeroSet J gamma)) :
    (localSecondFromH J name gamma observed reference insideNames).question j.val =
      Sum.inr (insideNames j) := by
  have hjJ : j.val ∈ J := zeroSet_subset J gamma j.property
  simp [localSecondFromH, ZeroInformation.reconstructSecond, ZeroInformation.secondInput,
    ZeroInformation.partnerQuestion, ZeroInformation.reconstructQuestion,
    fillHidden, membershipBool, j.property, hjJ]

omit [Fintype P] [DecidableEq R] in
theorem outside_pair_agree (reference sample : RawObservationFibre J name gamma observed)
    (j : P) (hj : j ∉ zeroSet J gamma) :
    incidence name (reference.val.2 j) = incidence name (sample.val.2 j) := by
  exact congrFun (reference.property.2.trans sample.property.2.symm) ⟨j, hj⟩

omit [Fintype P] [DecidableEq R] in
theorem fillHidden_occurrences (reference sample : RawObservationFibre J name gamma observed) :
    fillHidden (zeroSet J gamma) (fun j => (reference.val.2 j).1)
        (fun j => (sample.val.2 j.val).1) =
      (fun j => (sample.val.2 j).1) := by
  funext j
  by_cases hj : j ∈ zeroSet J gamma
  · simp [fillHidden, hj]
  · simp only [fillHidden, hj, ↓reduceDIte]
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj)

omit [Fintype P] [DecidableEq R] in
theorem fillHidden_names (reference sample : RawObservationFibre J name gamma observed) :
    fillHidden (zeroSet J gamma)
        (fun j => name (reference.val.2 j).1 (reference.val.2 j).2)
        (fun j => name (sample.val.2 j.val).1 (sample.val.2 j.val).2) =
      (fun j => name (sample.val.2 j).1 (sample.val.2 j).2) := by
  funext j
  by_cases hj : j ∈ zeroSet J gamma
  · simp [fillHidden, hj]
  · simp only [fillHidden, hj, ↓reduceDIte]
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj)

/-- Equality of the entire first private input, including its row map. -/
theorem localFirstFromH_correct
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (reference sample : RawObservationFibre J name gamma observed) :
    localFirstFromH J name gamma observed reference (fun j => (sample.val.2 j.val).1) =
      actualFirst J gamma sample.val.2 := by
  unfold localFirstFromH actualFirst
  rw [fillHidden_occurrences J name gamma observed reference sample]
  apply ZeroInformation.first_input_reconstruction
  · intro j hj
    exact singleCoefficient_zero J gamma j (of_decide_eq_true hj)
  · exact distinct
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj')
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj')

omit [DecidableEq R] in
/-- Equality of the entire second private input. The constructor requires no
occurrence, equation rhs, or slot from any position in K. -/
theorem localSecondFromH_correct (reference sample : RawObservationFibre J name gamma observed) :
    localSecondFromH J name gamma observed reference
        (fun j => name (sample.val.2 j.val).1 (sample.val.2 j.val).2) =
      actualSecond J name gamma sample.val.2 := by
  unfold localSecondFromH actualSecond
  rw [fillHidden_names J name gamma observed reference sample]
  apply ZeroInformation.second_input_reconstruction
  · intro j hj
    exact decide_eq_true (zeroSet_subset J gamma (of_decide_eq_true hj))
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj')
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj')

end MaxCutGames.Soundness.ConditionalIncidences

end

end OAI
