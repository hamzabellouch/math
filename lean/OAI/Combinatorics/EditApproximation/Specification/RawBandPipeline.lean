import OAI.Combinatorics.EditApproximation.Specification.RawBandOuter
import OAI.Combinatorics.EditApproximation.Specification.ConcreteFootprints
import OAI.Combinatorics.EditApproximation.Definitions

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {ι α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (t : ℕ) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R) (draw : CountedCellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ × ℕ) (q : TargetInterval target.length) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction) (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (t : ℕ) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R) (q : TargetInterval target.length) (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction) (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction) (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (t : ℕ) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction) (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction) (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction) (q : TargetInterval target.length) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction) (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (t : ℕ) (readParent : TargetInterval target.length → BitQuery ι BinaryFraction) (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction) (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction) (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction) (q : TargetInterval target.length) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction) (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M] (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (copies pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J) (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction) (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery σ BinaryFraction) (q : TargetInterval target.length)



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {α : Type*} {M J R : ℕ} [NeZero M] (source target : List α) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (passes copies pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J) (time : Fin R) (q : TargetInterval target.length)



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ) (request : PhysicalTableRequest M J target.length) (hindex : T < request.index) (hbelow : request.node.1.val < J)
include hindex in
omit [DecidableEq α] [NeZero M] in

theorem active_request_eqRawBand :
    PhysicalTableRequest.refinement request.pass request.copy request.node T (request.index - T)
      request.state = request := by
  have hi : T + (request.index - T) = request.index := by omega
  unfold PhysicalTableRequest.refinement
  rw [hi]

end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ) (request : PhysicalTableRequest M J target.length) (hindex : T < request.index) (hbelow : request.node.1.val < J)


end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ) (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S}) (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R] (source target : List ℕ) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ) (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R] (source target : List ℕ) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ) (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R] (source target : List ℕ) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ) (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ) (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ) (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation




end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation




end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
attribute [local instance] queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
attribute [local instance] queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open Filter MeasureTheory



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
attribute [local instance] queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation




end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open MeasureTheory



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
variable (draw : CellGroupReadDraws M F Q) (drawAllocation : CellGroupSourceAllocations M F Q)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
variable (draw : CellGroupReadDraws M F Q) (drawAllocation : CellGroupSourceAllocations M F Q)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
variable (draw : CellGroupReadDraws M F Q) (drawAllocation : CellGroupSourceAllocations M F Q)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
variable (draw : CellGroupReadDraws M F Q) (drawAllocation : CellGroupSourceAllocations M F Q)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
variable (draw : CellGroupReadDraws M F Q) (drawAllocation : CellGroupSourceAllocations M F Q)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ) (tableAllocation : ℕ → Fin M × TargetInterval target.length → ℕ) (integerAllocation : ℕ → TargetInterval target.length → ℕ)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ) (tableAllocation : ℕ → Fin M × TargetInterval target.length → ℕ) (integerAllocation : ℕ → TargetInterval target.length → ℕ)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation.BinaryFraction
variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)



end OAI.EditApproximation.BinaryFraction
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open Filter MeasureTheory



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open Filter



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open Filter MeasureTheory
attribute [local instance] queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open Filter MeasureTheory
attribute [local instance] queryRoundsNeZero



end OAI.EditApproximation
end

section
universe u v w u_1 u_2 u_3
namespace OAI.EditApproximation
open Filter MeasureTheory
attribute [local instance] queryRoundsNeZero



end OAI.EditApproximation
end
