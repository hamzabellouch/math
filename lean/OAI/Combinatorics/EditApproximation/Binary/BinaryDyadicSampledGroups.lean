import OAI.Combinatorics.EditApproximation.Binary.BinarySampledGroups
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The generated binary scale list is reindexed into the finite
draw domain. Only proof transport is used: the accepted draw count is the
same natural computed by `groupSampleCountWithWork`. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem indexedGroupScales_value (raw : List BinaryFraction) (M b : ℕ) (F : ℚ)
    (h : raw.map value = groupDyadicScales M b F)
    (i : Fin (groupDyadicScales M b F).length) :
    (indexedGroupScales raw M b F h i).value = groupDyadicScaleAt M b F i := by
  unfold indexedGroupScales groupDyadicScaleAt
  simp only [List.get_eq_getElem]
  rw [← List.getElem_map value (l := raw) (i := i.val) (h := by rw [h]; exact i.isLt)]
  simp only [h]

theorem unskippedEstimate_scale_transport {α : Type*} {source target : List α} {M T : ℕ}
    {parent : TargetInterval source.length} {b P exponent Q : ℕ} {tau F : ℚ}
    {child initial : Fin M → TargetInterval target.length → ℚ}
    (left right : Fin T → ℚ) (h : left = right)
    (current : Fin M → TargetInterval target.length → ℚ)
    (member : UnskippedBand source target parent b P exponent tau F child initial)
    (draw : ∀ t, Fin (groupSampleCount M Q b (right t)) → Fin M) :
    unskippedGroupEstimate left (fun t => groupSampleCount M Q b (left t)) current member
      (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b) (congrFun h t)) j)) =
      unskippedGroupEstimate right (fun t => groupSampleCount M Q b (right t)) current member draw := by
  cases h
  rfl

section Physical
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
  (raw : List BinaryFraction) (hraw : raw.map value = groupDyadicScales M b F.value)
  (draw : ∀ t : Fin (groupDyadicScales M b F.value).length,
    Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F.value t)) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q)) (fun i q => BinaryFraction.value (initial i q))

def dyadicSampledGroupActionWithWork (members : List Member) (hne : members ≠ []) :=
  sampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
    (indexedGroupScales raw M b F.value hraw)
    (fun t j => draw t (Fin.cast (congrArg (groupSampleCount M Q b)
      (indexedGroupScales_value raw M b F.value hraw t)) j)) members hne

theorem dyadicSampledGroupActionWithWork_value (members : List Member) (hne : members ≠ [])
    (hb : 0 < b) :
    (dyadicSampledGroupActionWithWork source target parent b P exponent Q tau F child initial current
      raw hraw draw members hne).1.decode =
      (chooseUnskippedGroup Q (fun i q => (current i q).value) members hne draw).rationalAction := by
  unfold dyadicSampledGroupActionWithWork
  rw [sampledGroupActionWithWork_value source target parent b P exponent Q hb]
  unfold chooseUnskippedGroup dyadicUnskippedGroupEstimate
  congr 2
  funext member
  exact unskippedEstimate_scale_transport _ _
    (funext (indexedGroupScales_value raw M b F.value hraw)) _ member draw

end Physical
end BinaryFraction
end EditApproximation

end OAI
