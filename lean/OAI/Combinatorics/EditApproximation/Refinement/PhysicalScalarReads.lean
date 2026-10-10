import OAI.Combinatorics.EditApproximation.Refinement.PhysicalScalarSource
import OAI.Combinatorics.EditApproximation.Geometry.LocalGroupSourceQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRawGroupProgram
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRawOnlineProgram
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Direct scalar source requests. The physical scale/cell guards agree
with the original raw providers, and an online request carries its range. -/

namespace EditApproximation

section Reads

variable (M J N n exponent F Q R B : ℕ) [NeZero M]



def physicalScalarAnswer (draw : PhysicalScalarDraw M J N n exponent F Q R B)
    (key : PhysicalScalarKey M J N n exponent F Q R B) : ℚ := (draw key).val









end Reads

section GroupCorrectness

variable (M J N n exponent F Q R B : ℕ) [NeZero M]
  (draw : PhysicalScalarDraw M J N n exponent F Q R B)

omit [NeZero M] in
private theorem groupQuery_transport (b c : ℕ) (h : b = c)
    (queries : PhysicalGroupQueries M J N n exponent F Q R B b)
    (values : ParentGroupDraw M (groupDyadicScales M b F).length
      (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale)))
    (hq : ∀ scale sample, (queries scale sample).value
      (physicalScalarAnswer M J N n exponent F Q R B draw) = (values scale sample).val) :
    ∀ scale sample,
      ((Eq.mp (congrArg (PhysicalGroupQueries M J N n exponent F Q R B) h) queries) scale sample).value
        (physicalScalarAnswer M J N n exponent F Q R B draw) =
      ((Eq.mp (congrArg (fun b => ParentGroupDraw M (groupDyadicScales M b F).length
        (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale))) h) values) scale sample).val := by
  subst c
  exact hq

 theorem physicalScalarGroupRead_value (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    (physicalScalarGroupRead M J N n exponent F Q R B node time key).value
      (physicalScalarAnswer M J N n exponent F Q R B draw) =
    groupScalarValue (physicalRawGroupDraws M J N n exponent F Q R
      (fun group => physicalScalarPack M J N n exponent F Q R B draw (.inr group)) node time) key := by
  rcases key with ⟨⟨b, cell⟩, scale, sample⟩
  unfold physicalScalarGroupRead physicalScalarGroupQueries groupScalarValue physicalRawGroupDraws
  dsimp only
  split_ifs with hb hc
  · let group : PhysicalLocalGroupKey M J N n exponent :=
      (node, physicalScaleIndex N b hb,
        ⟨cell.1, Nat.lt_succ_of_le hc.1⟩, ⟨cell.2, Nat.lt_succ_of_le hc.2⟩)
    exact groupQuery_transport M J N n exponent F Q R B draw
      ((dyadicScales N).get group.2.1) b (physicalScaleIndex_get N b hb)
      (physicalScalarGroupQueriesAt M J N n exponent F Q R B group time)
      (physicalScalarPack M J N n exponent F Q R B draw (.inr group) time)
      (fun _ _ => rfl) scale sample
  · rfl
  · rfl

end GroupCorrectness

section OnlineCorrectness

variable {α : Type*} [DecidableEq α] {M J : ℕ} [NeZero M]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q R B : ℕ) (tau : ℚ)
  (hbound : ∀ key, physicalLocalOnlineMass source target U N P F A T exponent H tau key ≤ B)
  (draw : PhysicalScalarDraw M J N target.length exponent F Q R B)

omit [NeZero M] in
 theorem physicalScalarOnlineRead_value [NeZero R]
    (node : PhysicalInternalNode M J) (time : Fin R) (key : ℕ × TargetInterval target.length)
    (range : ℕ)
    (hrange : ∀ hb : key.1 ∈ dyadicScales N, range =
      physicalLocalOnlineMass source target U N P F A T exponent H tau
        (node, physicalScaleIndex N key.1 hb, key.2)) :
    (physicalScalarOnlineRead M J N target.length exponent F Q R B node time key range).value
      (physicalScalarAnswer M J N target.length exponent F Q R B draw) =
    (physicalRawOnlineIntegers source target U N P F A T exponent H tau
      (fun online => physicalCommonSample source target U N P F A T exponent H Q R B tau hbound
        (physicalScalarPack M J N target.length exponent F Q R B draw) (.inl online))
      node time key.1 key.2 : ℚ) := by
  unfold physicalScalarOnlineRead physicalRawOnlineIntegers
  by_cases hb : key.1 ∈ dyadicScales N
  · rw [dite_eq_left hb, dite_eq_left hb, hrange hb]
    have hpos := physicalCommonMass_positive source target U N P F A T exponent H tau
      (node, physicalScaleIndex N key.1 hb, key.2)
    rw [dite_eq_left ⟨hpos, hbound _⟩]
    simp only [FiniteQuery.value, physicalCommonSample, physicalCommonCoordinateImage,
      physicalScalarPack, physicalScalarCoordinatePack, physicalScalarAnswer,
      physicalCommonSelectedKey, physicalCommonSelectedOnlineKey]
    exact (congrArg (fun z : ℕ => (z : ℚ)) (Fin.val_cast _ _)).symm
  · rw [dite_eq_right hb, dite_eq_right hb]
    rfl

end OnlineCorrectness

end EditApproximation

end OAI
