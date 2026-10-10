import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupSourceSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryContinuationSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundingSpace
import OAI.Combinatorics.EditApproximation.Binary.BinarySampledSourcePort

namespace OAI

namespace EditApproximation.BinaryFraction

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M × ℕ)
  (drawAllocation : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → ℕ)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q))
  (fun i q => BinaryFraction.value (Prod.fst (initial i q)))

def unskippedEstimateSourceAllocation (member : Member) : ℕ :=
  let mass := (envelopeVectorReadWithWork b member.actions initial).1
  let rounded := (roundedBandReadWithWork exponent b member.actions member.nonempty initial).1
  let values := (vectorMapWithWork M (fun i => current i (rounded.get i))).1
  let connection := (endpointConnectionWithWork member.center rounded.get).1
  envelopeVectorReadAllocation b member.actions initial initialAllocation +
    roundedBandReadAllocation exponent b member.actions member.nonempty initial initialAllocation +
    vectorMapAllocation M (fun i => currentAllocation i (rounded.get i)) +
    endpointConnectionAllocation member.center rounded.get + countedGroupMemberSourceAllocation Q b scales connection mass values draw drawAllocation

theorem unskippedEstimateSourceAllocation_le_work (member : Member)
    (hi : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hc : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (ha : ∀ t i, drawAllocation t i ≤ (draw t i).2) :
    unskippedEstimateSourceAllocation source target parent b P exponent Q tau F child initial current
      initialAllocation currentAllocation scales draw drawAllocation member ≤
      (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current scales draw member).2 := by
  let mass := (envelopeVectorReadWithWork b member.actions initial).1
  let rounded := (roundedBandReadWithWork exponent b member.actions member.nonempty initial).1
  let values := (vectorMapWithWork M (fun i => current i (rounded.get i))).1
  have he := envelopeVectorReadAllocation_le_work b member.actions initial initialAllocation (fun i action _ => hi i (action i))
  have hr := roundedBandReadAllocation_le_work exponent b member.actions member.nonempty initial initialAllocation hi
  have hv := vectorMapAllocation_le_work M (fun i => current i (rounded.get i))
    (fun i => currentAllocation i (rounded.get i)) (fun i => hc i (rounded.get i))
  have hg := endpointConnectionAllocation_le_work member.center rounded.get
  have hm := countedGroupMemberSourceAllocation_le_work Q b scales
    (endpointConnectionWithWork member.center rounded.get).1 mass values draw drawAllocation ha
  unfold unskippedEstimateSourceAllocation unskippedEstimateSourceWithWork
  dsimp only [mass, rounded, values] at hv hg hm ⊢
  omega

def chooseUnskippedSourceAllocation (members : List Member) : ℕ :=
  selectGroupAllocation members
    (unskippedEstimateSourceWithWork source target parent b P exponent Q tau F child initial current scales draw)
    (unskippedEstimateSourceAllocation source target parent b P exponent Q tau F child initial current
      initialAllocation currentAllocation scales draw drawAllocation)

theorem chooseUnskippedSourceAllocation_le_work (members : List Member) (hne : members ≠ [])
    (hi : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hc : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (ha : ∀ t i, drawAllocation t i ≤ (draw t i).2) :
    chooseUnskippedSourceAllocation source target parent b P exponent Q tau F child initial current
      initialAllocation currentAllocation scales draw drawAllocation members ≤
      (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current scales draw members hne).2 :=
  selectGroupAllocation_le_work members hne _ _ (fun member _ =>
    unskippedEstimateSourceAllocation_le_work source target parent b P exponent Q tau F child initial current
      initialAllocation currentAllocation scales draw drawAllocation member hi hc ha)

def sampledGroupActionSourceAllocation (members : List Member) (hne : members ≠ []) : ℕ :=
  let selected := (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
    scales draw members hne).1
  let rounded := (roundedBandReadWithWork exponent b selected.actions selected.nonempty initial).1
  chooseUnskippedSourceAllocation source target parent b P exponent Q tau F child initial current
    initialAllocation currentAllocation scales draw drawAllocation members +
    roundedBandReadAllocation exponent b selected.actions selected.nonempty initial initialAllocation +
    endpointActionAllocation selected.center rounded.get

theorem sampledGroupActionSourceAllocation_le_work (members : List Member) (hne : members ≠ [])
    (hi : ∀ i q, initialAllocation i q ≤ (initial i q).2)
    (hc : ∀ i q, currentAllocation i q ≤ (current i q).2)
    (ha : ∀ t i, drawAllocation t i ≤ (draw t i).2) :
    sampledGroupActionSourceAllocation source target parent b P exponent Q tau F child initial current
      initialAllocation currentAllocation scales draw drawAllocation members hne ≤
      (sampledGroupActionSourceWithWork source target parent b P exponent Q tau F child initial current scales draw members hne).2 := by
  let selected := (chooseUnskippedSourceWithWork source target parent b P exponent Q tau F child initial current
    scales draw members hne).1
  have hs := chooseUnskippedSourceAllocation_le_work source target parent b P exponent Q tau F child initial current
    initialAllocation currentAllocation scales draw drawAllocation members hne hi hc ha
  have hr := roundedBandReadAllocation_le_work exponent b selected.actions selected.nonempty initial initialAllocation hi
  have ha := endpointActionAllocation_le_work selected.center
    (roundedBandReadWithWork exponent b selected.actions selected.nonempty initial).1.get
  unfold sampledGroupActionSourceAllocation sampledGroupActionSourceWithWork
  dsimp only [selected] at hr ha ⊢
  omega

end Group

end EditApproximation.BinaryFraction

end OAI
