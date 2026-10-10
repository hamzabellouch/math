import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.InitialState
import OAI.LinearAlgebra.MatrixFields.Entropy.InitialLeafRates
import OAI.LinearAlgebra.MatrixFields.Entropy.TerminalStatisticLaws

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldFinalState

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldTerminalStatisticLaws
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev InitialIndex (K : ℕ) := AllFieldInitialLeafRates.PopulationHistory K
abbrev CIndex (K : ℕ) := AfterC K × Placement
abbrev Index (K : ℕ) := InitialIndex K ⊕ (TerminalZero K ⊕ CIndex K)

def history {K : ℕ} : Index K → History K
  | .inl h => (.initial h.1.val, h.2)
  | .inr (.inl h) => AllFieldTerminalStatisticLaws.history h
  | .inr (.inr h) => (.afterC h.1, h.2)

theorem history_terminal {K : ℕ} (h : Index K) : terminal (history h).1 := by
  rcases h with h | h | h
  · exact h.1.property
  · rcases h with h | h
    · exact h.1.property
    · exact h.1.property
  · trivial

theorem terminal_resident_final {K : ℕ} (h : CanonicalHistory K) (ht : terminal h) :
    resident (K + 2) h := by
  have hlot := (initialAncestor h).1.isLt
  cases h with
  | initial h => exact fun hp => False.elim (ht hp)
  | afterA h =>
      refine ⟨?_, fun hp => False.elim (ht hp)⟩
      change h.1.val.1.val < K at hlot
      omega
  | afterB h =>
      refine ⟨?_, ht⟩
      change h.1.val.1.val.1.val < K at hlot
      omega
  | partC h => exact False.elim ht
  | afterC h =>
      change h.1.1.val.1.val.1.val.1.val < K at hlot
      change h.1.1.val.1.val.1.val.1.val + 3 ≤ K + 2
      omega

def toState {K : ℕ} (h : Index K) : State K (K + 2) :=
  ⟨history h, terminal_resident_final _ (history_terminal h)⟩

def fromState {K : ℕ} (h : State K (K + 2)) : Index K := by
  have ht := final_state_terminal h
  rcases h with ⟨⟨h, phi⟩, hr⟩
  cases h with
  | initial h => exact .inl (⟨h, ht⟩, phi)
  | afterA h => exact .inr (.inl (.inl (⟨h, ht⟩, phi)))
  | afterB h => exact .inr (.inl (.inr (⟨h, ht⟩, phi)))
  | partC h => exact False.elim ht
  | afterC h => exact .inr (.inr (h, phi))

def indexEquiv (K : ℕ) : Index K ≃ State K (K + 2) where
  toFun := toState
  invFun := fromState
  left_inv h := by
    rcases h with h | h | h
    · rfl
    · cases h <;> rfl
    · rfl
  right_inv h := by
    have ht := final_state_terminal h
    rcases h with ⟨⟨h, phi⟩, hr⟩
    cases h with
    | initial h => rfl
    | afterA h => rfl
    | afterB h => rfl
    | partC h => exact False.elim ht
    | afterC h => rfl

variable {K : ℕ} (allocation : Allocation) (dilation : ℕ)

abbrev Words := ∀ h : Index K, HistoryWord allocation dilation (history h)
abbrev InitialWords := ∀ h : InitialIndex K,
  HistoryWord allocation dilation (.initial h.1.val, h.2)
abbrev ZeroWords := ∀ h : TerminalZero K,
  HistoryWord allocation dilation (AllFieldTerminalStatisticLaws.history h)
abbrev CWords := ∀ h : CIndex K, HistoryWord allocation dilation (.afterC h.1, h.2)
abbrev Parts := InitialWords (K := K) allocation dilation ×
  (ZeroWords (K := K) allocation dilation × CWords (K := K) allocation dilation)

instance wordsFintype : Fintype (Words (K := K) allocation dilation) :=
  Fintype.ofFinite _

def grouped (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (Words (K := K) allocation dilation) (Words (K := K) allocation dilation)
      (Words (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : Index K =>
    historyTensor F allocation dilation ε (history h))

def stateWord (w : Words (K := K) allocation dilation) :
    ∀ h : State K (K + 2), HistoryWord allocation dilation h.val :=
  Equiv.piCongrLeft (fun h : State K (K + 2) => HistoryWord allocation dilation h.val)
    (indexEquiv K) w

theorem grouped_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : Words (K := K) allocation dilation) :
    stateTensor F allocation dilation ε (K + 2) (stateWord allocation dilation x)
      (stateWord allocation dilation y) (stateWord allocation dilation z) =
    grouped allocation dilation F ε x y z := by
  change (∏ h : State K (K + 2), historyTensor F allocation dilation ε h.val
    (stateWord allocation dilation x h) (stateWord allocation dilation y h)
      (stateWord allocation dilation z h)) = _
  rw [← (indexEquiv K).prod_comp]
  unfold grouped CommonDimensions.familyProduct
  apply Finset.prod_congr rfl
  intro h _
  have hstate (w : Words (K := K) allocation dilation) :
      stateWord allocation dilation w ((indexEquiv K) h) = w h :=
    Equiv.piCongrLeft_apply_apply
      (fun state : State K (K + 2) => HistoryWord allocation dilation state.val)
      (indexEquiv K) w h
  rw [hstate, hstate, hstate]
  rfl

def groupedMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (stateTensor F (K := K) allocation dilation ε (K + 2))
      (grouped (K := K) allocation dilation F ε) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (stateWord (K := K) allocation dilation) (stateWord (K := K) allocation dilation)
    (stateWord (K := K) allocation dilation) _).symm.trans ?_⟩
  funext x y z
  exact grouped_coefficient allocation dilation F ε x y z

def initialTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (InitialWords (K := K) allocation dilation) (InitialWords (K := K) allocation dilation)
      (InitialWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : InitialIndex K =>
    historyTensor F allocation dilation ε (.initial h.1.val, h.2))

def zeroTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (ZeroWords (K := K) allocation dilation) (ZeroWords (K := K) allocation dilation)
      (ZeroWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : TerminalZero K =>
    historyTensor F allocation dilation ε (AllFieldTerminalStatisticLaws.history h))

def cTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (CWords (K := K) allocation dilation) (CWords (K := K) allocation dilation)
      (CWords (K := K) allocation dilation) :=
  CommonDimensions.familyProduct (fun h : CIndex K =>
    historyTensor F allocation dilation ε (.afterC h.1, h.2))

def partsTensor (F : Type*) [Field F] (ε : ℝ) :
    Tensor F (Parts (K := K) allocation dilation) (Parts (K := K) allocation dilation)
      (Parts (K := K) allocation dilation) :=
  Tensor.product (initialTensor (K := K) allocation dilation F ε)
    (Tensor.product (zeroTensor (K := K) allocation dilation F ε)
      (cTensor (K := K) allocation dilation F ε))

def joinParts (w : Parts (K := K) allocation dilation) : Words (K := K) allocation dilation
  | .inl h => w.1 h
  | .inr (.inl h) => w.2.1 h
  | .inr (.inr h) => w.2.2 h

theorem parts_coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : Parts (K := K) allocation dilation) :
    grouped allocation dilation F ε (joinParts allocation dilation x)
      (joinParts allocation dilation y) (joinParts allocation dilation z) =
    partsTensor allocation dilation F ε x y z := by
  unfold grouped CommonDimensions.familyProduct
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  rfl

def partsMap (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (grouped (K := K) allocation dilation F ε)
      (partsTensor (K := K) allocation dilation F ε) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (joinParts (K := K) allocation dilation) (joinParts (K := K) allocation dilation)
    (joinParts (K := K) allocation dilation) _).symm.trans ?_⟩
  funext x y z
  exact parts_coefficient allocation dilation F ε x y z

def map (F : Type*) [Field F] (ε : ℝ) :
    LocalMap (stateTensor F (K := K) allocation dilation ε (K + 2))
      (partsTensor (K := K) allocation dilation F ε) :=
  (groupedMap allocation dilation F ε).comp (partsMap allocation dilation F ε)

end MatrixMultiplication.AllFieldFinalState

end

end MatrixAllFields

end OAI
