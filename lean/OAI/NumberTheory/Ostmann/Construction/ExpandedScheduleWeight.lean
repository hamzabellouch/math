import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduleHistory
import OAI.NumberTheory.Ostmann.Construction.WordTransferUniformCoefficient

namespace OAI

/-! # The original atom weight is the concrete prime-word coefficient -/

namespace Ostmann

open scoped BigOperators Classical SchwartzMap FourierTransform ComplexConjugate

noncomputable def scheduleAtomTotal {I : Type*} [Fintype I] (role : I → CopyScheduleRole) :
    ScheduleAtomState role → ℕ
  | ⟨n, x⟩ => ∏ i : CopyScheduleAtoms role n, x i

theorem expanded_schedule_leaf_total {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ) (childBound pivotBound : ℕ → ℕ)
    (path : List Bool) (current : CopyScheduleAtoms role 0 → List σ) (x : σ → ℕ) :
    wordTransferLeafValue
      ((expandedScheduledTemplate role address childBound pivotBound 0 path current).state x) =
      scheduleAtomTotal role ⟨0, expandedAtomValues role 0 current x⟩ := by
  change ((Finset.univ.toList.flatMap current).map x).prod = _
  rw [list_flatMap_product]
  exact Finset.prod_map_toList _ _

theorem recursiveTransferWeight_eq_zero_of_not_valid {State : Type*}
    (sys : TransferHistorySystem State) (leaf : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (n : ℕ) (x : State) (t : FrequencyTree ℤ n)
    (h : ¬ ValidTransferHistory sys n x t) :
    recursiveTransferWeight sys leaf cutoff n x t = 0 := by
  by_contra hn
  exact h (recursiveTransferWeight_nonzero_valid sys leaf cutoff n x t hn)

/-- Expanding the constituents preserves the whole recursive weight,
including invalid support, the forced pivots and all right conjugations. -/
theorem expanded_schedule_weight_eq {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (F : ℕ → ℤ → ℂ) (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (x : ExpandedScheduledVariable α depth → ℕ) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight (wordTransferSystem (ExpandedScheduledVariable α depth))
      (fun τ v => F (wordTransferLeafValue τ) v) (fun _ _ _ _ => 1) n
      ((expandedScheduledTemplate role (expandedPivotAddress α depth)
        childBound pivotBound n path current).state x) t =
    recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound)
      (fun τ v => F (scheduleAtomTotal role τ) v) (fun _ _ _ _ => 1) n
      ⟨n, expandedAtomValues role n current x⟩ t := by
  induction n generalizing path x with
  | zero =>
    change F _ t = F _ t
    rw [expanded_schedule_leaf_total]
  | succ n ih =>
    by_cases hv : ValidTransferHistory (wordTransferSystem (ExpandedScheduledVariable α depth)) (n + 1)
        ((expandedScheduledTemplate role (expandedPivotAddress α depth)
          childBound pivotBound (n + 1) path current).state x) t
    · obtain ⟨P, hp, _, _⟩ := hv
      have hpa := (expanded_schedule_node_iff role (expandedPivotAddress α depth)
        childBound pivotBound n path current x _ _ _ P).mp hp
      rw [recursiveTransferWeight_node _ _ _ _ _ _ P hp,
        recursiveTransferWeight_node _ _ _ _ _ _ P hpa]
      have hn' : n ≤ depth := by omega
      have hl := ih hn' (true :: path)
        (reverseCopyLabelMap role n true [expandedPivotAddress α depth n path] current)
        (reverseExpandedCoordinates_after role depth n hn' true path current hc)
        (Function.update x (expandedPivotAddress α depth n path) P) t.2.1
      have hr := ih hn' (false :: path)
        (reverseCopyLabelMap role n false [expandedPivotAddress α depth n path] current)
        (reverseExpandedCoordinates_after role depth n hn' false path current hc)
        (Function.update x (expandedPivotAddress α depth n path) P) t.2.2
      rw [expanded_schedule_child_state role depth n hn' true path current hc x P] at hl
      rw [expanded_schedule_child_state role depth n hn' false path current hc x P] at hr
      simp only [expandedScheduledTemplate, wordTransferLeftState_node, wordTransferRightState_node]
      rw [hl, hr]
      rfl
    · have hva := mt (expanded_schedule_history_iff role childBound pivotBound depth (n + 1)
          hn path current hc x t).mpr hv
      rw [recursiveTransferWeight_eq_zero_of_not_valid _ _ _ _ _ _ hv,
        recursiveTransferWeight_eq_zero_of_not_valid _ _ _ _ _ _ hva]

/-- The original grouped-atom Fourier weight has an explicit polynomial
coefficient on the independent constituent variables. -/
theorem expandedRootTemplate_weight_coefficient {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth : ℕ) (words : CopyScheduleAtoms role depth → List α)
    (childBound pivotBound : ℕ → ℕ) (x : ExpandedScheduledVariable α depth → ℕ)
    (t : FrequencyTree ℤ depth) (ht : NonzeroInternalFrequencies depth t)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) :
    recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound)
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X))
      (fun _ _ _ _ => 1) depth
      ⟨depth, fun i => (((words i).map Sum.inl).map x).prod⟩ t =
      (WordFourierParameters.uniform depth (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).coefficient
        (expandedRootTemplate role depth words childBound pivotBound) t ht (fun i => (x i : ℤ)) := by
  have he := expanded_schedule_weight_eq role childBound pivotBound
    (fun M v => (if (M : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((M : ℝ) / X)) depth depth le_rfl []
      (fun i => (words i).map Sum.inl) (expandedRootCoordinates_after role depth words) x t
  exact he.symm.trans
    (WordTransferTemplate.recursive_weight_coefficient _ x t ht ψ hreal X lo hi hlo hhi)

end Ostmann

end OAI
