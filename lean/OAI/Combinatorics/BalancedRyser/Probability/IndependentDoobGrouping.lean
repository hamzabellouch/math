import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrials

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {A : Fin T → Type*} [∀ j, MeasurableSpace (A j)]
  {ξ : ∀ j, Ω → A j}

theorem prefixFiltration_eq_iSup_past (hξ : ∀ j, Measurable (ξ j)) (n : ℕ) :
    prefixFiltration ξ hξ n =
      ⨆ j : {j : Fin T // j.val < n},
        (inferInstance : MeasurableSpace (A j)).comap (ξ j) := by
  classical
  change ((MeasurableSpace.pi.comap (prefixIndices T n).restrict).comap
    (trialVector ξ)) = _
  rw [MeasurableSpace.comap_comp]
  change (inferInstance : MeasurableSpace (∀ j : prefixIndices T n, A j)).comap
    (fun ω (j : prefixIndices T n) => ξ j ω) = _
  rw [MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    exact le_iSup_of_le ⟨j, by simpa only [prefixIndices, Finset.mem_filter, Finset.mem_univ, true_and] using j.property⟩ le_rfl
  · refine iSup_le fun j => ?_
    exact le_iSup_of_le ⟨j, by simpa only [prefixIndices, Finset.mem_filter, Finset.mem_univ, true_and] using j.property⟩ le_rfl

theorem comap_past_eq_prefixFiltration (hξ : ∀ j, Measurable (ξ j)) (i : Fin T) :
    (inferInstance : MeasurableSpace (∀ j : {j : Fin T // j.val < i.val}, A j)).comap
      (fun ω (j : {j : Fin T // j.val < i.val}) => ξ j ω) =
        prefixFiltration ξ hξ i.val := by
  rw [MeasurableSpace.comap_process_pi, prefixFiltration_eq_iSup_past]

theorem comap_past_current_eq_prefixFiltration
    (hξ : ∀ j, Measurable (ξ j)) (i : Fin T) :
    (inferInstance : MeasurableSpace
      ((∀ j : {j : Fin T // j.val < i.val}, A j) × A i)).comap
      (fun ω => ((fun j : {j : Fin T // j.val < i.val} => ξ j ω), ξ i ω)) =
        prefixFiltration ξ hξ (i.val + 1) := by
  change (MeasurableSpace.prod MeasurableSpace.pi inferInstance).comap _ = _
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_process_pi,
    prefixFiltration_eq_iSup_past]
  apply le_antisymm
  · apply sup_le
    · refine iSup_le fun j => ?_
      exact le_iSup_of_le ⟨j, Nat.lt_succ_of_lt j.property⟩ le_rfl
    · exact le_iSup_of_le ⟨i, Nat.lt_succ_self i.val⟩ le_rfl
  · refine iSup_le fun j => ?_
    by_cases hji : (j : Fin T) = i
    · rw [hji]
      exact le_sup_right
    · have hlt : (j : Fin T).val < i.val := by
        have hne : (j : Fin T).val ≠ i.val := fun h => hji (Fin.ext h)
        have hj := j.property
        omega
      exact le_sup_of_le_left (le_iSup_of_le ⟨j, hlt⟩ le_rfl)

end Balanced.IndependentTrials

end OAI
