import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFixedConfigurationDefs
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceRoleBoundsTargets

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource

theorem configurationAnchorPair_sum {k : ℕ} (cfg : SourceConfiguration k) :
    (∑ i, (cfg.1 i:ℝ)) = ∑ j ∈ Finset.range k, configurationAnchorPair cfg j := by
  have he := (finCongr (show k+k=2*k by omega)).sum_comp (fun i => (cfg.1 i:ℝ))
  rw [←he, Fin.sum_univ_add, ←Fin.sum_univ_eq_sum_range]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [configurationAnchorPair, dite_eq_left i.isLt]
  rfl

theorem configurationTarget_sum {k : ℕ} (logX J : ℝ) (Δ : ℕ → ℝ)
    (cfg : SourceConfiguration k) :
    (∑ j, configurationTarget logX J Δ cfg j) =
      (∑ j ∈ Finset.range k, HigherBiasSourceTargets.pivotTarget k J
        (configurationAnchorPair cfg) Δ j) +
      HigherBiasSourceTargets.fillerTarget k logX J (configurationAnchorPair cfg) Δ := by
  rw [Fin.sum_univ_castSucc]
  simp only [configurationTarget, Fin.val_castSucc, Fin.val_last,
    Nat.lt_irrefl, ite_false, ite_eq_left (Fin.isLt _)]
  rw [Fin.sum_univ_eq_sum_range]

theorem configuration_targets_total_identity {k : ℕ} (logX J : ℝ) (Δ : ℕ → ℝ)
    (cfg : SourceConfiguration k) :
    2*(J+(∑ i,(cfg.1 i:ℝ))+(∑ j,configurationTarget logX J Δ cfg j)) = logX+Δ 0 := by
  rw [configurationAnchorPair_sum, configurationTarget_sum]
  have h := HigherBiasSourceTargets.targets_total_identity k logX J (configurationAnchorPair cfg) Δ
  rw [Finset.sum_add_distrib] at h
  linarith

theorem configuration_indices_target_error {k : ℕ} (logX J : ℝ) (Δ : ℕ → ℝ)
    (cfg : SourceConfiguration k) {c : ℝ}
    (hlist : ∀ j, |((cfg.2 j).sum:ℝ)-configurationTarget logX J Δ cfg j| ≤ 6/c) :
    |2*(J+∑ i,(configCellIndices cfg i:ℝ))-(logX+Δ 0)| ≤ 2*(k+1:ℕ)*(6/c) := by
  rw [configCellIndices_sum]
  have hh := HigherBiasSourceRoleBounds.configuration_list_sum_error cfg
    (configurationTarget logX J Δ cfg) hlist
  have ht := configuration_targets_total_identity logX J Δ cfg
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  apply abs_le.mpr
  constructor <;> linarith

end Ostmann.Characters.HigherBiasSource

end

end OAI
