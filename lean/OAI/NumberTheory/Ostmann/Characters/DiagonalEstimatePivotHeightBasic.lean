import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceDefs
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateIndices

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD)

theorem configuration_list_entry_le (j : Fin (k+1))
    (a : Fin (w.configuration.2 j).length) :
    ((w.configuration.2 j).get a : ℝ) ≤ Real.exp (β*L) := by
  obtain ⟨n, hn⟩ := w.nonempty
  have h := (w.good n hn (cellCoordinateEquiv w.configuration (.inr ⟨j,a⟩))).2.1
  simpa only [cellCoordinateEquiv_list] using h

theorem configuration_list_sum_le (j : Fin (k+1)) :
    ((w.configuration.2 j).sum : ℝ) ≤
      (2*Real.exp (2*((1/10000:ℝ)*k)))*Real.exp (β*L) := by
  have hs : (∑ a : Fin (w.configuration.2 j).length,
      ((w.configuration.2 j).get a : ℝ)) = ((w.configuration.2 j).sum : ℝ) := by
    rw [← Int.cast_sum, ← List.sum_ofFn, List.ofFn_get]
  rw [← hs]
  calc
    _ ≤ ∑ _a : Fin (w.configuration.2 j).length, Real.exp (β*L) := by
      exact Finset.sum_le_sum (fun a _ => configuration_list_entry_le w j a)
    _ = ((w.configuration.2 j).length : ℝ)*Real.exp (β*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (w.geometry.length_upper j) (Real.exp_pos _).le

theorem sourcePivotTarget_le (j : ℕ) (hj : j < k) :
    sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j ≤
      (2*Real.exp (2*((1/10000:ℝ)*k)))*Real.exp (β*L) + 6/c := by
  let jf : Fin k := ⟨j,hj⟩
  have ht := w.geometry.target_error jf.castSucc
  rw [configurationTarget_pivot] at ht
  have hs := configuration_list_sum_le w jf.castSucc
  have hlow := (abs_le.mp ht).1
  change -(6/c) ≤ ((w.configuration.2 jf.castSucc).sum : ℝ) -
    sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j at hlow
  linarith

theorem sourcePivotRanges_le_exp (j : ℕ) (hj : j < k) {P : ℕ+}
    (hP : P ∈ sourcePivotRanges w j) :
    (P : ℝ) ≤ Real.exp ((2*Real.exp (2*((1/10000:ℝ)*k)))*Real.exp (β*L) +
      (6/c + sourceAtomWidth k c)) := by
  have hp := pivotWindow_upper _ _ hP
  apply hp.trans (Real.exp_le_exp.mpr _)
  have ht := sourcePivotTarget_le w j hj
  linarith

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
