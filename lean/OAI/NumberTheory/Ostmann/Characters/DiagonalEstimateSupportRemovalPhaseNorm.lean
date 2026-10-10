import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalPhaseDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSurvivorNorm

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

private theorem primeProduct_mass_pos {I : Type*} [Fintype I] {Q : ℕ}
    (E : I→Finset (PrimeUpTo Q)) (hE : ∀i,0 < primeShellMass (E i))
    (x : I→PrimeUpTo Q) (hx : ∀i,x i∈E i) :
    0 < (productPrior (fun i=>primeShellPrior (E i) (hE i))).mass x := by
  change 0 < ∏i,(primeShellPrior (E i) (hE i)).mass (x i)
  apply Finset.prod_pos
  intro i hi
  rw [primeShellPrior_mass,ite_eq_left (hx i)]
  exact div_pos (inv_pos.mpr (by exact_mod_cast (primeUpTo_prime (x i)).pos)) (hE i)

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k)

theorem sourceRetainedUnitPhase_norm_le_of_cutoff {U : ℕ}
    (hU : ∀i p,p∈sourceScheduledShells w j i → U < p.val)
    (hS : ∀path f,f∈ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j path →
      f≠0 ∧ f.natAbs ≤ U)
    (P : ℕ+) (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) (hx : ∀i,x i∈sourceSurvivorShells w j i) :
    ‖sourceRetainedUnitPhase w j hj P h x‖ ≤ 1 := by
  exact norm_unitRetainedPhase_le_of_mass k j hj (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledShells w j) (sourceScheduledShells_pos w j)
    (sourceScheduledUnits w j) (fixedConfiguration_scheduled_unit_norm w j)
    (sourceScheduledCharacters w j) (fixedConfiguration_scheduled_nonprincipal w j)
    (sourceScheduledCenters w j) hU (fun i=>x (.inl i)) (fun i=>x (.inr i))
    (primeProduct_mass_pos _ (fun i=>sourceScheduledShells_pos w j _)
      (fun i=>x (.inl i)) (fun i=>hx (.inl i))).ne'
    (primeProduct_mass_pos _ (fun i=>sourceScheduledShells_pos w j _)
      (fun i=>x (.inr i)) (fun i=>hx (.inr i))).ne'
    _ hS [] h P

theorem sourceSurvivorPairPhase_norm_le_of_cutoff {U : ℕ}
    (hU : ∀i p,p∈sourceScheduledShells w j i → U < p.val)
    (hS : ∀path f,f∈ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j path →
      f≠0 ∧ f.natAbs ≤ U)
    (P : ℕ+) (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) (hx : ∀i,x i∈sourceSurvivorShells w j i) :
    ‖sourceSurvivorPairPhase w j hj P e h h' x‖ ≤ 1 := by
  unfold sourceSurvivorPairPhase
  split_ifs with hguard
  · by_cases he : ∀i,x (.inl (e i))∈sourceScheduledShells w j
        (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i)
    · have hp : sourceCounterpartProduct w j e x=1 := by
        simp only [sourceCounterpartProduct,he,ite_true,Finset.prod_const_one,Complex.ofReal_one]
      have hy : ∀i,sourceCounterpartSample w j e x i∈sourceSurvivorShells w j i := by
        intro i
        cases i with
        | inl i => exact he i
        | inr i => exact hx (.inr i)
      rw [hp,one_mul,norm_mul,Complex.norm_conj]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (sourceRetainedUnitPhase_norm_le_of_cutoff w j hj hU hS P h x hx)).trans
        (sourceRetainedUnitPhase_norm_le_of_cutoff w j hj hU hS P h' _ hy)
    · obtain ⟨i,hi⟩ := not_forall.mp he
      have hp : sourceCounterpartProduct w j e x=0 := by
        unfold sourceCounterpartProduct
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)]
      simp only [hp,zero_mul,norm_zero,zero_le_one]
  · simp only [norm_zero,zero_le_one]

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
