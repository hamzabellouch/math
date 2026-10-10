import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateFrequencyScales
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalPhaseIdentity
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalPhaseNorm

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale Filter
attribute [local instance] Classical.propDecidable

theorem integerPrimeTest_norm_le_on_support {I : Type*} {Q : ℕ}
    (E : I→Finset (PrimeUpTo Q)) (F : (I→PrimeUpTo Q)→ℂ) (A : ℝ)
    (hF : ∀x,(∀i,x i∈E i) → ‖F x‖ ≤ A)
    (x : I→ℤ) (hx : ∀i,x i∈integerPrimeSupport (E i)) :
    ‖integerPrimeTest F x‖ ≤ A := by
  have hh : ∀i,∃p : PrimeUpTo Q,p∈E i ∧ (p.val:ℤ)=x i := by
    intro i
    exact Finset.mem_image.mp (hx i)
  choose f hf he using hh
  have heq : primeIntegerAssignment f=x := funext he
  rw [←heq,integerPrimeTest_at_prime]
  exact hF f hf

theorem eventually_sourceSurvivorPairPhase_norm_le (k : ℕ) {BD α : ℝ}
    (hBD : 0 ≤ BD) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop,∀(d : Decomposition)(E : Finset ℕ)(δ β ρ γ c₀ c : ℝ),
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀j (hj : j<k) (P : ℕ+)
        (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
        (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
        (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
          PrimeUpTo s.locations.Q),
        (∀i,x i∈sourceSurvivorShells w j i) → ‖sourceSurvivorPairPhase w j hj P e h h' x‖ ≤ 1 := by
  filter_upwards [exists_actual_frequency_cutoff_eventually k hBD hα] with L hfreq
  intro d E δ β ρ γ c₀ c hband s w j hj P e h h' x hx
  obtain ⟨U,hS,hU⟩ := hfreq
  exact sourceSurvivorPairPhase_norm_le_of_cutoff w j hj
    (fun i p hp=>hU p.val (fixedConfiguration_scheduled_log_bounds w hband j i p hp).1)
    (hS j hj.le) P e h h' x hx

theorem eventually_integer_sourceSurvivorPairPhase_norm_le (k : ℕ) {BD α : ℝ}
    (hBD : 0 ≤ BD) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop,∀(d : Decomposition)(E : Finset ℕ)(δ β ρ γ c₀ c : ℝ),
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀j (hj : j<k) (P : ℕ+)
        (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
        (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
        (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→ℤ),
        (∀i,x i∈sourceSurvivorIntegerSupport w j i) →
          ‖integerPrimeTest (sourceSurvivorPairPhase w j hj P e h h') x‖ ≤ 1 := by
  filter_upwards [eventually_sourceSurvivorPairPhase_norm_le k hBD hα] with L hL
  intro d E δ β ρ γ c₀ c hband s w j hj P e h h' x hx
  exact integerPrimeTest_norm_le_on_support (sourceSurvivorShells w j)
    (sourceSurvivorPairPhase w j hj P e h h') 1
    (hL d E δ β ρ γ c₀ c hband s w j hj P e h h') x hx

end Ostmann.Characters.DiagonalEstimate

end

end OAI
