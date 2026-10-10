import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateIntegerPriorProperties
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurviving

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template Template.OneSidedPhase HigherBiasSource
open HigherBiasSource.SourceTemplate InitialCharacterScale TemplateOneSidedSupportSurviving
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k)

abbrev sourceRetainedUnitPhase (P : ℕ+) (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) : ℂ :=
  unitRetainedPhase k j hj (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledUnits w j) (sourceScheduledCharacters w j) (sourceScheduledCenters w j)
    (fun i=>x (.inl i)) (fun i=>x (.inr i)) P h.val.1 h.val.2

def sourceCounterpartSample
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) :
    SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→PrimeUpTo s.locations.Q :=
  Sum.elim (fun i=>x (.inl (e i))) (fun i=>x (.inr i))

def sourceCounterpartProduct
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) : ℂ :=
  ((∏i,if x (.inl (e i))∈sourceScheduledShells w j
    (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i)
    then (1:ℝ) else 0):ℂ)

def sourceSurvivorPairPhase (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→
      PrimeUpTo s.locations.Q) : ℂ :=
  if Pairwise (fun i v=>(x i).val.Coprime (x v).val) ∧
      pivotPrimeGuard (sourceWidth w.configuration (wordSize k L)) P x then
    sourceCounterpartProduct w j e x *
      sourceRetainedUnitPhase w j hj P h x *
      conj (sourceRetainedUnitPhase w j hj P h' (sourceCounterpartSample w j e x))
  else 0

def sourceSurvivorPhaseMasks (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (i : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))) (p : ℕ) : ℂ :=
  counterpartSourceMask (fun i=>sourceScheduledShells w j
    (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i)) e i p *
      if p.Coprime P then 1 else 0

theorem sourceSurvivorPhaseMasks_norm (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (i : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))) (p : ℕ) :
    ‖sourceSurvivorPhaseMasks w j P e i p‖ ≤ 1 := by
  unfold sourceSurvivorPhaseMasks
  split_ifs with hp
  · simpa only [mul_one] using counterpartSourceMask_norm _ e i p
  · simp only [mul_zero,norm_zero,zero_le_one]

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
