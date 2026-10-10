import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateIntegerPriorProperties
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalPrior
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingFamilies

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template TemplateSupportRemoval Template.OneSidedPhase
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale
open TemplateOneSidedSupportSurviving
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ)

def groupedSourceNaturalSupport (i : GroupedSourceIndex w j) : Finset ℕ :=
  sourceSurvivorNaturalSupport w j
    (survivingPrimeEquiv k j (sourceWidth w.configuration (wordSize k L)) i)

theorem groupedSourceIntegerSupport_eq_nat_image (i : GroupedSourceIndex w j) :
    groupedSourceIntegerSupport w j i=
      (groupedSourceNaturalSupport w j i).image (fun p:ℕ=>(p:ℤ)) :=
  sourceSurvivorIntegerSupport_eq_nat_image w j _

theorem groupedSourceNaturalSupport_prime (i : GroupedSourceIndex w j) {p : ℕ}
    (hp : p∈groupedSourceNaturalSupport w j i) : p.Prime :=
  sourceSurvivorNaturalSupport_prime w j _ hp

theorem groupedSourceIntegerWeight_nonneg (i : GroupedSourceIndex w j) (n : ℤ) :
    0≤groupedSourceIntegerWeight w j i n :=
  sourceSurvivorIntegerWeight_nonneg w j _ n

theorem groupedSourceIntegerWeight_sum (i : GroupedSourceIndex w j) :
    (∑n∈groupedSourceIntegerSupport w j i,groupedSourceIntegerWeight w j i n)=1 :=
  sourceSurvivorIntegerWeight_sum w j _

theorem groupedSourceIntegerSupport_bounds
    (hband : ∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L)
    (i : GroupedSourceIndex w j) {n : ℤ} (hn : n∈groupedSourceIntegerSupport w j i) :
    Real.exp (Real.exp (α*L))≤(n:ℝ) ∧ (n:ℝ)≤Real.exp (Real.exp (β*L)) :=
  sourceSurvivorIntegerSupport_bounds w j hband _ hn

theorem groupedSourceIntegerSupport_abs_le
    (hband : ∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L)
    (i : GroupedSourceIndex w j) {n : ℤ} (hn : n∈groupedSourceIntegerSupport w j i) :
    |(n:ℝ)|≤Real.exp (Real.exp (β*L)) :=
  sourceSurvivorIntegerSupport_abs_le w j hband _ hn

theorem ungroupSourceAssignment_groupedPrimeAssignment
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q) :
    ungroupSourceAssignment w j
      (groupedPrimeAssignment (sourceWidth w.configuration (wordSize k L)) p)=primeIntegerAssignment p := by
  funext i
  simp only [ungroupSourceAssignment,groupedPrimeAssignment,Equiv.apply_symm_apply,primeIntegerAssignment]

theorem integerPrimeTest_groupedPrimeAssignment
    (F : (SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q) → ℂ)
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q) :
    integerPrimeTest F (ungroupSourceAssignment w j
      (groupedPrimeAssignment (sourceWidth w.configuration (wordSize k L)) p))=F p := by
  rw [ungroupSourceAssignment_groupedPrimeAssignment,integerPrimeTest_at_prime]

theorem groupedSource_support_exists_prime (x : GroupedSourceIndex w j → ℤ)
    (hx : ∀i,x i∈groupedSourceIntegerSupport w j i) :
    ∃p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q,
      (∀i,p i∈sourceSurvivorShells w j i) ∧
      groupedPrimeAssignment (sourceWidth w.configuration (wordSize k L)) p=x := by
  let π := survivingPrimeEquiv k j (sourceWidth w.configuration (wordSize k L))
  have hh : ∀i,∃p : PrimeUpTo s.locations.Q,p∈sourceSurvivorShells w j i ∧
      (p.val:ℤ)=x (π.symm i) := by
    intro i
    have hm := hx (π.symm i)
    change x (π.symm i)∈integerPrimeSupport (sourceSurvivorShells w j (π (π.symm i))) at hm
    rw [π.apply_symm_apply] at hm
    exact Finset.mem_image.mp hm
  choose p hp he using hh
  refine ⟨p,hp,?_⟩
  funext i
  change ((p (π i)).val:ℤ)=x i
  exact (he (π i)).trans (congrArg x (π.symm_apply_apply i))

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
