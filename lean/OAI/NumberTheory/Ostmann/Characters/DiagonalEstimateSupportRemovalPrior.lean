import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateIntegerPriorSource
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingOrigins
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTransportPrior

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template TemplateSupportRemoval Template.OneSidedPhase
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale
open TemplateOneSidedSupportSurviving TemplateOneSidedSupportTransport
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)

abbrev GroupedSourceIndex (j : ℕ) :=
  Σi : SurvivingSlot k j,Fin (survivingWidth k j
    (sourceWidth w.configuration (wordSize k L)) i)

def groupedSourceIntegerSupport (j : ℕ) : GroupedSourceIndex w j → Finset ℤ :=
  fun i => sourceSurvivorIntegerSupport w j
    (survivingPrimeEquiv k j (sourceWidth w.configuration (wordSize k L)) i)

def groupedSourceIntegerWeight (j : ℕ) : GroupedSourceIndex w j → ℤ → ℝ :=
  fun i => sourceSurvivorIntegerWeight w j
    (survivingPrimeEquiv k j (sourceWidth w.configuration (wordSize k L)) i)

def ungroupSourceAssignment (j : ℕ) (x : GroupedSourceIndex w j → ℤ) :
    SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) → ℤ :=
  fun i => x ((survivingPrimeEquiv k j (sourceWidth w.configuration (wordSize k L))).symm i)

theorem groupedSource_fullProductMean (j : ℕ)
    (F : (SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) → ℤ) → ℂ) :
    fullProductMean (sourceSurvivorIntegerSupport w j) (sourceSurvivorIntegerWeight w j) F =
      fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
        (fun x => F (ungroupSourceAssignment w j x)) := by
  have hh := fullProductMean_reindex
    (survivingPrimeEquiv k j (sourceWidth w.configuration (wordSize k L)))
    (sourceSurvivorIntegerSupport w j) (sourceSurvivorIntegerWeight w j)
    (fun x => F (ungroupSourceAssignment w j x))
  have he : (fun a => F (ungroupSourceAssignment w j
      (fun i => a (survivingPrimeEquiv k j (sourceWidth w.configuration (wordSize k L)) i))))=F := by
    funext a
    congr 1
    funext i
    exact congrArg a ((survivingPrimeEquiv k j (sourceWidth w.configuration (wordSize k L))).apply_symm_apply i)
  rw [he] at hh
  exact hh.symm

theorem sourceSurvivorPrior_cmean_eq_grouped_integer (j : ℕ)
    (F : (SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q) → ℂ) :
    (sourceSurvivorPrior w j).cmean F =
      fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
        (fun x => integerPrimeTest F (ungroupSourceAssignment w j x)) := by
  rw [sourceSurvivorPrior_cmean_eq_integer]
  exact groupedSource_fullProductMean w j _

theorem sourceHistoryPairMean_eq_grouped_integer (j : ℕ) (hj : j<k)
    (B V : (l:ℕ) → State k (l+1) → ℤ) (hc : 0<c) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) :
    sourceHistoryPairMean w j hj B V P e h h' =
      fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
        (fun x => integerPrimeTest (cutoffSourceSurvivorKernel w j hj B V P e h h')
          (ungroupSourceAssignment w j x)) := by
  rw [sourceHistoryPairMean_eq_integer w j hj B V hc]
  exact groupedSource_fullProductMean w j _

theorem groupedSource_fullProductMean_error (j : ℕ)
    (F G : (SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) → ℤ) → ℂ) :
    ‖fullProductMean (sourceSurvivorIntegerSupport w j) (sourceSurvivorIntegerWeight w j) F-
      fullProductMean (sourceSurvivorIntegerSupport w j) (sourceSurvivorIntegerWeight w j) G‖ =
    ‖fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
        (fun x => F (ungroupSourceAssignment w j x))-
      fullProductMean (groupedSourceIntegerSupport w j) (groupedSourceIntegerWeight w j)
        (fun x => G (ungroupSourceAssignment w j x))‖ := by
  rw [groupedSource_fullProductMean w j F,groupedSource_fullProductMean w j G]

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
