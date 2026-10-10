import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentActions
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePrefix
import OAI.NumberTheory.Ostmann.Characters.TemplateParityActions
import OAI.NumberTheory.Ostmann.Characters.TemplateWeightedHilbertComparison

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries ParityActions OneSidedPhase
attribute [local instance] Classical.propDecidable

theorem prefixConstituentPermutation_shells (k n : ℕ) (width : Role → ℕ)
    (m : ℕ) (hm : m≤width .word) {Q : ℕ}
    (E : (schedule k (n+1)).Constituent width → Finset (PrimeUpTo Q))
    (bulk : Fin m → Finset (PrimeUpTo Q))
    (hbulk : ∀z : BulkSlot k n m,E (prefixBulkEmbedding k n width m hm z)=bulk z.2)
    (σ : Reassignments k n m) :
    ∀i,E (prefixConstituentPermutation k n width m hm σ i)=E i := by
  intro i
  by_cases hi : i∈Set.range (prefixBulkEmbedding k n width m hm)
  · obtain ⟨z,rfl⟩ := hi
    rw [prefixConstituentPermutation_bulk,hbulk,hbulk,bulkPermutation_position]
  · exact congrArg E (Equiv.Perm.viaEmbedding_apply_of_notMem _ _ i hi)

section
variable (k n : ℕ) (width : Role → ℕ) (m : ℕ) (hm : m≤width .word) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k (n+1)) width Q)
    (χ : PrimeCharacterData (schedule k (n+1)) width Q)
    (a : PrimeTranslationData (schedule k (n+1)) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)

def terminalParityIntegrand (σ : Reassignments k n m)
    (x : (schedule k (n+1)).Constituent width → PrimeUpTo Q) (s : ↥(S [])) : ℂ :=
  unitTerminalRootIntegrand k (n+1) width ζ χ a B V extra mask X Δ W S
    (constituentAssignment (schedule k (n+1)) width
      (prefixConstituentPermutation k n width m hm σ) x) s

variable (E : (schedule k (n+1)).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i)) (bulk : Fin m → Finset (PrimeUpTo Q))
    (hbulk : ∀z : BulkSlot k n m,E (prefixBulkEmbedding k n width m hm z)=bulk z.2)

include hbulk

theorem terminalParityIntegrand_mean (σ : Reassignments k n m) :
    (constituentPrimePrior (schedule k (n+1)) width E hE).cmean (fun x =>
      ∑s : ↥(S []),terminalParityIntegrand k n width m hm ζ χ a B V extra mask X Δ W S σ x s)=
    unitAmplitude k (n+1) width ζ χ a B V extra mask X Δ W S E hE := by
  unfold terminalParityIntegrand
  exact (constituentPrimePrior_cmean_assignment _ width E hE _
    (prefixConstituentPermutation_shells k n width m hm E bulk hbulk σ)
    (fun x => ∑s : ↥(S []),unitTerminalRootIntegrand k (n+1) width ζ χ a B V extra mask X Δ W S x s)).trans
    (unitAmplitude_eq_terminalRootMean k (n+1) width ζ χ a B V extra mask X Δ W S E hE).symm

theorem terminalParityIntegrand_norm_mean (σ : Reassignments k n m) :
    (constituentPrimePrior (schedule k (n+1)) width E hE).mean (fun x =>
      ∑s : ↥(S []),‖terminalParityIntegrand k n width m hm ζ χ a B V extra mask X Δ W S σ x s‖^2)=
    (constituentPrimePrior (schedule k (n+1)) width E hE).mean (fun x =>
      ∑s : ↥(S []),‖unitTerminalRootIntegrand k (n+1) width ζ χ a B V extra mask X Δ W S x s‖^2) := by
  unfold terminalParityIntegrand
  exact constituentPrimePrior_mean_assignment _ width E hE _
    (prefixConstituentPermutation_shells k n width m hm E bulk hbulk σ)
    (fun x => ∑s : ↥(S []),‖unitTerminalRootIntegrand k (n+1) width ζ χ a B V extra mask X Δ W S x s‖^2)

theorem terminalParity_comparison {e : ℝ} (he : 0≤e)
    (hoff : ∀σ ρ : Reassignments k n m,σ≠ρ →
      ‖(constituentPrimePrior (schedule k (n+1)) width E hE).cmean (fun x =>
        ∑s : ↥(S []),conj (terminalParityIntegrand k n width m hm ζ χ a B V extra mask X Δ W S σ x s)*
          terminalParityIntegrand k n width m hm ζ χ a B V extra mask X Δ W S ρ x s)‖≤e) :
    ‖unitAmplitude k (n+1) width ζ χ a B V extra mask X Δ W S E hE‖^2 ≤
      (Fintype.card ↥(S []) : ℝ)*
        ((constituentPrimePrior (schedule k (n+1)) width E hE).mean (fun x =>
          ∑s : ↥(S []),‖unitTerminalRootIntegrand k (n+1) width ζ χ a B V extra mask X Δ W S x s‖^2) /
          (factorialCount n m : ℝ)+e) := by
  apply TemplateWeightedHilbert.weighted_parity_permutation_comparison n m
    (constituentPrimePrior (schedule k (n+1)) width E hE)
    (fun σ => terminalParityIntegrand k n width m hm ζ χ a B V extra mask X Δ W S
      ((genericReassignmentEquiv k n m).symm σ)) _ he
  · intro σ
    exact terminalParityIntegrand_mean k n width m hm ζ χ a B V extra mask X Δ W S E hE bulk hbulk _
  · intro σ
    exact (terminalParityIntegrand_norm_mean k n width m hm ζ χ a B V extra mask X Δ W S E hE bulk hbulk _).le
  · intro σ ρ hne
    apply hoff
    exact fun h => hne ((genericReassignmentEquiv k n m).symm.injective h)

end
end Ostmann.Characters.Template

end

end OAI
