import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceWeightedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
open Construction Conclusion HistoryGiantReferenceMean HistoryBulkSourceDisintegration
open HistoryGiantOriginalMeanFactorization (Choices)
open HistoryPairBulkTransport
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C)
variable (J : SelectedBulkSample C l → ℤ → ℤ → ℂ)

def weightedFibreReferenceTerm (K : ℕ) (y₀ : SelectedBulkSample C l) (P₀ Q₀ : ℤ)
    (hs : FibreSupported C outside σ a s t c e y₀ P₀ Q₀)
    (y : SelectedBulkSample C l) (P Q : ℤ) : ℂ :=
  HistoryBulkFixedReferenceTerm.referenceTerm C (frequencyBound Bs BD Bz k L) outside l K σ
    (fibreAssignment C a y₀) (fibreAssignment C a y) s t P₀.toNat Q₀.toNat c e
    hs.1 hs.2 (bulkSize k L/2) (bulkSize k L/2)
    C.scale C.bulkBin C.spectatorBin C.giantCenter (J y) P Q

theorem weightedFibreTerm_eq_weightedFibreReferenceTerm
    {spectator : PrimeSource}
    (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
    (K : ℕ) (hle : l≤K) (hl : l≤k)
    (y₀ : SelectedBulkSample C l) (P₀ Q₀ : ℤ)
    (hs : FibreSupported C outside σ a s t c e y₀ P₀ Q₀)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hy₀ : 0 < (selectedBulkPrior C l).mass y₀)
    (hc : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c≠0)
    (he : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l e≠0)
    (houtside : ∀q∈outside,∃p : spectator.Sample,(p:ℕ)=q)
    (y : SelectedBulkSample C l) (P Q : ℤ)
    (hy : (selectedBulkPrior C l).mass y≠0) (hp : 0<P) (hq : 0<Q) :
    weightedFibreTerm C outside σ a s t c e J y P Q =
      weightedFibreReferenceTerm C outside σ a s t c e J K y₀ P₀ Q₀ hs y P Q := by
  exact hactual outside l K hle hl σ (fibreAssignment C a y₀) (fibreAssignment C a y)
    s t P₀.toNat Q₀.toNat c e hs.1 hs.2 (bulkSize k L/2) (bulkSize k L/2)
    C.scale C.bulkBin C.spectatorBin C.giantCenter (J y) P Q
    (fibreAssignment_nonbulk_fixed C a y y₀)
    (ne_of_gt (fibreAssignment_mass_pos C a y₀ ha hy₀))
    (ne_of_gt (fibreAssignment_mass_pos C a y ha
      (lt_of_le_of_ne ((selectedBulkPrior C l).mass_nonneg y) (Ne.symm hy))))
    hc he hp hq houtside

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

end

end OAI
