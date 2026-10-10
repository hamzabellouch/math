import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageWitness
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrameDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreSourceMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrame
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreOriginalReference HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily HistoryBulkFibreGiantApproximationReference
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkFibreSourceMean
open HistoryBulkSelectedPrincipalAmplitude HistoryBulkGiantCorrectedBounds
open HistoryPairGiantCoordinates HistoryBulkGoodPatternPrincipalFrame
open HistoryGiantOriginalMeanFactorization (Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def witnessFrame (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
    (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
      SelectedBulkSample C l → ℤ → ℤ → ℂ)
    {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (r : Witness C outside σ a x y J w P Q i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C x i) ≠ 0)
    (he : choicesMass C.sources _ _ l (rightChoices C y i) ≠ 0)
    (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
      |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
    (hp : ∀q∈outside,q.Prime) : Frame (l:=l) C outside :=
  let hm := plain_reference_masses C σ a r.bulk ha r.bulk_pos
  let hg := hcell r.giant r.giant_pos.ne'
  { leftSource := fibreAssignment C a r.bulk
    rightSource := permuteAssignment C σ (fibreAssignment C a r.bulk)
    s := i.1.val
    t := i.1.val
    P := P r.giant
    Q := Q r.giant
    leftChoices := leftChoices C x i
    rightChoices := rightChoices C y i
    left_mass := hm.1
    right_mass := hm.2
    left_choices_mass := hc
    right_choices_mass := he
    plus_pos := hg.1
    minus_pos := hg.2.1
    plus_cell := hg.2.2.1
    minus_cell := hg.2.2.2
    left_supported := r.supported.1
    right_supported := r.supported.2
    matching := plain_reference_matching C σ a i.1.val i.1.val
      (leftChoices C x i) (rightChoices C y i) r.bulk _ _
    outside_primes := hp }

end Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrame

end

end OAI
