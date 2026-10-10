import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkReferenceFrequencyFamily
open HistoryBulkActualPrincipalSourceReindexFamily
attribute [local instance] Classical.propDecidable
local instance actualBSquareBasicInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : Background C l → Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def sourceMean (probability corrected mixed : Bool) : ℂ :=
  (backgroundPrior C l).cmean (fun bg => (selectedBulkPrior C l).cmean (fun u =>
    rootExpression C outside σ (J bg) w P Q hactual hl houtside hw hpos hcell hp hAd hout hV
      bg u probability corrected mixed))

def frequencyError (corrected mixed : Bool) : ℝ :=
  ∑v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
    ∑f : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
      ∑g : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
        ‖(FinitePrior.pair (backgroundPrior C l) (selectedBulkPrior C l)).cmean
            (fun a => expression C outside σ (J a.1) w P Q hactual hl houtside hw hpos hcell hp
              hAd hout hV a.1 a.2 (v,(f,g)) false corrected mixed) -
          (FinitePrior.pair (backgroundPrior C l) (selectedBulkPrior C l)).cmean
            (fun a => expression C outside σ (J a.1) w P Q hactual hl houtside hw hpos hcell hp
              hAd hout hV a.1 a.2 (v,(f,g)) true corrected mixed)‖

theorem norm_sourceMean_sub_le_frequencyError (corrected mixed : Bool) :
    ‖sourceMean C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV
        false corrected mixed -
      sourceMean C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV
        true corrected mixed‖ ≤
      frequencyError C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV
        corrected mixed := by
  unfold sourceMean rootExpression
  simp_rw [FinitePrior.cmean_sum]
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
        ‖(backgroundPrior C l).cmean (fun bg => (selectedBulkPrior C l).cmean (fun u =>
          expression C outside σ (J bg) w P Q hactual hl houtside hw hpos hcell hp hAd hout hV
            bg u i false corrected mixed)) -
         (backgroundPrior C l).cmean (fun bg => (selectedBulkPrior C l).cmean (fun u =>
          expression C outside σ (J bg) w P Q hactual hl houtside hw hpos hcell hp hAd hout hV
            bg u i true corrected mixed))‖ := norm_sum_le _ _
    _ = _ := by
      simp only [frequencyError, Index, RootFrequencyIndex, Fintype.sum_prod_type,
        FinitePrior.pair_cmean]

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
