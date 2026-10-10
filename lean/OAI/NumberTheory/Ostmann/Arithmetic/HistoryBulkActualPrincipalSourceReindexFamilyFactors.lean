import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyFalse

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamily
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkReferencePeriodicMeanSource
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
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
  (bg : Background C l) (u : SelectedBulkSample C l)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : Block p → CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))

theorem densityPatternFactor_eq (probability corrected mixed : Bool) :
    densityPatternFactor
      (referenceFamily C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV bg u i)
      (densitySources C outside σ J w P Q hactual hl houtside hw hpos hcell hp bg u i)
      probability corrected mixed
      (staticMask C outside σ J w P Q hactual hl houtside hw hpos hcell hp bg u i) p b =
    selectedTerm C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV bg u i p b
      probability corrected mixed := by
  by_cases hu : (selectedBulkPrior C l).mass u≠0
  · cases hr : selectedOuter C outside σ J w P Q hactual hl houtside hw hpos bg i p b with
    | none =>
      simp only [densityPatternFactor, densityFactor, principalPatternFactor, principalValue,
        optionalPrincipalBFactor, referenceFamily, densitySources, staticMask, selectedTerm,
        hr, Option.elim_none, and_false, ↓reduceIte,
        mul_zero, zero_mul]
    | some R =>
      simp only [densityPatternFactor, densityFactor, principalPatternFactor, principalValue,
        optionalPrincipalBFactor, referenceFamily, densitySources, staticMask, selectedTerm,
        squareTerm, hr, Option.elim_some]
      rw [dite_eq_left hu, dite_eq_left hu]
      simp only [and_iff_right hu]
      change _ = (if staticCondition C outside σ bg u (R.frame (l:=l) hcell hp) then 1 else 0) * _
      exact mul_left_comm _ _ _
  · simp only [densityPatternFactor, principalPatternFactor, principalValue,
      optionalPrincipalBFactor, referenceFamily, staticMask, selectedTerm,
      hu, ↓reduceDIte, false_and, ↓reduceIte, mul_zero]
    cases selectedOuter C outside σ J w P Q hactual hl houtside hw hpos bg i p b with
    | none => rfl
    | some R => simp only [Option.elim_some, squareTerm, hu, ↓reduceDIte]

theorem densityPatternFactor_false_eq :
    ∀ corrected mixed : Bool,
    densityPatternFactor
      (referenceFamily C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV bg u i)
      (densitySources C outside σ J w P Q hactual hl houtside hw hpos hcell hp bg u i)
      false corrected mixed
      (staticMask C outside σ J w P Q hactual hl houtside hw hpos hcell hp bg u i) p b =
    (selectedOuter C outside σ J w P Q hactual hl houtside hw hpos bg i p b).elim 0
      (fun R=>R.squareBTerm (l:=l) hcell hp (hAd (R.frame (l:=l) hcell hp)) hout hV corrected mixed u) := by
  intro corrected mixed
  rw [densityPatternFactor_eq]
  unfold selectedTerm
  cases selectedOuter C outside σ J w P Q hactual hl houtside hw hpos bg i p b with
  | none => rfl
  | some R => exact squareTerm_false C outside σ J w P Q hcell hp hAd hout hV bg u i p b R corrected mixed

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamily

end

end OAI
