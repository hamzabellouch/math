import OAI.Combinatorics.ContingencyTables.Dense.DenseCandidateCounts
import OAI.Combinatorics.ContingencyTables.Transport.IndexedTableLaw
import OAI.Combinatorics.ContingencyTables.Machines.VectorRetryProgram

namespace OAI

/-! # Complete indexed integer law of a bounded dense draw -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical
noncomputable section

theorem candidateCounts_indexed {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (cap : List Bool)
    (hcap : ∀ j : Fin (m*n),FairBits.offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d≤cap.length) :
    candidateCounts ((tabulateDenseWalk ((marginCode R,marginCode P),(d,h)),cap),
      ((marginCode R,marginCode P),(d,h)))=
    List.ofFn (fun k => (IndexedTableLaw.law R P (le_refl (∑ i,R i))
      ((denseTrialCounts R P d hd hR hP finProdFinEquiv h
        (canonicalOrigin (m*n) d (by omega))).push
          (trialSuccess R P d finProdFinEquiv htotal))).count (some k)) := by
  unfold candidateCounts
  rw [completionCandidates_code R P htotal,List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  simp only [Function.comp_apply]
  rw [candidateCount_actual R P hd hq hR hP h cap hcap,
    IndexedTableLaw.count_some R P htotal]
  unfold IndexedTableLaw.tableAt
  simp_rw [denseTrial_success_count R P d hd hR hP finProdFinEquiv htotal]

/-- Full retry numerators are obtained by the polynomial binary vector
recurrence, after the accepted-trial vector has been tabulated once. -/
theorem denseRetryVector_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hd : 14≤d) (hq : m*n≤d)
    (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j) (htotal : ∑ i,R i=∑ j,P j)
    (h : ℕ) (cap xs : List Bool)
    (hcap : ∀ j : Fin (m*n),FairBits.offsetBitLength
      (integerWidth R P d (finProdFinEquiv.symm j)) h d≤cap.length)
    (fallback : Table R P) :
    VectorRetryPrograms.counts ((xs,2^denseTrialBits R P d finProdFinEquiv h),
      (candidateCounts ((tabulateDenseWalk ((marginCode R,marginCode P),(d,h)),cap),
        ((marginCode R,marginCode P),(d,h))),
        (IndexedTableLaw.index R P (le_refl (∑ i,R i)) fallback).val))=
    List.ofFn (((IndexedTableLaw.law R P (le_refl (∑ i,R i))
      ((denseTrialCounts R P d hd hR hP finProdFinEquiv h
        (canonicalOrigin (m*n) d (by omega))).push
          (trialSuccess R P d finProdFinEquiv htotal))).retry
            (IndexedTableLaw.index R P (le_refl (∑ i,R i)) fallback) xs.length).count) := by
  rw [candidateCounts_indexed R P hd hq hR hP htotal h cap hcap]
  exact VectorRetryPrograms.counts_actual _ xs _

end
end ContingencyTables.DensePrograms

end OAI
