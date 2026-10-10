import OAI.NumberTheory.JointDickman.Amplification.ArithmeticRootIdentification
import OAI.NumberTheory.JointDickman.Counting.BlockSquareHits
import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeQuotientSite

namespace OAI

/-! # The six arithmetic graph factors are the candidate root weight -/

namespace JointDickman
open Finset Classical

noncomputable def candidateCutoff {M : ℕ} (w : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (e : BlockCandidateIndex M) : ℝ :=
  w (candidateQuotient e)*v (candidateHigh e) (candidateQuotient e)*
    v (candidateLow e) (candidateQuotient e)

/-- Removing the selected squarefree factors leaves exactly the two
endpoint complements occurring in the candidate kernel. -/
theorem arithmetic_graph_candidate_weight {B L T H M u : ℕ} {τ C : ℝ}
    (w : ℕ → ℝ) (v : ℕ → ℕ → ℝ) {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hsq : ¬ BlockSquareHit B M u) :
    arithmeticGraphPairWeight B L τ C w v
      (candidateHigh e) (candidateLow e) (candidateQuotient e) (candidateLag e)
      (u+(e.1.1.val+1))/(B : ℝ) =
    candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
      (candidateCutoff w v) e
      (coefficientPrimeSet B (divisorEdgeInverse (candidateHigh e) (candidateLow e)
        (candidateQuotient e) (u+(e.1.1.val+1)))) := by
  obtain ⟨hs,hadm⟩ := mem_blockCandidates.mp he
  obtain ⟨hlo,_,_⟩ := mem_endpointSplits.mp hs.1
  obtain ⟨hhi,_,_⟩ := mem_endpointSplits.mp hs.2
  have hlowP : e.2.1 ⊆ auxiliaryPrimes B := hlo.trans (filter_subset _ _)
  have hhighP : e.2.2 ⊆ auxiliaryPrimes B := hhi.trans (filter_subset _ _)
  have hlowD : candidateLow e ∣ u+(e.1.1.val+1) :=
    (primeProduct_dvd_site_iff hlowP).mpr hlo
  have hhighD : candidateHigh e ∣ u+(e.1.2.val+1) :=
    (primeProduct_dvd_site_iff hhighP).mpr hhi
  have hno (i : Fin M) (p : ℕ) (hp : p ∈ auxiliaryPrimes B) : ¬ p^2 ∣ u+(i.val+1) :=
    fun hd => hsq ⟨i,p,hp,hd⟩
  have hqlow := coefficientPrimeSet_quotient hlowP hlowD (hno e.1.1)
  have hqhigh := coefficientPrimeSet_quotient hhighP hhighD (hno e.1.2)
  change coefficientPrimeSet B ((u+(e.1.1.val+1))/candidateLow e) = _ at hqlow
  change coefficientPrimeSet B ((u+(e.1.2.val+1))/candidateHigh e) = _ at hqhigh
  have hshift : (((u+(e.1.1.val+1) : ℕ) : ℤ)+(candidateLag e : ℤ)).toNat =
      u+(e.1.2.val+1) := by
    have hi : e.1.1.val ≤ e.1.2.val := (show e.1.1.val < e.1.2.val from hadm.1).le
    have hl : (candidateLag e : ℤ) = (e.1.2.val : ℤ)-e.1.1.val := Int.ofNat_sub hi
    rw [hl]
    omega
  unfold arithmeticGraphPairWeight arithmeticResidueWeight candidateRootWeight candidateCutoff
  rw [hshift]
  change (_ * (_ * regularResidueWeight B L τ C
      (coefficientPrimeSet B ((u+(e.1.1.val+1))/candidateLow e)) * _) *
    (_ * regularResidueWeight B L τ C
      (coefficientPrimeSet B ((u+(e.1.2.val+1))/candidateHigh e)) * _))/(B : ℝ) = _
  rw [hqlow,hqhigh]
  ring

end JointDickman

end OAI
