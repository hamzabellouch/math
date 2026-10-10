import OAI.NumberTheory.JointDickman.Amplification.ArithmeticCandidateSum

namespace OAI

/-! # The original candidate weights and the masked residue kernel -/

namespace JointDickman
open Finset Classical

noncomputable def candidateArithmeticQuotient {M : ℕ} (u : ℕ)
    (e : BlockCandidateIndex M) : ℕ :=
  divisorEdgeInverse (candidateHigh e) (candidateLow e) (candidateQuotient e)
    (u+(e.1.1.val+1))

/-- Both endpoint divisibilities reconstruct the affine quotient, without
any counting-scale cutoff or squarefree-site assumption. -/
theorem candidateArithmeticQuotient_equation {B L T H M u : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1)))) :
    candidateHigh e*candidateLow e*candidateArithmeticQuotient u e+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)) := by
  obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
  have hlo := (mem_endpointSplits.mp hs.1).1
  have hhi := (mem_endpointSplits.mp hs.2).1
  have hloP := hlo.trans (show coefficientPrimeSet B (u+(e.1.1.val+1)) ⊆ auxiliaryPrimes B
    from filter_subset _ _)
  have hhiP := hhi.trans (show coefficientPrimeSet B (u+(e.1.2.val+1)) ⊆ auxiliaryPrimes B
    from filter_subset _ _)
  have hloD : candidateLow e ∣ u+(e.1.1.val+1) := (primeProduct_dvd_site_iff hloP).mpr hlo
  have hhiD : candidateHigh e ∣ u+(e.1.2.val+1) := (primeProduct_dvd_site_iff hhiP).mpr hhi
  have hapos : 0 < candidateHigh e :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hhiP hp)).pos)
  have hj := candidateLag_pos ha
  have heq : (candidateHigh e : ℤ)-candidateLow e = (candidateLag e : ℤ)*candidateQuotient e := by
    have h : (candidateHigh e : ℤ) = candidateLow e+(candidateLag e : ℤ)*candidateQuotient e :=
      by exact_mod_cast ha.2.2.2.2.1
    linarith
  have hcop : (candidateHigh e).Coprime (Int.natAbs (candidateLag e : ℤ)) := by
    rw [Int.natAbs_natCast]
    exact auxiliaryProduct_coprime_small hhiP hj (ha.2.2.1.le.trans hT)
  have hshift : ((u+(e.1.1.val+1) : ℕ) : ℤ)+(candidateLag e : ℤ) =
      (u+(e.1.2.val+1) : ℕ) := by
    rw [show (candidateLag e : ℤ) = (e.1.2.val : ℤ)-e.1.1.val from Int.ofNat_sub ha.1.le]
    push_cast
    ring
  obtain ⟨m,hm,_⟩ := natural_divisor_edge_inverse hapos ha.2.2.2.1
    (by omega : 0 < u+(e.1.1.val+1)) hloD heq hcop
    (by rw [hshift]; exact_mod_cast hhiD)
  have hinv : candidateArithmeticQuotient u e = m := divisorEdgeInverse_eq hapos hm
  rw [hinv]
  calc
    _ = candidateLow e*(candidateHigh e*m+1) := by ring
    _ = candidateLow e*(candidateQuotient e*((u+(e.1.1.val+1))/candidateLow e)) := by rw [hm]
    _ = candidateQuotient e*(candidateLow e*((u+(e.1.1.val+1))/candidateLow e)) := by ring
    _ = _ := by rw [Nat.mul_div_cancel' hloD]

theorem arithmeticCandidatePrimeFamily_transpose {M B : ℕ}
    (I : Finset (BlockCandidateIndex M)) (m : BlockCandidateIndex M → ℕ) (e : I) :
    (primeSiteTranspose I (auxiliaryPrimes B) (arithmeticCandidatePrimeFamily B I m) e).val =
      coefficientPrimeSet B (m e.val) := by
  ext p
  by_cases hp : p ∈ auxiliaryPrimes B
  · rw [primeSiteTranspose_mem I (auxiliaryPrimes B)
      (arithmeticCandidatePrimeFamily B I m) e ⟨p,hp⟩]
    simp [arithmeticCandidatePrimeFamily,arithmeticCandidateHit,coefficientPrimeSet,hp,e.property]
  · have hleft : p ∉ (primeSiteTranspose I (auxiliaryPrimes B)
        (arithmeticCandidatePrimeFamily B I m) e).val :=
      fun h => hp (mem_powerset.mp
        (primeSiteTranspose I (auxiliaryPrimes B) (arithmeticCandidatePrimeFamily B I m) e).property h)
    simp [coefficientPrimeSet,hp,hleft]

noncomputable def actualCandidateKernel (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) : Fin M → Fin M → ℝ :=
  let I := blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
  independentCandidateKernel B L T H M τ C
    (fun i => coefficientPrimeSet B (u+(i.val+1))) χ
    (primeSiteTranspose I (auxiliaryPrimes B)
      (arithmeticCandidatePrimeFamily B I (candidateArithmeticQuotient u)))

/-- Pointwise identification of the arithmetic kernel with the masked
model outside the three explicitly bounded exceptional events. -/
theorem actualCandidateKernel_eq_masked {B L T H M u : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ)
    (hforce : ∀ e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))),
      ¬ CandidateForcedWitness B e (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hactual : ¬ ArithmeticCoefficientHit B
      (blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
      (candidateArithmeticQuotient u))
    (hmasked : ¬ MaskedCoefficientEvent
      (blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
      (arithmeticPrimePatterns B M u) (fun p => (u : ZMod p.val))) :
    actualCandidateKernel B L T H M τ C χ u =
      independentCandidateKernel B L T H M τ C
        (fun i => coefficientPrimeSet B (u+(i.val+1))) χ
        (primeSiteTranspose _ (auxiliaryPrimes B)
          (maskedPrimeRootFamily _ (arithmeticPrimePatterns B M u) (fun p => (u : ZMod p.val)))) := by
  have heq := arithmetic_roots_eq_masked
    (blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (candidateArithmeticQuotient u) (fun _ he => (mem_blockCandidates.mp he).2)
    (fun _ he => candidateArithmeticQuotient_equation hT he) hforce hactual hmasked
  unfold actualCandidateKernel
  dsimp only
  rw [heq]

end JointDickman

end OAI
