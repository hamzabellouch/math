import OAI.NumberTheory.JointDickman.Probability.ArithmeticKernelPeriod

namespace OAI

/-! # The counting-scale edge condition is a single monotone cutoff -/

namespace JointDickman
open Finset Classical

theorem divisorEdgeNew_iff_threshold {a b c n m N : ℕ} {j : ℤ}
    (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hba : b ≤ a)
    (hn : 0 < n) (hbn : b ∣ n) (han : (a : ℤ) ∣ (n : ℤ)+j)
    (hm : divisorEdgeInverse a b c n = m) (he : c*n = a*b*m+b) :
    n ∈ divisorEdgeNew a b c N j ↔ c*n < b*(N+1) := by
  have hcut : c*n < b*(N+1) ↔ a*m < N := by
    rw [he]
    constructor <;> intro h <;> nlinarith
  rw [hcut]
  constructor
  · intro h
    simpa only [hm] using (mem_filter.mp h).2.2.2.1
  · intro h
    have hbm : b*m < N := (Nat.mul_le_mul_right m hba).trans_lt h
    have hnN : n ≤ b*N := by
      have h1 : a*m+1 ≤ N := h
      have h2 : c*n ≤ b*N := by nlinarith
      have h3 : n ≤ c*n := Nat.le_mul_of_pos_left n hc
      exact h3.trans h2
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hn,hnN⟩,hbn,han,
      by simpa only [hm] using h,by simpa only [hm] using hbm⟩

theorem candidateGraphTriple_edge_iff {B L T H M u N : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1)))) :
    u+(e.1.1.val+1) ∈ graphTripleEdges N (candidateGraphTriple B e) ↔
      candidateQuotient e*(u+(e.1.1.val+1)) < candidateLow e*(N+1) := by
  obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
  have hlo := (mem_endpointSplits.mp hs.1).1
  have hhi := (mem_endpointSplits.mp hs.2).1
  have hloP := hlo.trans (show coefficientPrimeSet B (u+(e.1.1.val+1)) ⊆ auxiliaryPrimes B
    from filter_subset _ _)
  have hhiP := hhi.trans (show coefficientPrimeSet B (u+(e.1.2.val+1)) ⊆ auxiliaryPrimes B
    from filter_subset _ _)
  have hb : 0 < candidateLow e := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hloP hp)).pos)
  have haa : 0 < candidateHigh e := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hhiP hp)).pos)
  have hbd : candidateLow e ∣ u+(e.1.1.val+1) := (primeProduct_dvd_site_iff hloP).mpr hlo
  have had : candidateHigh e ∣ u+(e.1.2.val+1) := (primeProduct_dvd_site_iff hhiP).mpr hhi
  have hshift : ((u+(e.1.1.val+1) : ℕ) : ℤ)+(candidateLag e : ℤ) =
      (u+(e.1.2.val+1) : ℕ) := by
    rw [show (candidateLag e : ℤ) = (e.1.2.val : ℤ)-e.1.1.val from Int.ofNat_sub ha.1.le]
    push_cast
    ring
  have hcoeff := ha.2.2.2.2.2.2.2.2.1
  unfold graphTripleEdges
  rw [candidateGraphTriple_lag ha]
  change _ ∈ divisorEdgeNew (candidateHigh e) (candidateLow e)
    (∏ p ∈ coefficientPrimeSet B (candidateQuotient e), p) N (candidateLag e) ↔ _
  rw [← hcoeff]
  apply divisorEdgeNew_iff_threshold haa hb ha.2.2.2.1
    (by have := ha.2.2.2.2.1; omega) (by omega) hbd
    (by rw [hshift]; exact_mod_cast had) rfl
  exact (candidateArithmeticQuotient_equation hT he).symm

noncomputable def finiteCandidateCutoff {M : ℕ} (B T N u : ℕ)
    (e : BlockCandidateIndex M) : ℝ :=
  if candidateQuotient e*(u+(e.1.1.val+1)) < candidateLow e*(N+1) then
    candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e else 0

theorem finiteCandidateCutoff_bounds {M : ℕ} (B T N u : ℕ) (e : BlockCandidateIndex M) :
    0 ≤ finiteCandidateCutoff B T N u e ∧ finiteCandidateCutoff B T N u e ≤ 1 := by
  unfold finiteCandidateCutoff candidateCutoff amplificationOuterWeight amplificationInnerWeight
  split_ifs
  · have h1 := amplificationBump_bounds (Real.log (candidateQuotient e)/(B : ℝ))
    have h2 := amplificationBump_bounds ((candidateHigh e : ℝ)/(T*candidateQuotient e))
    have h3 := amplificationBump_bounds ((candidateLow e : ℝ)/(T*candidateQuotient e))
    exact ⟨mul_nonneg (mul_nonneg h1.1 h2.1) h3.1,
      (mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 (by norm_num)) h3.2 h3.1 (by norm_num)).trans_eq (by norm_num)⟩
  · exact ⟨le_rfl,by norm_num⟩

end JointDickman

end OAI
