import OAI.NumberTheory.JointDickman.Amplification.CandidateModularRoots
import OAI.NumberTheory.JointDickman.Amplification.FiniteWeightedUnion

namespace OAI

/-! # The finite set of primes defective for candidate root comparison -/

namespace JointDickman
open Finset

noncomputable def auxiliaryDivisors (B : ℕ) (z : ℤ) : Finset ℕ :=
  (auxiliaryPrimes B).filter (fun p => p ∣ z.natAbs)

theorem auxiliaryDivisors_mass {B : ℕ} {z : ℤ} (hz : z ≠ 0) {K : ℝ}
    (hsize : (z.natAbs : ℝ) ≤ Real.exp K) (hP : 0 < auxiliaryCutoff B) :
    (∑ p ∈ auxiliaryDivisors B z, 1/(p : ℝ)) ≤ K/(Real.log 2*auxiliaryCutoff B) := by
  apply large_prime_divisor_reciprocals hz _ _ (by exact_mod_cast hP) _ hsize
  · intro p hp
    obtain ⟨hp,hdiv⟩ := mem_filter.mp hp
    exact (auxiliaryPrimes_prime B p hp).mem_primeFactors hdiv (Int.natAbs_ne_zero.mpr hz)
  · intro p hp
    exact (mem_filter.mp (mem_filter.mp hp).1).2.le

open Classical in
noncomputable def candidateDefectPrimes {M : ℕ} (B : ℕ)
    (I : Finset (BlockCandidateIndex M)) : Finset ℕ :=
  I.biUnion (fun e => auxiliaryDivisors B (candidateQuotient e : ℤ) ∪
    (univ.biUnion (fun s : Fin M => auxiliaryDivisors B (candidateSiteValue e s))) ∪
    (I.biUnion (fun f => if e = f then ∅ else auxiliaryDivisors B (candidateRootDifference e f))))

open Classical in
theorem candidateDefectPrimes_mass {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) (I : Finset (BlockCandidateIndex M))
    (ha : ∀ e ∈ I, BlockCandidateAdmissible B L T H τ C e)
    (hr : Set.InjOn blockCandidateRoot (I : Set (BlockCandidateIndex M))) :
    (∑ p ∈ candidateDefectPrimes B I, 1/(p : ℝ)) ≤
      (I.card : ℝ)*(2+5*(M : ℝ)+8*I.card)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  let D := (B : ℝ)/(Real.log 2*auxiliaryCutoff B)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlocal (e : BlockCandidateIndex M) (he : e ∈ I) :
      (∑ p ∈ auxiliaryDivisors B (candidateQuotient e : ℤ) ∪
        (univ.biUnion (fun s : Fin M => auxiliaryDivisors B (candidateSiteValue e s))) ∪
        (I.biUnion (fun f => if e = f then ∅ else auxiliaryDivisors B (candidateRootDifference e f))),
        1/(p : ℝ)) ≤ (2+5*(M : ℝ)+8*I.card)*D := by
    have hc : (∑ p ∈ auxiliaryDivisors B (candidateQuotient e : ℤ), 1/(p : ℝ)) ≤ 2*D := by
      have hh := auxiliaryDivisors_mass (z := (candidateQuotient e : ℤ))
        (by exact_mod_cast (ha e he).2.2.2.1.ne')
        (by simpa only [Int.natAbs_natCast] using (candidate_quotient_exp_bounds (ha e he)).2) hP
      convert hh using 1; dsimp [D]; ring
    have hs : (∑ p ∈ univ.biUnion (fun s : Fin M => auxiliaryDivisors B (candidateSiteValue e s)),
        1/(p : ℝ)) ≤ (M : ℝ)*(5*D) := by
      apply (sum_biUnion_le_nonneg _ _ _ (fun _ => by positivity)).trans
      calc
        _ ≤ ∑ _s : Fin M, 5*D := sum_le_sum (fun s _ => by
          have hh := auxiliaryDivisors_mass (candidateSiteValue_ne_zero hB (ha e he) s)
            (candidateSiteValue_size hB hT hM (ha e he) s) hP
          convert hh using 1; dsimp [D]; ring)
        _ = _ := by simp
    have hd : (∑ p ∈ I.biUnion (fun f => if e = f then ∅ else
        auxiliaryDivisors B (candidateRootDifference e f)), 1/(p : ℝ)) ≤ (I.card : ℝ)*(8*D) := by
      apply (sum_biUnion_le_nonneg _ _ _ (fun _ => by positivity)).trans
      calc
        _ ≤ ∑ _f ∈ I, 8*D := sum_le_sum (fun f hf => by
          by_cases hef : e = f
          · simp only [hef,ite_true,sum_empty]; positivity
          · rw [ite_eq_right hef]
            have hroots : blockCandidateRoot e ≠ blockCandidateRoot f := fun h => hef (hr he hf h)
            have hh := auxiliaryDivisors_mass
              (candidateRootDifference_ne_zero (ha e he) (ha f hf) hroots)
              (candidateRootDifference_size hB hT hM (ha e he) (ha f hf)) hP
            convert hh using 1; dsimp [D]; ring)
        _ = _ := by simp
    calc
      _ ≤ ((∑ p ∈ auxiliaryDivisors B (candidateQuotient e : ℤ), 1/(p : ℝ))+
          ∑ p ∈ univ.biUnion (fun s : Fin M => auxiliaryDivisors B (candidateSiteValue e s)), 1/(p : ℝ))+
          ∑ p ∈ I.biUnion (fun f => if e = f then ∅ else
            auxiliaryDivisors B (candidateRootDifference e f)), 1/(p : ℝ) :=
        (sum_union_le_nonneg _ _ (fun p : ℕ => 1/(p : ℝ)) (fun _ => by positivity)).trans
          (add_le_add (sum_union_le_nonneg _ _ (fun p : ℕ => 1/(p : ℝ))
            (fun _ => by positivity)) le_rfl)
      _ ≤ 2*D+(M : ℝ)*(5*D)+(I.card : ℝ)*(8*D) := add_le_add (add_le_add hc hs) hd
      _ = _ := by ring
  calc
    _ ≤ ∑ e ∈ I, _ := sum_biUnion_le_nonneg _ _ _ (fun _ => by positivity)
    _ ≤ ∑ _e ∈ I, (2+5*(M : ℝ)+8*I.card)*D := sum_le_sum hlocal
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; dsimp [D]; ring

end JointDickman

end OAI
