import OAI.NumberTheory.Ostmann.Characters.SparseTailMassBound
import OAI.NumberTheory.Ostmann.Construction.TailBandCollision
import OAI.NumberTheory.Ostmann.Construction.TailFourierMass
import OAI.NumberTheory.Ostmann.ZeroDensity.ExceptionalPrimeDeletion

namespace OAI

/-! # Proposition 5.1: favorable primes for the actual infinite summand tails -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.favorable_tail_prime_mass
    (ls : PublishedAdditiveLargeSieve) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) :
    ∃ N : ℕ, (∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q)) ∧
      ∀ᶠ L : ℝ in atTop, ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
        (3 / 20 : ℝ) * L <
          ∑ p ∈ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
            (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2), (p : ℝ)⁻¹ := by
  obtain ⟨N, hN, hsmall⟩ := h.sparse_tail_mass_bound ls hsize hA hB CM hM Z hD hR P hPNT
  obtain ⟨a, _, hcollision⟩ := h.tail_band_collision_budget hsize hA hB N hN CM hM.lower
  refine ⟨N, hN, ?_⟩
  filter_upwards [hsmall, hcollision, eventual_logLogPrimeBand_harmonic_le hMH,
    eventual_sparse_mass_error CH 20 (4 * CM + 4 * Real.log 2 + 2 * Real.log 4 / a),
    eventually_ge_atTop (50 : ℝ)] with L hsmall hcollision hbandmass herr hL
  obtain ⟨exception, hsmall⟩ := hsmall
  intro X hX
  by_contra hfail
  have hfail' : (∑ p ∈ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
      (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2), (p : ℝ)⁻¹) ≤ (3 / 20 : ℝ) * L :=
    le_of_not_gt hfail
  let R := sparseTransformPrimes (logLogPrimeBand L) (tailSupport A N)
    (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2)
  have hRsub : R ⊆ logLogPrimeBand L := Finset.filter_subset _ _
  have hRprime (p : ℕ) (hp : p ∈ R) : p.Prime := (logLogPrimeBand_mem (hRsub hp)).1
  have hmass : (69 / 100 : ℝ) * L ≤ ∑ p ∈ R, (p : ℝ)⁻¹ := by
    have hh := logLog_sparse_mass_lower hMH L (by linarith) (tailSupport A N)
      (fun p => Finset.range p \ tailSupport A N p)
      (fun p => residueMass (summandTail A (summandTailCutoff (Real.exp L)) X)
        (fun _ => 1 / ((summandTail A (summandTailCutoff (Real.exp L)) X).card : ℝ)) p)
      (fun p => fiberMass (summandTail B (summandTailCutoff (Real.exp L)) X)
        (fun _ => 1 / ((summandTail B (summandTailCutoff (Real.exp L)) X).card : ℝ))
        (negativeResidue p))
      (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2)
      (20 * L + (4 * CM + 4 * Real.log 2 + 2 * Real.log 4 / a))
      (fun p hp => tailSupport_nonempty hA N p (logLogPrimeBand_mem hp).1.pos)
      (fun p hp => tailSupport_complement_nonempty hB (logLogPrimeBand_mem hp).1.pos
        (hN p (logLogPrimeBand_mem hp).1))
      (fun p _ => tailSupport_card_add_complement A N p)
      (hcollision X hX) hfail'
    exact (herr _ le_rfl).trans hh
  obtain ⟨Q, hQR, hQmass, havoid⟩ := exists_exceptional_prime_deletion_mass R hRprime
    exception L hL hmass
  let p := primeFamilyEnumeration Q
  have hp (i : Fin Q.card) : (p i).Prime :=
    hRprime _ (hQR (primeFamilyEnumeration_mem Q i))
  let (i : Fin Q.card) : Fact (p i).Prime := ⟨hp i⟩
  let : NeZero (∏ i, p i) := ⟨(Finset.prod_pos (fun i _ => (hp i).pos)).ne'⟩
  have hpR (i : Fin Q.card) : p i ∈ R := hQR (primeFamilyEnumeration_mem Q i)
  have hpband (i : Fin Q.card) : p i ∈ logLogPrimeBand L := hRsub (hpR i)
  have hbal (i : Fin Q.card) :
      (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N (p i)) ∧
        residueDensity (tailDensityMask A N (p i)) ≤ 2 / 3 := by
    apply (tailDensityMask_balanced_iff A N _ (hp i).pos).mpr
    exact ⟨(Finset.mem_filter.mp (hpR i)).2.1, (Finset.mem_filter.mp (hpR i)).2.2.1⟩
  have hL1 (i : Fin Q.card) : (p i : ℝ)⁻¹ * ∑ b,
      ‖normalizedResidueTransform (tailDensityMask A N (p i)) b‖ ≤ (1 / 1000000 : ℝ) ^ 2 := by
    rw [← tailFourierMass_eq]
    exact (Finset.mem_filter.mp (hpR i)).2.2.2.le
  have hsum : (∑ i, (p i : ℝ)⁻¹) = ∑ q ∈ Q, (q : ℝ)⁻¹ :=
    primeFamilyEnumeration_sum Q (fun q => (q : ℝ)⁻¹)
  have hmassQ : (∑ i, (p i : ℝ)⁻¹) ≤ L := by
    rw [hsum]
    apply le_trans _ hbandmass
    exact Finset.sum_le_sum_of_subset_of_nonneg (hQR.trans hRsub) (fun _ _ _ => by positivity)
  have hbad := hsmall X hX Q.card p
    (primeFamilyEnumeration_coprime Q (fun q hq => hRprime q (hQR hq))) hpband
    (fun i => (hbal i).1) (fun i => (hbal i).2)
    (1 / 1000000) (by norm_num) (by norm_num) hL1 hmassQ
    (by simpa only [p, primeFamilyEnumeration_prod] using havoid)
  rw [hsum] at hbad
  linarith

end Ostmann

end OAI
