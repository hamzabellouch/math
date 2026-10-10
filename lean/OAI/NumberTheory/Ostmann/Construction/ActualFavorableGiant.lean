import OAI.NumberTheory.Ostmann.Supply.FavorableTailPrimeMass
import OAI.NumberTheory.Ostmann.Construction.FavorableBlockSelection
import OAI.NumberTheory.Ostmann.Construction.FavorableGiantCutoff
import OAI.NumberTheory.Ostmann.Construction.EventualTailGiant

namespace OAI

/-! # The initial complete giant cell supplied by the actual summand tails -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.actual_favorable_giant
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) :
    ∃ N : ℕ, (∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q)) ∧
      ∀ᶠ L : ℝ in atTop, ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
        ∃ lo : ℝ, Real.exp ((1 / 20 : ℝ) * L) ≤ lo ∧ lo ≤ Real.exp ((9 / 10 : ℝ) * L) ∧
        ∃ F : Finset ℕ, F ⊆ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
          (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2) ∧
        ∃ G : ℤ, lo - 2 ≤ G ∧ (G : ℝ) ≤ (lo - 2) + 12 * Real.exp ((1 / 100 : ℝ) * L) ∧
          Real.exp (-(91 / 100 : ℝ) * L) ≤ smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
          smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100 : ℝ) * L ∧
          ((1 / 1000000 : ℝ) ^ 2 * (1 / 20) / 32) <
            ∑ p : smoothGiantPrimeRange G,
              smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G p *
                tailGiantEndpointMean A N F (summandTail A (summandTailCutoff (Real.exp L)) X) p := by
  obtain ⟨N, hN, hfav⟩ := h.favorable_tail_prime_mass ls hsize hA hB CM CH hM hMH Z hD hR P hPNT
  obtain ⟨_a, _, hgiant⟩ := h.eventual_giant_from_favorable_blocks P0 hsize hA hB N hN
    CM ((1 / 1000000 : ℝ) ^ 2) (1 / 20) hM (by norm_num) (by norm_num)
  refine ⟨N, hN, ?_⟩
  filter_upwards [hfav, hgiant, eventual_favorable_giant_cutoff,
    eventually_ge_atTop (1000 : ℝ)] with L hfav hgiant hcut hL X hX
  let F0 := favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
    (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2)
  have hF0 : F0 ⊆ logLogPrimeBand L := Finset.filter_subset _ _
  obtain ⟨lo, hlo, hhi, hmass⟩ := favorable_logarithmic_block L hL F0 hF0 (hfav X hX)
  let F := F0.filter (fun p : ℕ => lo ≤ Real.log (p : ℝ) ∧
    Real.log (p : ℝ) ≤ lo + 10 * Real.exp ((1 / 100 : ℝ) * L))
  have hFF (p : ℕ) (hp : p ∈ F) : p ∈ F0 := (Finset.mem_filter.mp hp).1
  have hFp (p : ℕ) (hp : p ∈ F) : p.Prime := (logLogPrimeBand_mem (hF0 (hFF p hp))).1
  have hFb (p : ℕ) (hp : p ∈ F) :
      p.Prime ∧ lo ≤ Real.log p ∧ Real.log p ≤ lo + 10 * Real.exp ((1 / 100 : ℝ) * L) :=
    ⟨hFp p hp, (Finset.mem_filter.mp hp).2⟩
  have hbal (p : ℕ) (hp : p ∈ F) : ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3 :=
    (Finset.mem_filter.mp (hFF p hp)).2.2.1
  have hγ (p : ℕ) (hp : p ∈ F) : let _ : Fact p.Prime := ⟨hFp p hp⟩;
      (1 / 1000000 : ℝ) ^ 2 ≤
        (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (tailDensityMask A N p) b‖ := by
    dsimp only
    let : NeZero p := ⟨(hFp p hp).ne_zero⟩
    rw [← tailFourierMass_eq A N p]
    exact (Finset.mem_filter.mp (hFF p hp)).2.2.2
  have hXL : Real.exp ((4 / 100 : ℝ) * L) ≤ Real.exp L :=
    Real.exp_le_exp.mpr (by linarith)
  obtain ⟨G, hGlo, hGhi, hmassG, hnormG, hmean⟩ := hgiant (Real.exp L) hXL le_rfl X hX
    lo (by convert hlo using 1; norm_num) hhi (hcut lo hhi) F hFb hbal hγ hmass.le
  exact ⟨lo, hlo, hhi, F, fun p hp => hFF p hp, G, hGlo, hGhi, hmassG, hnormG, hmean⟩

end Ostmann

end OAI
