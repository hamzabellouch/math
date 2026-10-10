import OAI.NumberTheory.Ostmann.Construction.ActualFavorableGiant
import OAI.NumberTheory.Ostmann.Construction.FavorableBlockEndpoint

namespace OAI

/-! # The giant with the endpoint chosen from its favorable block -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.selected_endpoint_giant
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (P : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) :
    ∃ N : ℕ, (∀ q, q.Prime → Disjoint (tailResidues A N q) (negTailResidues B N q)) ∧
      ∀ k : ℕ, ∀ᶠ reference : ℕ in atTop,
        let L := Real.log (Real.log (reference : ℝ))
        ∃ lo : ℝ, Real.exp ((1 / 20 : ℝ) * L) ≤ lo ∧ lo ≤ Real.exp ((9 / 10 : ℝ) * L) ∧
        ∃ F : Finset ℕ, F ⊆ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
          (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2) ∧
        ∃ Y : ℝ, ∃ hi : ℕ, (hi : ℝ) = Real.exp Y ∧
          2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y ∧
          Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 ∧
          Real.exp ((4 / 100 : ℝ) * L) ≤ Y ∧ Y ≤ Real.exp L ∧
        ∃ G : ℤ, lo - 2 ≤ G ∧ (G : ℝ) ≤ (lo - 2) + 12 * Real.exp ((1 / 100 : ℝ) * L) ∧
          Real.exp (-(91 / 100 : ℝ) * L) ≤ smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
          smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100 : ℝ) * L ∧
          ((1 / 1000000 : ℝ) ^ 2 * (1 / 20) / 32) <
            ∑ p : smoothGiantPrimeRange G,
              smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G p *
                tailGiantEndpointMean A N F (summandTail A (summandTailCutoff Y) hi) p := by
  obtain ⟨N, hN, hfav⟩ := h.favorable_tail_prime_mass ls hsize hA hB CM CH hM hMH Z hD hR P hPNT
  obtain ⟨_a, _, hgiant⟩ := h.eventual_giant_from_favorable_blocks P0 hsize hA hB N hN
    CM ((1 / 1000000 : ℝ) ^ 2) (1 / 20) hM (by norm_num) (by norm_num)
  have ht : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨N, hN, fun k => ?_⟩
  filter_upwards [ht.eventually hfav, ht.eventually hgiant,
    ht.eventually (eventual_favorable_block_endpoint k),
    ht.eventually (eventually_ge_atTop (1000 : ℝ)), eventually_ge_atTop (3 : ℕ)]
    with reference hfav hgiant hgeo hL href
  let L := Real.log (Real.log (reference : ℝ))
  have href3 : (3 : ℝ) ≤ reference := by exact_mod_cast href
  have href0 : (0 : ℝ) < reference := by linarith
  have hlog : 0 < Real.log (reference : ℝ) := Real.log_pos (by linarith)
  have hX : (reference : ℝ) = Real.exp (Real.exp L) := by
    dsimp [L]
    rw [Real.exp_log hlog, Real.exp_log href0]
  dsimp only
  let F0 := favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
    (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2)
  have hF0 : F0 ⊆ logLogPrimeBand L := Finset.filter_subset _ _
  obtain ⟨lo, hlo, hhiLo, hmass⟩ := favorable_logarithmic_block L hL F0 hF0 (hfav reference hX)
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
  obtain ⟨Y, hi, hhi, hYlo, hYhi, hYmin, hYmax, hcut⟩ :=
    hgeo lo (by simpa only [L, show (1 / 20 : ℝ) = 5 / 100 by norm_num] using hlo) hhiLo
  obtain ⟨G, hGlo, hGhi, hmassG, hnormG, hmean⟩ := hgiant Y hYmin hYmax hi hhi
    lo (by simpa only [L, show (1 / 20 : ℝ) = 5 / 100 by norm_num] using hlo) hhiLo hcut F hFb hbal hγ hmass.le
  exact ⟨lo, hlo, hhiLo, F, fun p hp => hFF p hp, Y, hi, hhi, hYlo, hYhi, hYmin, hYmax,
    G, hGlo, hGhi, hmassG, hnormG, hmean⟩

end Ostmann

end OAI
