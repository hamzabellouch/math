import OAI.NumberTheory.Ostmann.Construction.SelectedInitialAmplitude
import OAI.NumberTheory.Ostmann.Construction.SelectedInitialPrimeLower
import OAI.NumberTheory.Ostmann.Construction.SelectedEndpointGiant
import OAI.NumberTheory.Ostmann.Construction.ConstructedInitialNongiantPriors
import OAI.NumberTheory.Ostmann.Construction.InitialAmbientPrimeRange
import OAI.NumberTheory.Ostmann.Construction.InitialTailEndpoint
import OAI.NumberTheory.Ostmann.Construction.TailCutoffHarmonicMass
import OAI.NumberTheory.Ostmann.Construction.InitialFrozenAmplitude

namespace OAI

/-! # Constructing the original positive initial amplitude from published inputs -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem EventuallyPrimeSumset.constructed_initial_amplitude
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hBonami : PublishedBonamiBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT)
    (ψ : 𝓢(ℝ, ℂ)) (H c : ℝ) (hH : 0 ≤ H) (hc : 0 < c)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0)
    (hψlower : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ (ψ t).re) :
    ∃ N : ℕ, ∃ a : ℝ, 0 < a ∧
      (∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) ∧
      ∀ k : ℕ, 2 ≤ k → ∀ Bs BD Bz : ℝ, 0 ≤ Bs → 0 ≤ BD → 0 ≤ Bz →
      2 * ((4 - 2 * Real.log (1 / 320000)) + 2 + 2 * Real.log 4 +
        (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs - 1 →
      14 * (64 * tailCellLinearRate a CM + 3) ≤ (k : ℝ) ^ 3 →
      ∀ cutoff : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ reference : ℕ in atTop,
      let L := Real.log (Real.log (reference : ℝ))
      ∃ lo : ℝ, Real.exp ((1 / 20 : ℝ) * L) ≤ lo ∧ lo ≤ Real.exp ((9 / 10 : ℝ) * L) ∧
      ∃ F : Finset ℕ, F ⊆ favorableTransformPrimes (logLogPrimeBand L) (tailSupport A N)
        (tailFourierMass A N) ((1 / 1000000 : ℝ) ^ 2) ∧
      ∃ Y : ℝ, ∃ hi : ℕ, (hi : ℝ) = Real.exp Y ∧
        2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) ≤ Y ∧
        Y ≤ 2 * lo + 2 ^ (k + 1) * (12 * Real.exp ((1 / 100 : ℝ) * L)) + 1 ∧
        Real.exp ((4 / 100 : ℝ) * L) ≤ Y ∧ Y ≤ Real.exp L ∧
      ∃ G : ℤ, lo - 2 ≤ G ∧ (G : ℝ) ≤ lo - 2 + 12 * Real.exp ((1 / 100 : ℝ) * L) ∧
        Real.exp (-(91 / 100 : ℝ) * L) ≤
          smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G ∧
        smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100) * L ∧
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ Qd : Finset ℕ, ∃ cb cd : ℤ, ∃ top : ℕ, ∃ centers : List ℕ,
        Qd ⊆ primeLogCellSet 1 0 (Real.exp ((4 / 10000 : ℝ) * L))
          (Real.exp ((6 / 10000 : ℝ) * L)) \ D ∧
        L / 320000 ≤ ∑ p ∈ Qd, (p : ℝ)⁻¹ ∧
        (∀ p ∈ Qd, cutoff ≤ p ∧
          ((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
            residueDensity (tailDensityMask A N p) ≤ 2 / 3) ∧ tailCharacterBias A N p ≤ ε / 2) ∧
        cb ∈ Finset.Icc (0 : ℤ)
          ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 1000 : ℝ) * L)⌉₊ ∧
        cd ∈ Finset.Icc (0 : ℤ)
          ⌈(spectatorBulkCount k L / 2 : ℕ) * Real.exp ((6 / 10000 : ℝ) * L)⌉₊ ∧
        SelectedSmallTailCell A B N a CM L Y hi D
          ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top ∧
        List.Forall₂ (fun j w => SelectedSmallTailCell A B N a CM L Y hi D (w / 4) j)
          centers (movingCompensationTargets
            (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
            (movingCompensationGaps k BD Bz L)) ∧ centers.length = k ∧
        let P := Nat.primesLE (tailCollisionCutoff Y)
        let _ : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(Nat.prime_of_mem_primesLE p.property).ne_zero⟩
        let m := spectatorBulkCount k L
        let cells := initialSmallCellList top centers
        let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
          (Real.exp ((6 / 1000 : ℝ) * L)) \ D
        let ν := selectedInitialHalfPrior P A B N hi Y G D Qb Qd (m / 2) (m / 2) top centers
        let w := initialHalfCutoffWeight (fun p : P => (p : ℕ)) (m / 2) (m / 2) cells.length cb cd
        let Δ := selectedInitialLogCenter G Y cb cd top centers
        let width : ℝ := 2 * (cells.length + 3)
        ∀ T : ℕ → ℝ,
        let V := movingProductNaturalCutoff T (Y + Δ + width) Y ((m : ℝ) / 4) 0
        let Ftest : Fin ((m / 2 + (m / 2 + cells.length)) + 1) →
          (p : P) → ZMod (p : ℕ) → ℂ :=
            primeHalfTests P (fun p => tailDensityMask A N p) (fun p => decide ((p : ℕ) ∈ F))
        Real.exp (-(6 * Real.log 2 + 13) * m) ≤
          ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append Ftest Ftest) ψ (Real.exp Y) V
            (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ)))‖ ∧
        ∃ sl sr : Fin (m / 2) → P, Function.Injective (Fin.append sl sr) ∧
          (∀ i, (sl i : ℕ) ∈ Qd) ∧ (∀ i, (sr i : ℕ) ∈ Qd) ∧
          Real.exp (-(6 * Real.log 2 + 13) * m) ≤
            ‖initialFrozenAmplitude P (m / 2) (m / 2) cells.length
              (smoothGiantPrior P logCellProfile G) (fun _ => primeSubsetPrior P Qb)
              (fun i => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D (cells.get i)))
              (Fin.append Ftest Ftest) ψ (Real.exp Y) V
              (doubledHalfWeight (fun y => (w (Fin.tail y) : ℂ))) sl sr‖ := by
  classical
  obtain ⟨N, hN, hgiant⟩ := h.selected_endpoint_giant P0 ls hsize hA hB CM CH hM hMH
    Z hD hR Pexplicit hPNT
  obtain ⟨a, ha, hnongiant⟩ := h.constructed_initial_nongiant_priors hBonami P0 Hreal
    hSiegel sieve hsize hM hA hB N hN
  obtain ⟨atail, hatail, htail⟩ := h.initial_tail_endpoint hsize hA hB N
  have ht : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have hYlarge : ∀ᶠ L : ℝ in atTop, Y₀ ≤ Real.exp ((4 / 100 : ℝ) * L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))).eventually
      (eventually_ge_atTop Y₀)
  refine ⟨N, a, ha, hN, ?_⟩
  intro k hk Bs BD Bz hBs hBD hBz hgap hklarge cutoff ε hε
  have hamp := eventual_selected_initial_amplitude k hk Bs BD Bz a CM atail c
    ((1 / 1000000 : ℝ) ^ 2 * (1 / 20) / 32) H hBs hH hatail hc (by norm_num)
    hgap hklarge ψ hψ hsupp
  filter_upwards [hgiant k, ht.eventually (hnongiant k hk Bs BD Bz hBs hBD hBz cutoff ε hε),
    ht.eventually hamp, ht.eventually eventual_initial_regular_prime_range,
    ht.eventually (eventual_initial_giant_prime_range k hk),
    ht.eventually (eventual_selected_initial_prime_lower k hk Bs BD Bz hBs hBD hBz),
    ht.eventually htail, ht.eventually hYlarge,
    ht.eventually (eventually_ge_atTop (max 1 CH))]
    with reference hgiant hnongiant hamp hsmall hbig hprimelow htail hYlarge hL
  dsimp only at hgiant ⊢
  let L := Real.log (Real.log (reference : ℝ))
  obtain ⟨lo, hlo, hlohi, F, hF, Y, hi, hhi, hYlo', hYhi', hYlo, hYhi,
    G, hGlo, hGhi, hmass, hnorm, hmean⟩ := hgiant
  refine ⟨lo, hlo, hlohi, F, hF, Y, hi, hhi, hYlo', hYhi', hYlo, hYhi,
    G, hGlo, hGhi, hmass, hnorm, ?_⟩
  intro D hDcard
  let P := Nat.primesLE (tailCollisionCutoff Y)
  have hP : ∀ p ∈ P, p.Prime := fun _ hp => Nat.prime_of_mem_primesLE hp
  have hsmallP : initialRegularPrimeRange L ⊆ P := hsmall Y hYlo hYhi
  have hgiantP : smoothGiantPrimeRange G ⊆ P := hbig lo Y G hYlo hYhi hYlo' hGhi
  obtain ⟨Qd, cb, cd, top, centers, hQd, hQmass, hgood, hcb, hcd, htop, hcenters,
    hlen, _htotal, hb, hd, hpoint, hbalanced⟩ :=
    hnongiant Y hYlo hYhi hi hhi lo G hYlo' hYhi' hGlo hGhi D hDcard P hP hsmallP
  refine ⟨Qd, cb, cd, top, centers, hQd, hQmass, hgood, hcb, hcd, htop, hcenters, hlen, ?_⟩
  let : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(hP p p.property).ne_zero⟩
  let m := spectatorBulkCount k L
  intro T
  have hend := htail Y hYlo hYhi hi hhi
  have hcut := hY₀ Y (hYlarge.trans hYlo)
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hCH : CH ≤ L := (le_max_right _ _).trans hL
  have hYpos : 0 < Y := (Real.exp_pos _).trans_le hYlo
  have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (show (2 : ℝ) ≤ k by exact_mod_cast hk) 4
    norm_num at hh
    nlinarith
  have hmlo : L ≤ (m : ℝ) := by
    have hh := spectatorBulkCount_half k L hscale
    have hp : (2 : ℝ) ≤ (k : ℝ) ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ k by exact_mod_cast hk) 4
      norm_num at hh
      linarith
    nlinarith only [hh, mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ L)]
  have htotal := hMH.tail_cutoff_mass_linear Y L m hcut.1 hcut.2.1 hYhi hCH hmlo
  have hmean' := ambient_tail_giant_endpoint_lower A N F
    (summandTail A (summandTailCutoff Y) hi) P hP G
    ((1 / 1000000 : ℝ) ^ 2 * (1 / 20) / 32) hgiantP
    (by simpa only [positiveSummandTail, Finset.image_nonempty] using hend.2.1) hmean.le
  have hlower := hamp hYpos hYhi htop hcenters hlen P hP hsmallP hgiantP
    ((Real.exp_pos _).trans_le hmass) hnorm hb hd hpoint
    (by simpa only [selectedInitialHalfPrior, Fin.tail_cons, initialHalfCutoffWeight,
      mul_assoc] using hbalanced)
    (hprimelow cb cd hcb hcd hYlo' hYhi' hlo hGlo hGhi hQd htop hcenters P hP (m / 2) (m / 2))
    htotal (positiveSummandTail A (summandTailCutoff Y) hi)
    (fun p => decide ((p : ℕ) ∈ F)) hend.1 (fun e he => hψlower _ (hend.2.2.1 e he))
    hend.2.2.2 hmean' T
  refine ⟨hlower, ?_⟩
  obtain ⟨sl, sr, hinj, hsl, hsr, hfrozen⟩ := exists_distinct_initial_spectators P
    (m / 2) (m / 2) (initialSmallCellList top centers).length
    (smoothGiantPrior P logCellProfile G)
    (fun _ => primeSubsetPrior P
      (primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D))
    (fun _ => primeSubsetPrior P Qd)
    (fun i => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y hi D ((initialSmallCellList top centers).get i)))
    (fun _ => primeSubsetPrior_nonneg P Qd) (fun _ => hd) _ ψ (Real.exp Y) _ _
    (Real.exp (-(6 * Real.log 2 + 13) * m)) (Real.exp_pos _) hlower
  exact ⟨sl, sr, hinj, fun i => primeSubsetPrior_support P Qd (sl i) (hsl i),
    fun i => primeSubsetPrior_support P Qd (sr i) (hsr i), hfrozen⟩

end Ostmann

end OAI
