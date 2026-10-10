import OAI.NumberTheory.Ostmann.Construction.ConstructedInitialAmplitude
import OAI.NumberTheory.Ostmann.Construction.FrozenInitialSmallAmplitude
import OAI.NumberTheory.Ostmann.Construction.SelectedScheduledFinalContradiction
import OAI.NumberTheory.Ostmann.Construction.SelectedInitialUnshiftedCutoff
import OAI.NumberTheory.Ostmann.Construction.ScheduledAnalyticParameters
import OAI.NumberTheory.Ostmann.Construction.ScheduledInitialWindow
import OAI.NumberTheory.Ostmann.Construction.SelectedFrequencySeparation
import OAI.NumberTheory.Ostmann.Construction.PositiveFourierCutoff
import OAI.NumberTheory.Ostmann.Construction.InitialSpectatorProduct
import OAI.NumberTheory.Ostmann.Construction.SelectedProductBudget
import OAI.NumberTheory.Ostmann.Construction.SelectedScheduledIteration

namespace OAI

/-! # The two-infinite-summand theorem from the precise published inputs -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem twoInfiniteSummandsImpossible_of_published
    (P0 : PublishedProgressionInput) (ls : PublishedAdditiveLargeSieve)
    (hsize : PublishedSummandSizeBound) (hBonami : PublishedBonamiBound)
    (Hreal : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve)
    (CM CH : ℝ) (hM : MertensEstimate CM) (hMH : MertensHarmonicEstimate CH)
    (Z : ∀ χ, ComplexZeroEnumeration χ) (hD : PublishedComplexZeroDensity Z)
    (hR : PublishedComplexZeroRegion Z) (Pexplicit : PublishedSmoothExplicitFormula Z)
    (hPNT : PublishedSmoothPrincipalPNT) : TwoInfiniteSummandsImpossible := by
  intro A B hA hB h
  obtain ⟨c, ψ, hc, _hreal, hψ, hψlower, hsupp⟩ := exists_positive_fourier_cutoff
  obtain ⟨N, a, ha, hN, hconstruct⟩ := h.constructed_initial_amplitude P0 ls hsize hBonami
    Hreal hSiegel sieve hA hB CM CH hM hMH Z hD hR Pexplicit hPNT ψ ((3 : ℝ) ^ 2) c
    (by positivity) hc hψ hsupp hψlower
  obtain ⟨Bs, BD, hBs, hBD, hgapInitial, hgapDiagonal⟩ := scheduled_gap_parameters
  obtain ⟨Dφ, hDφ, hloglip⟩ := logCellProfile_lipschitz
  have hfinal := P0.selected_scheduled_final_contradiction CM hM (𝓕 ψ)
    Bs BD 9 scheduledIterationRate Dφ (by linarith) (by linarith) (by norm_num) hDφ hloglip
  obtain ⟨k, hkFinal, hk, hdepth, hlarge, hkReserve, hkCell⟩ :=
    (hfinal.and (eventual_scheduled_depth_reserves (tailCellLinearRate a CM))).exists
  let Wwin := Bs + 1 + 8 * Real.log ((k : ℝ) ^ 4)
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  have hWwin : 0 ≤ Wwin := by
    have hh := Real.log_nonneg hz
    dsimp only [Wwin]
    linarith
  obtain ⟨εF, hεF, _hεF1, pF, hpF, hFL⟩ := hkFinal Wwin hWwin hdepth
  obtain ⟨εD, hεD, _hεD1, pD, hpD, hDL⟩ := P0.selected_scheduled_diagonal CM hM (𝓕 ψ)
    k hk Bs BD 9 scheduledIterationRate Wwin Dφ hBs (by linarith) (by norm_num)
    hWwin hDφ hloglip hdepth hgapDiagonal
  let ε := min εD εF
  let p₀ := max pD pF
  have hε : 0 < ε := lt_min hεD hεF
  have hp₀ : 3 ≤ p₀ := hpD.trans (le_max_left _ _)
  have hconstruct := hconstruct k hk Bs BD 9 (by linarith) (by linarith) (by norm_num)
    hgapInitial hlarge p₀ ε hε
  have ht : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hfalse : ∀ᶠ reference : ℕ in atTop, False := by
    filter_upwards [hconstruct, ht.eventually hDL, ht.eventually hFL,
      ht.eventually eventual_initial_regular_prime_range,
      ht.eventually (eventual_initial_giant_prime_range k hk),
      ht.eventually (eventual_scheduled_iteration_thresholds k hk a CM hkReserve),
      ht.eventually (eventual_initial_protected_target k hk Bs BD 9
        (by linarith) (by linarith) (by norm_num)),
      ht.eventually (eventual_initial_selected_centers_lower k hk Bs BD 9
        (by linarith) (by linarith) (by norm_num)),
      ht.eventually (eventual_selected_tier_budgets k (by omega) a CM BD 9
        (by linarith) (by norm_num)),
      ht.eventually (eventual_selected_initial_energy_window k hk Bs BD 9
        (tailCellLinearRate a CM) hBs (tailCellLinearRate_nonneg a CM) hlarge),
      ht.eventually eventual_scheduled_giant_lower,
      ht.eventually (eventual_tailDefectBudget_nonneg a CM),
      ht.eventually (eventual_selected_frequency_band k Bs BD 9 (39 / 10000) (by norm_num)),
      ht.eventually (eventual_selected_frequency_separation k Bs BD 9),
      ht.eventually (eventually_gt_atTop (2 : ℝ))]
      with reference hconstruct hDL hFL hregular hgiant hiteration hprotected hcenters
        htiers henergy hGlarge hdefNonneg hsmallFreq hfrequencies hL
    let L := Real.log (Real.log (reference : ℝ))
    obtain ⟨lo, hlo, _hloUpper, favorablePrimes, _hfavorable, Y, endpoint, hendpoint,
      hYlo, hYhi, hYlower, hYupper, G, hGlo, hGhi, hGmass, hGnorm, hselected⟩ := hconstruct
    let D := scheduledPageDeletions P0 L (scheduledComparisonCutoff L)
    have hDcard : (D.card : ℝ) ≤ Real.exp L := by
      have hh : (D.card : ℝ) ≤ 2 := by exact_mod_cast scheduledPageDeletions_card P0 L (scheduledComparisonCutoff L)
      have he := Real.add_one_le_exp L
      linarith
    obtain ⟨Qd, cb, cd, top, cs, hQd, _hQdmass, hgood, hcb, hcd, htop, hcs, hlen, hstart⟩ :=
      hselected D hDcard
    let m := spectatorBulkCount k L
    let b := m / 2
    have hsize : spectatorBulkCount k L = b + b := by
      obtain ⟨d, hd⟩ := spectatorBulkCount_even k L
      dsimp only [b, m]
      omega
    have hsize' : spectatorBulkCount k (Real.log (Real.log (reference : ℝ))) = b + b := hsize
    have hY : 0 < Y := (Real.exp_pos _).trans_le hYlower
    have hL1 : 1 ≤ L := by linarith
    have hcb0 : 0 ≤ (cb : ℝ) := (initial_log_center_bounds m _ cb hcb).1
    have hdef := tailDefectBudget_linear a CM L Y hL1 hY hYupper
    have hdef0 : 0 ≤ tailDefectBudget a CM Y := hdefNonneg Y hYlower
    have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ k by exact_mod_cast hk) 4
      norm_num at hh
      nlinarith
    obtain ⟨hm, hcount, herror, hbudget⟩ := hiteration Y hY hYupper top cs hlen
    have hGdata := hGlarge lo G hlo hGlo
    have hlower := hcenters cb cd hcb hcd hYlo hYhi hGlo hGhi htop hcs
    let T := movingCellPivotExponent (fun _ => (G : ℝ)) (selectedCompensationCenter cs)
    let center := selectedInitialLogCenter G Y cb cd top cs
    let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
    have hzero := selected_initial_unshifted_cutoff k hk hL1 hY hYupper
      (tailCellLinearRate_nonneg a CM) hdef0 hdef hlarge hscale hkCell hcount hm
      (by linarith only [hGdata.1]) hcb0 (by linarith) (by linarith) (by norm_num) htop hcs
    dsimp only at hzero
    let P := Nat.primesLE (tailCollisionCutoff Y)
    let Q := initialRegularPrimeRange L
    let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
      (Real.exp ((6 / 1000 : ℝ) * L)) \ D
    let cells := initialSmallCellList top cs
    have hP : ∀ p ∈ P, p.Prime := fun _ hp => Nat.prime_of_mem_primesLE hp
    have hQprime := initialRegularPrimeRange_prime L
    let : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(hP p p.property).ne_zero⟩
    have hQP : Q ⊆ P := hregular Y hYlower hYupper
    have hgiantP : smoothGiantPrimeRange G ⊆ P := hgiant lo Y G hYlower hYupper hYlo hGhi
    obtain ⟨hbulk, hbulkLower⟩ := selected_bulk_prime_range L (by linarith) D
    have hQdSmall : Qd ⊆ Q := hQd.trans
      (initial_broad_cell_subset L (4 / 10000) (6 / 10000) (by linarith) (by norm_num) D)
    obtain ⟨_hweighted, sl₀, sr₀, hinj₀, hsl₀, hsr₀, hfrozen⟩ := hstart T
    let sl := restrictPrimeSamples sl₀ (fun i => hQdSmall (hsl₀ i))
    let sr := restrictPrimeSamples sr₀ (fun i => hQdSmall (hsr₀ i))
    let e := primeAlphabetEmbedding hQP
    have hslEq : e ∘ sl = sl₀ := restrictPrimeSamples_embedding hQP sl₀ _
    have hsrEq : e ∘ sr = sr₀ := restrictPrimeSamples_embedding hQP sr₀ _
    have hinj : Function.Injective (Fin.append (e ∘ sl) (e ∘ sr)) := by
      rw [hslEq, hsrEq]
      exact hinj₀
    have hsl : ∀ i, ((e ∘ sl) i : ℕ) ∈ Qd := by rw [hslEq]; exact hsl₀
    have hsr : ∀ i, ((e ∘ sr) i : ℕ) ∈ Qd := by rw [hsrEq]; exact hsr₀
    let q : Fin (b + b) → ℕ := fun i => ((Fin.append (e ∘ sl) (e ∘ sr) i : P) : ℕ)
    let : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append (e ∘ sl) (e ∘ sr) i).property⟩
    have hqData : FrozenInitialSpectatorData A N q L ε p₀ D :=
      frozen_initial_spectator_data hA hB N hN hp₀ hQd hgood
        (e ∘ sl) (e ∘ sr) hinj hsl hsr
    let hcq : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hqData.prime i) (hqData.prime j)).mpr
        (fun heq => hij (hqData.injective heq))
    let Dq := initialSpectatorCofactor q hcq
    let fallback : Q := ⟨(selected_regular_alphabet_nonempty htop).choose,
      (selected_regular_alphabet_nonempty htop).choose_spec⟩
    let Dlog := Real.log ((∏ i, q i : ℕ) : ℝ)
    let X := Real.exp Y / (∏ i, q i : ℕ)
    let lower := Real.exp (center - width)
    let upper := Real.exp (center + width)
    let μ := completedCompensationPrior A B N Y endpoint D Q top cs
    let V := movingProductNaturalCutoff T (Y + center + width - Dlog) (Y - Dlog) ((m : ℝ) / 4)
    let g : ∀ i, ZMod (q i) → ℂ := fun i => normalizedResidueFamily (tailDensityMask A N) (q i)
    let leaf := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b b cells.length cb cd sl sr fallback)
      g Dq Finset.univ (𝓕 ψ) X lower upper
    let favorable := fun p => decide (p ∈ favorablePrimes)
    let η := fun n => scheduledCellAmplitude Subtype.val (List.ofFn q) μ (scheduledChildBound V)
      (scheduledPivotCaps G cs) V leaf logCellProfile (fun _ => (G : ℝ))
      (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
      (fun c => primeSubsetPrior Q (selectedTailCellPrimes A B N Y endpoint D c))
      (primeSubsetPrior Q Qb) top cs n (b + b)
      (normalizedResidueFamily (tailDensityMask A N)) (normalizedResidueFamily (tailDensityMask A N)) favorable
    have hVzero : V 0 = movingProductNaturalCutoff T (Y + center + width) Y ((m : ℝ) / 4) 0 :=
      movingProductNaturalCutoff_zero_translate T (Y + center + width) Y ((m : ℝ) / 4) Dlog
    have hVzeroGiant : (V 0 : ℝ) < Real.exp ((G : ℝ) - 1) := by
      rw [hVzero]
      have hv := hsmallFreq 0 (Nat.zero_le _) (fun _ => movingProductNaturalCutoff T
        (Y + center + width) Y ((m : ℝ) / 4) 0) hzero.1
      apply hv.trans_le
      apply Real.exp_le_exp.mpr
      exact (Real.exp_le_exp.mpr (by linarith : (39 / 10000 : ℝ) * L ≤ (49 / 1000 : ℝ) * L)).trans hGdata.2
    have hid := frozen_initial_small_amplitude (cb := (cb : ℝ)) (cd := (cd : ℝ)) htop hcs
      P hP hQP hgiantP Qb hbulk b b sl sr hinj
      (fun i => hsl₀ i) (fun i => hsr₀ i)
      fallback (tailDensityMask A N) favorable ψ
      (completedCompensationSets A B N Y endpoint D top cs) (scheduledChildBound V)
      (scheduledPivotCaps G cs) V hVzeroGiant
    dsimp only at hid
    change _ = η 0 at hid
    have hinit : Real.exp (-scheduledInitialRate * (m : ℝ)) ≤ ‖η 0‖ := by
      rw [← hid]
      have hp := hfrozen
      rw [← hslEq, ← hsrEq] at hp
      simpa only [scheduledInitialRate, hVzero] using hp
    have hηnonzero : η 0 ≠ 0 := by
      intro hh
      have hn := hinit
      rw [hh, norm_zero] at hn
      exact (not_le_of_gt (Real.exp_pos _)) hn
    have hηsource := hηnonzero
    unfold η scheduledCellAmplitude at hηsource
    rw [List.drop_zero] at hηsource
    have hcertificate := initialTemplateAmplitude_spectator_product Subtype.val
      (fun p : Q => (hQprime p p.property).pos) b b cells.length (scheduledSmallLength cs)
      cb cd sl sr fallback q g Dq Finset.univ (𝓕 ψ) X lower upper (List.ofFn q) μ
      (scheduledChildBound V) (scheduledPivotCaps G cs) V logCellProfile (fun _ => (G : ℝ))
      (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
      (scheduledRegularPrior (fun c => primeSubsetPrior Q
        (selectedTailCellPrimes A B N Y endpoint D c)) (primeSubsetPrior Q Qb) top cs 0 (b + b))
      (normalizedResidueFamily (tailDensityMask A N))
      (normalizedResidueFamily (tailDensityMask A N)) favorable
      hηsource
    have hqProduct : (∏ i, q i : ℕ) = ∏ i, ((Fin.append sl sr i : Q) : ℕ) := by
      apply Finset.prod_congr rfl
      intro i _
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · dsimp only [q]
        rw [Fin.append_left, Fin.append_left]
        rfl
      · dsimp only [q]
        rw [Fin.append_right, Fin.append_right]
        rfl
    have hDlog : |Dlog - 2 * (cd : ℝ)| ≤ 2 := by
      dsimp only [Dlog]
      rw [hqProduct]
      exact hcertificate.le
    have hcut := selected_scheduled_cutoff_data k hk hL1 hY hYupper
      (tailCellLinearRate_nonneg a CM) hdef0 hdef hlarge hscale hkCell hcount hm
      (by linarith only [hGdata.1]) hcb0 hDlog rfl (by linarith) (by linarith) (by norm_num) htop hcs
    dsimp only at hcut
    have hVmono : Monotone V := hcut.1
    have hVbound := hcut.2.2.2
    have hVuniform := movingFrequencyRate_uniform_bounds (Bs + 1) (BD + 2) 9 ((k : ℝ) ^ 4)
      (m : ℝ) k V (by linarith) (by linarith) (by norm_num) hz (Nat.cast_nonneg _) hVbound
    have hVseparated := hfrequencies V G (fun n hn => (hVbound n hn).1) hGdata.2
    have hproduct : 0 < ((∏ i, q i : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos (fun i _ => (hqData.prime i).pos)
    have hXwindow := frozen_spectator_window ((∏ i, q i : ℕ) : ℝ) hproduct Y center width
    obtain ⟨_, hΔ, hΔbound, hlu, hWin, _, hV0bound⟩ := henergy hdef htop hcs hlen
    let J := movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD 9 L)
    have hJ := hprotected cb cd hcb hcd lo G Y hYlo hYhi hGlo hGhi
    have hTier := htiers Y J hY hYupper hJ.1
    have hg : g = (fun i => normalizedResidueTransform (tailDensityMask A N (q i))) := by
      funext i
      exact normalizedResidueFamily_eq (tailDensityMask A N) (q i)
    have hDdata := hqData.mono (min_le_left _ _) (le_max_left _ _)
    have hFdata := hqData.mono (min_le_right _ _) (le_max_right _ _)
    have hU (n : ℕ) (hn : n ≤ k) :
        (V n : ℝ) ≤ Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) 9 ((k : ℝ) ^ 4) k * (b + b : ℕ)) ∧
        ((transferFrequencyRange (V n)).card : ℝ) ≤
          Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) 9 ((k : ℝ) ^ 4) k * (b + b : ℕ)) := by
      simpa only [m, hsize] using hVuniform n hn
    have hV0Window : (V 0 : ℝ) ≤ Real.exp (center - width + Real.sqrt (4 * (b + b : ℕ))) := by
      rw [hVzero]
      simpa only [center, width, m, L, hsize'] using hV0bound T
    have hΔbound' : center - width ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) (b + b : ℕ) := by
      simpa only [center, width, hsize'] using hΔbound
    have hWin' : upper - lower ≤ Real.exp (Wwin * (b + b : ℕ)) := by
      simpa only [upper, lower, center, width, Wwin, hsize'] using hWin
    have hdiagonal := hDL A B hA hB N hN b endpoint top a Y G J cb cd (center - width)
      upper X cs hsize hlen hY hYupper hcb0 hkCell hcount hJ.1 hTier.1 hTier.2
      htop hcs hlower hGdata.2 hGnorm q hDdata sl sr fallback Dq
      (scheduledChildBound V) (scheduledPivotCaps G cs) V hVmono
      (fun n hn => (hU n hn).1) (fun n hn => (hU n hn).2) hV0Window hΔ hΔbound' hlu hWin' favorable
    dsimp only at hdiagonal
    have hdiagTransfer : ∀ n < k,
        scheduledCellDiagonal Subtype.val (List.ofFn q) μ (scheduledChildBound V)
          (scheduledPivotCaps G cs) V leaf logCellProfile (fun _ => (G : ℝ))
          (smoothGiantPrimeRange G) (Finset.Ioc ⌊Real.exp ((G : ℝ) - 1)⌋₊ ⌊Real.exp ((G : ℝ) + 1)⌋₊)
          (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
          (fun c => primeSubsetPrior Q (selectedTailCellPrimes A B N Y endpoint D c))
          (primeSubsetPrior Q Qb) top cs n (b + b)
          (normalizedResidueFamily (tailDensityMask A N))
          (normalizedResidueFamily (tailDensityMask A N)) favorable ≤
          Real.exp (-(2 * (scheduledInitialRate + 1) + 3) * (2 : ℝ) ^ n * m) := by
      intro n hn
      simpa only [leaf, hg, μ, cells, lower, upper, m, hsize, scheduledIterationRate,
        Nat.cast_pow, Nat.cast_ofNat] using hdiagonal n hn
    have hmassG : 0 < smoothGiantMass (smoothGiantPrimeRange G) logCellProfile G :=
      (Real.exp_pos _).trans_le hGmass
    have hIter := selected_scheduled_iteration hA hB k hk hQprime (fun _ hp => hp)
      hL1 hY hYupper hkCell hcount hm (by linarith only [hGdata.1]) hcb0 hDlog
      (by linarith) hBD (by norm_num) herror hbudget htop hcs hlower hbulk hbulkLower
      (fun p hp => hN p (hQprime p hp)) b b sl sr fallback q g Dq Finset.univ (𝓕 ψ)
      X lower upper hXwindow.1 logCellProfile logCellProfile_nonneg logCellProfile_zero_outside hmassG
      (List.ofFn q) favorable scheduledInitialRate
      hXwindow.2.le (fun n hn => (hVseparated n hn).1) (fun n hn => (hVseparated n hn).2)
      (by nlinarith only [hGnorm, hL]) hinit hdiagTransfer
    have hFinalAmplitude := hIter k le_rfl
    conv at hFinalAmplitude =>
      lhs
      rw [hsize]
    apply hFL A B hA hB N hN b endpoint top a Y G J cb cd (center - width) upper X cs
      hsize hlen hcb0 hJ.1 hTier.1 hTier.2 htop hcs hlower hGdata.2
      (by nlinarith only [hGnorm, hL]) q hFdata sl sr fallback Dq
      (scheduledChildBound V) (scheduledPivotCaps G cs) V hVmono (hU k le_rfl).1
      (hU k le_rfl).2 hV0Window hΔ hΔbound' hlu hWin' favorable
    simpa only [η, μ, leaf, hg, cells, lower, upper, scheduledIterationRate] using hFinalAmplitude
  obtain ⟨_, hf⟩ := hfalse.exists
  exact hf

end Ostmann

end OAI
