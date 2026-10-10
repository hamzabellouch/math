import OAI.NumberTheory.Ostmann.Arithmetic.MovingInitialDiagonalUniform
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyRateMonotone
import OAI.NumberTheory.Ostmann.Construction.ScheduledDiagonalLengths
import OAI.NumberTheory.Ostmann.Construction.ScheduledComparisonCounts
import OAI.NumberTheory.Ostmann.Construction.SelectedSchedulePrimeData
import OAI.NumberTheory.Ostmann.Construction.SelectedTierConstruction
import OAI.NumberTheory.Ostmann.Construction.ScheduledGiantSeparation
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularTransformCongruence
import OAI.NumberTheory.Ostmann.Construction.ScheduledCellIteration

namespace OAI

/-! # The published-input diagonal estimate on the actual selected cell schedule -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.selected_scheduled_diagonal
    (P0 : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz B Wwin Dφ : ℝ) (hBs : 1 ≤ Bs) (hBD : 1 ≤ BD) (hBz : 9 ≤ Bz)
    (hWwin : 0 ≤ Wwin) (hDφ : 0 ≤ Dφ)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dφ * |x - y|)
    (hdepth : 120 ≤ (k : ℝ) ^ 3)
    (hgap : (Bs + 1) + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + 1 + Real.log 12 + 1 + 1) + 6 ≤ BD - 1) :
    let Afreq := movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) k
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ p₀ : ℕ, 3 ≤ p₀ ∧
    ∀ᶠ L : ℝ in atTop, ∀ (Aset Bset : Set ℕ), Aset.Infinite → Bset.Infinite →
    ∀ (N : ℕ), (∀ p, p.Prime → Disjoint (tailResidues Aset N p) (negTailResidues Bset N p)) →
    ∀ (b endpoint top : ℕ) (a Y G J cb cd Δ upper X : ℝ) (cs : List ℕ),
      spectatorBulkCount k L = b + b → cs.length = k →
      0 < Y → Y ≤ Real.exp L → 0 ≤ cb →
      1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4 →
      (8 + 4 * cs.length : ℕ) ≤ L →
      16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      48 * (64 * tailDefectBudget a C Y + 2) ≤ J →
      (2 : ℝ) ^ k * (movingCompensationGapRate k BD Bz * L) ≤ J / 4 →
      let Q := initialRegularPrimeRange L
      let D := scheduledPageDeletions P0 L (scheduledComparisonCutoff L)
      let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L)) \ D
      SelectedSmallTailCell Aset Bset N a C L Y endpoint D ((J - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell Aset Bset N a C L Y endpoint D (w / 4) j)
        cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) →
      (∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ)) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ G - 1 →
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ (91 / 100) * L →
      ∀ (q : Fin (b + b) → ℕ) [∀ i, Fact (q i).Prime],
      FrozenInitialSpectatorData Aset N q L ε p₀ D →
      ∀ (sl sr : Fin b → Q) (fallback : Q)
        (Dq : ∀ i, (ZMod (q i))ˣ) (childBound pivotBound V : ℕ → ℕ),
      Monotone V →
      (∀ n ≤ k, (V n : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ))) →
      (∀ n ≤ k, ((transferFrequencyRange (V n)).card : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ))) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * (b + b : ℕ))) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) (b + b : ℕ) →
      Real.exp Δ ≤ upper → upper - Real.exp Δ ≤ Real.exp (Wwin * (b + b : ℕ)) →
      ∀ favorable : ℕ → Bool,
      let F := movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b b (initialSmallCellList top cs).length cb cd sl sr fallback)
        (fun i => normalizedResidueTransform (tailDensityMask Aset N (q i))) Dq Finset.univ
        ψ X (Real.exp Δ) upper
      ∀ n < k,
        scheduledCellDiagonal Subtype.val (List.ofFn q)
          (completedCompensationPrior Aset Bset N Y endpoint D Q top cs)
          childBound pivotBound V F logCellProfile (fun _ => G)
          (smoothGiantPrimeRange G) (Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊)
          (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
          (fun c => primeSubsetPrior Q (selectedTailCellPrimes Aset Bset N Y endpoint D c))
          (primeSubsetPrior Q Qb) top cs n (b + b)
          (normalizedResidueFamily (tailDensityMask Aset N))
          (normalizedResidueFamily (tailDensityMask Aset N)) favorable ≤
        Real.exp (-(2 * B + 3) * (2 ^ n : ℕ) * (b + b : ℕ)) := by
  intro Afreq
  have hk0 : 0 < k := by omega
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  have hAfreq : 0 ≤ Afreq := movingFrequencyRate_nonneg _ _ _ _ (by linarith)
    (by linarith) (by linarith) hz k
  obtain ⟨ε, hε, hε1, p₀, hp₀, he⟩ := P0.moving_selected_initial_diagonal_uniform C hM ψ k
    (fun i => scheduledTailLength k i) hk0 Afreq Wwin 1 Dφ 1 2 1
    (Bs + 1) (BD - 1) Bz B hAfreq hWwin (by norm_num) hDφ (by norm_num)
    (by norm_num) (by norm_num) (by linarith) Dφ hDφ hloglip (by linarith)
    (by linarith) hBz
    (fun i => scheduledTailLength_budget k i i.isLt 2 (by norm_num) (by norm_num at hdepth ⊢; exact hdepth)) hgap
  refine ⟨ε, hε, hε1, p₀, hp₀, ?_⟩
  filter_upwards [he, eventual_scheduled_comparison_cutoffs k k p₀ (fun _ => Afreq),
    eventual_scheduled_comparison_count k, eventual_selected_bulk_mass hM,
    (spectatorBulkCount_tendsto k hk0).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with L he hcut hcount hmass hm hL
  intro Aset Bset hA hB N hN b endpoint top a Y G J cb cd Δ upper X cs hsize hlen hY hYupper hcb
    hcell hcsCount hJ hJerr hJgap Q D Qb htop hcs hlower hG hcg q inst hq sl sr fallback Dq
    childBound pivotBound V hV hVbound hVcard hV0 hΔ hΔbound hupper hwindow favorable F n hn
  have hm' : 1 ≤ b + b := by exact_mod_cast (show (1 : ℝ) ≤ (b + b : ℕ) by simpa only [hsize] using hm)
  have hQprime := initialRegularPrimeRange_prime L
  let : Nonempty Q := ⟨⟨(selected_regular_alphabet_nonempty htop).choose,
    (selected_regular_alphabet_nonempty htop).choose_spec⟩⟩
  obtain ⟨hbulk, hbulklower⟩ := selected_bulk_prime_range L (by linarith) D
  have hDcard : D.card ≤ 2 := scheduledPageDeletions_card P0 L _
  have hmass' := hmass D hDcard
  obtain ⟨hμdata, hμlower, hνdata, hνlower⟩ :=
    selected_schedule_prime_data htop hcs (by linarith) hlower hbulk hbulklower hmass'
  obtain ⟨tier, hμtier, hνtier⟩ := selected_cells_prime_tiers k hk0 (by linarith)
    (by linarith) (by linarith) hcb hJ hJerr hJgap htop hcs
  obtain ⟨tierB, hTierBound, hBtier⟩ := hνtier n (b + b) (n + 1) (by omega)
  have hd := he ⟨n, hn⟩ b hsize
  dsimp only at hd
  rw [← scheduledTailLength_eq cs k n hlen] at hd
  let Qν := scheduledRegularPrimeSets (selectedTailCellPrimes Aset Bset N Y endpoint D)
    Qb top (cs.drop (n + 1)) n (b + b)
  let setsReg := primeMaskExtension Q (tailDensityMask Aset N)
  have hsmallsets : ∀ p, p.Prime → (setsReg p).Nonempty ∧ (setsReg p).card < p :=
    tailPrimeMaskExtension_data hA hB N Q hQprime (fun p hp => hN p (hQprime p hp))
  have hlen' := scheduled_drop_length_balance top cs n (by omega)
  have hlength : 4 + scheduledSmallLength (cs.drop (n + 1)) ≤ 10 + 4 * k := by
    rw [scheduledSmallLength_eq, List.length_drop, hlen]
    omega
  have hcomplex :
      ((D.card + (Fintype.card (MovingRegularSlot n (4 + scheduledSmallLength (cs.drop (n + 1))) (b + b)) +
        4 * n * 2 ^ n)) + (List.ofFn q).length : ℕ) ≤
      scheduledComparisonCount k (spectatorBulkCount k L) := by
    rw [hsize]
    exact scheduled_comparison_count k n _ _ (by omega) hlength D (List.ofFn q) hDcard (by simp)
  have hcuts := hcut.2.2.2.2 n (by omega) (V n) (by simpa only [hsize] using hVbound n (by omega))
  have hprimeBand (i) := hcut.2.2.2.1 (q i) (hq.lower i) (hq.upper i)
  have hfrequency : (V n : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) := by
    have hnat : (V n : ℝ) ≤ scheduledComparisonPrimeLo L := by exact_mod_cast hcuts.2
    exact hnat.trans_lt hcut.2.2.1
  have hbulkD : Disjoint Qb D := Finset.disjoint_left.mpr (fun _ hp hd => (Finset.mem_sdiff.mp hp).2 hd)
  have hpage := selected_schedule_avoids_giant_page P0 Aset Bset N endpoint Y L
    (scheduledComparisonCutoff L) top cs Qb hbulkD
  have hbtop : ∀ p ∈ completedCompensationSets Aset Bset N Y endpoint D top cs n,
      (p : ℝ) ≤ Real.exp (((cs.drop n).headD 0 : ℝ) + 1) :=
    completedCompensationSets_upper_used Aset Bset N endpoint Y D top cs n (by omega)
  have hfreqCard : (((transferFrequencyRange (V n)).erase 0).card : ℝ) ≤
      Real.exp (Afreq * (b + b : ℕ)) := by
    have he : (((transferFrequencyRange (V n)).erase 0).card : ℝ) ≤
        (transferFrequencyRange (V n)).card := by exact_mod_cast Finset.card_erase_le
    exact he.trans (hVcard n (by omega))
  have hcomplexReal :
      ((D.card + (Fintype.card (MovingRegularSlot n (4 + scheduledSmallLength (cs.drop (n + 1))) (b + b)) +
        4 * n * 2 ^ n)) + (List.ofFn q).length : ℕ) ≤ Real.exp ((2 + 1) * L) := by
    have hh : (((D.card + (Fintype.card (MovingRegularSlot n (4 + scheduledSmallLength (cs.drop (n + 1))) (b + b)) +
        4 * n * 2 ^ n)) + (List.ofFn q).length : ℕ) : ℝ) ≤
        scheduledComparisonCount k (spectatorBulkCount k L) := by exact_mod_cast hcomplex
    exact hh.trans (by norm_num; exact hcount)
  have hShell : primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
      (Real.exp ((6 / 1000 : ℝ) * L)) ⊆ Q := by
    simpa only [Finset.sdiff_empty] using initial_broad_cell_subset L (4 / 1000)
      (6 / 1000) (by linarith) (by norm_num) ∅
  have hdiag := hd tierB Q hQprime b (initialSmallCellList top cs).length sl sr fallback
    childBound pivotBound V (List.ofFn q) q Dq (fun i => tailDensityMask Aset N (q i))
    (fun _ => ε / 2) (scheduledComparisonPrimeLo L) (scheduledComparisonCutoff L)
    (fun p => tier p) X Δ upper logCellProfile (fun _ => G) D
    (completedCompensationSets Aset Bset N Y endpoint D top cs) Qν setsReg cb cd
    (((cs.drop n).headD 0 : ℝ) + 1) (scheduledSmallLower top (cs.drop (n + 1)) n)
    (normalizedResidueFamily (tailDensityMask Aset N)) favorable
    hlen' hV
    hfreqCard
    (hVbound n (by omega)) hV0 hΔ hΔbound hupper hwindow
    (by have he := Real.one_le_exp (show 0 ≤ (49 / 1000 : ℝ) * L by positivity); linarith)
    (fun i => (Nat.le_succ n).trans (hTierBound i)) hm' hq.ge_cutoff hq.nonempty hq.proper
    (hq.comparison_upper (by linarith)) hq.balanced_lower hq.balanced_upper (fun _ => by linarith)
    hq.character_bound logCellProfile_nonneg
    (fun x => (abs_of_nonneg (logCellProfile_nonneg x)).trans_le (logCellProfile_le_one x))
    hloglip logCellProfile_zero_outside hShell
    hcomplexReal
    (by intro p hp; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp; exact (inferInstance : Fact (q i).Prime).out)
    (fun _ => rfl) (fun j => (hμdata j).1) (fun i => (hνdata n (b + b) (n + 1) i).1)
    (fun j => (hμdata j).2) (fun i => (hνdata n (b + b) (n + 1) i).2)
    hμlower (hνlower n (b + b) (n + 1))
    (by intro p hp; exact List.mem_ofFn.mp hp) hq.injective hG
    (by intro j hj p hp; exact hμtier j (by omega) p hp) (fun i p hp => hBtier i p hp)
    hcuts.2 hcuts.1 hcut.2.1 hcut.2.2.1 (fun p => initialRegularPrimeRange_upper L p p.property)
    hprimeBand (fun z hz p hp j => (hpage z hz p hp).1 j) (hq.avoids_giant_page)
    (fun z hz p hp i => (hpage z hz p hp).2 n (b + b) (n + 1) i) (hq.avoids_bulk_page)
    hsmallsets hbtop logCellProfile_le_one
    (fun i p hp => scheduledSmallLower_prime_bound Aset Bset N endpoint top Y D Qb
      (cs.drop (n + 1)) n (b + b) i p hp)
    (by intro i p hp; exact_mod_cast hfrequency.trans_le (hνlower n (b + b) (n + 1) i p hp))
    (by intro p hp i z hz; exact scheduled_giant_regular_separation L G (by linarith) hG p hp z
          ((hνdata n (b + b) (n + 1) i).1 hz))
    (by simpa only [hsize, Nat.cast_mul, Nat.cast_ofNat] using
      selected_scheduled_drop_diagonal_gap k n hn (by linarith) hY hYupper hcell hcsCount hcg htop hcs)
  unfold scheduledCellDiagonal
  rw [scheduledRegularPrior_prime]
  rw [movingAmplitudeDiagonal_regular_congr Subtype.val (List.ofFn q)
    (completedCompensationPrior Aset Bset N Y endpoint D Q top cs) childBound pivotBound V
    F logCellProfile (fun _ => G) n _ (b + b) _ _ _ _
    (normalizedResidueFamily (tailDensityMask Aset N)) (normalizedResidueFamily setsReg)
    (normalizedResidueFamily (tailDensityMask Aset N)) favorable
    (fun p => (normalizedResidueFamily_primeMaskExtension Q (tailDensityMask Aset N) p p.property).symm)]
  exact hdiag

end Ostmann

end OAI
