import OAI.NumberTheory.Ostmann.Construction.SelectedScheduledDiagonal
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedInitialContradiction
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalTemplate

namespace OAI

/-! # The last-depth contradiction for the actual selected finite schedule -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.selected_scheduled_final_contradiction
    (P0 : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (Bs BD Bz B Dφ : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hDφ : 0 ≤ Dφ)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dφ * |x - y|) :
    ∀ᶠ k : ℕ in atTop, ∀ Wwin : ℝ, 0 ≤ Wwin → 120 ≤ (k : ℝ) ^ 3 →
    let Afreq := movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) k
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ p₀ : ℕ, 3 ≤ p₀ ∧
    ∀ᶠ L : ℝ in atTop, ∀ (Aset Bset : Set ℕ), Aset.Infinite → Bset.Infinite →
    ∀ N : ℕ, (∀ p, p.Prime → Disjoint (tailResidues Aset N p) (negTailResidues Bset N p)) →
    ∀ (b endpoint top : ℕ) (a Y G J cb cd Δ upper X : ℝ) (cs : List ℕ),
      spectatorBulkCount k L = b + b → cs.length = k →
      0 ≤ cb →
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
      smoothGiantLogNormalizer (smoothGiantPrimeRange G) logCellProfile G ≤ L →
      ∀ (q : Fin (b + b) → ℕ) [∀ i, Fact (q i).Prime],
      FrozenInitialSpectatorData Aset N q L ε p₀ D →
      ∀ (sl sr : Fin b → Q) (fallback : Q)
        (Dq : ∀ i, (ZMod (q i))ˣ) (childBound pivotBound V : ℕ → ℕ),
      Monotone V →
      (V k : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ)) →
      ((transferFrequencyRange (V k)).card : ℝ) ≤ Real.exp (Afreq * (b + b : ℕ)) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * (b + b : ℕ))) →
      0 ≤ Δ → Δ ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) (b + b : ℕ) →
      Real.exp Δ ≤ upper → upper - Real.exp Δ ≤ Real.exp (Wwin * (b + b : ℕ)) →
      ∀ favorable : ℕ → Bool,
      let F := movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b b (initialSmallCellList top cs).length cb cd sl sr fallback)
        (fun i => normalizedResidueTransform (tailDensityMask Aset N (q i))) Dq Finset.univ
        ψ X (Real.exp Δ) upper
      Real.exp (-B * (2 : ℝ) ^ k * (b + b : ℕ)) ≤
        ‖scheduledCellAmplitude Subtype.val (List.ofFn q)
          (completedCompensationPrior Aset Bset N Y endpoint D Q top cs)
          childBound pivotBound V F logCellProfile (fun _ => G)
          (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
          (fun c => primeSubsetPrior Q (selectedTailCellPrimes Aset Bset N Y endpoint D c))
          (primeSubsetPrior Q Qb) top cs k (b + b)
          (normalizedResidueFamily (tailDensityMask Aset N))
          (normalizedResidueFamily (tailDensityMask Aset N)) favorable‖ → False := by
  have hf := P0.moving_selected_initial_final_contradiction_varying_window C hM ψ
    (Bs + 1) (BD + 2) Bz B 1 Dφ 1 2 (by linarith) (by linarith) hBz
    (by norm_num) hDφ (by norm_num) (by norm_num) Dφ hDφ hloglip
  filter_upwards [hf, eventually_ge_atTop (2 : ℕ)] with k hf hk
  intro Wwin hWwin hdepth Afreq
  obtain ⟨ε, hε, hε1, p₀, hp₀, he⟩ := hf Wwin hWwin (by linarith)
  refine ⟨ε, hε, hε1, p₀, hp₀, ?_⟩
  filter_upwards [he, eventual_scheduled_comparison_cutoffs k k p₀ (fun _ => Afreq),
    eventual_scheduled_comparison_count k, eventual_selected_bulk_mass hM,
    (spectatorBulkCount_tendsto k (by omega)).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with L he hcut hcount hmass hm hL
  intro Aset Bset hA hB N hN b endpoint top a Y G J cb cd Δ upper X cs hsize hlen hcb
    hJ hJerr hJgap Q D Qb htop hcs hlower hG hcg q inst hq sl sr fallback Dq
    childBound pivotBound V hV hVbound hVcard hV0 hΔ hΔbound hupper hwindow favorable F hamp
  have hm' : 1 ≤ b + b := by
    exact_mod_cast (show (1 : ℝ) ≤ (b + b : ℕ) by simpa only [hsize] using hm)
  have hQprime := initialRegularPrimeRange_prime L
  let : Nonempty Q := ⟨⟨(selected_regular_alphabet_nonempty htop).choose,
    (selected_regular_alphabet_nonempty htop).choose_spec⟩⟩
  obtain ⟨hbulk, hbulklower⟩ := selected_bulk_prime_range L (by linarith) D
  have hDcard : D.card ≤ 2 := scheduledPageDeletions_card P0 L _
  obtain ⟨hμdata, hμlower, hνdata, hνlower⟩ := selected_schedule_prime_data htop hcs
    (by linarith) hlower hbulk hbulklower (hmass D hDcard)
  obtain ⟨tier, hμtier, hνtier⟩ := selected_cells_prime_tiers k (by omega) (by linarith)
    hBD hBz hcb hJ hJerr hJgap htop hcs
  have hdrop : cs.drop k = [] := by rw [← hlen, List.drop_length]
  have ht := hνtier k (b + b) k (by omega)
  rw [hdrop] at ht
  obtain ⟨tierB, hTierBound, hBtier⟩ := ht
  have hνd := hνdata k (b + b) k
  have hνl := hνlower k (b + b) k
  rw [hdrop] at hνd hνl
  let Qν := scheduledRegularPrimeSets (selectedTailCellPrimes Aset Bset N Y endpoint D)
    Qb top [] k (b + b)
  let setsReg := primeMaskExtension Q (tailDensityMask Aset N)
  have hsmallsets : ∀ p, p.Prime → (setsReg p).Nonempty ∧ (setsReg p).card < p :=
    tailPrimeMaskExtension_data hA hB N Q hQprime (fun p hp => hN p (hQprime p hp))
  have hcomplex : ((D.card + (Fintype.card (MovingRegularSlot k 6 (b + b)) +
      4 * k * 2 ^ k)) + (List.ofFn q).length : ℕ) ≤
      scheduledComparisonCount k (spectatorBulkCount k L) := by
    rw [hsize]
    exact scheduled_comparison_count k k 6 _ le_rfl (by omega) D (List.ofFn q) hDcard (by simp)
  have hcomplexReal : ((D.card + (Fintype.card (MovingRegularSlot k 6 (b + b)) +
      4 * k * 2 ^ k)) + (List.ofFn q).length : ℕ) ≤ Real.exp ((2 + 1) * L) := by
    have hh : (((D.card + (Fintype.card (MovingRegularSlot k 6 (b + b)) +
        4 * k * 2 ^ k)) + (List.ofFn q).length : ℕ) : ℝ) ≤
        scheduledComparisonCount k (spectatorBulkCount k L) := by exact_mod_cast hcomplex
    exact hh.trans (by norm_num; exact hcount)
  have hcuts := hcut.2.2.2.2 k le_rfl (V k) (by simpa only [hsize] using hVbound)
  have hprimeBand (i) := hcut.2.2.2.1 (q i) (hq.lower i) (hq.upper i)
  have hbulkD : Disjoint Qb D :=
    Finset.disjoint_left.mpr (fun _ hp hd => (Finset.mem_sdiff.mp hp).2 hd)
  have hpage := selected_schedule_avoids_giant_page P0 Aset Bset N endpoint Y L
    (scheduledComparisonCutoff L) top cs Qb hbulkD
  have hpageν (z : PrimitiveRealZero)
      (hz : selectedPageZero P0 (giantProgressionCutoff L) = some z)
      (p : ℕ) (hp : deletedConductorPrime z.modulus (scheduledComparisonCutoff L) = some p)
      (i : MovingRegularSlot k 6 (b + b)) : p ∉ Qν i := by
    have hh := (hpage z hz p hp).2 k (b + b) k
    rw [hdrop] at hh
    exact hh i
  have hShell : primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
      (Real.exp ((6 / 1000 : ℝ) * L)) ⊆ Q := by
    simpa only [Finset.sdiff_empty] using initial_broad_cell_subset L (4 / 1000)
      (6 / 1000) (by linarith) (by norm_num) ∅
  have hfreqCard : (((transferFrequencyRange (V k)).erase 0).card : ℝ) ≤
      Real.exp (Afreq * (b + b : ℕ)) := by
    have he : (((transferFrequencyRange (V k)).erase 0).card : ℝ) ≤
        (transferFrequencyRange (V k)).card := by exact_mod_cast Finset.card_erase_le
    exact he.trans hVcard
  have hd := he b hsize
  dsimp only at hd
  apply hd tierB Q hQprime b (initialSmallCellList top cs).length sl sr fallback
    childBound pivotBound V (List.ofFn q) q Dq (fun i => tailDensityMask Aset N (q i))
    (fun _ => ε / 2) (scheduledComparisonPrimeLo L) (scheduledComparisonCutoff L)
    (fun p => tier p) X Δ upper logCellProfile (fun _ => G) D
    (completedCompensationSets Aset Bset N Y endpoint D top cs) Qν setsReg G cb cd
    (normalizedResidueFamily (tailDensityMask Aset N)) favorable
    (scheduled_final_length top cs k hlen) hV hfreqCard hVbound hV0 hΔ hΔbound hupper hwindow
    (by have he := Real.one_le_exp (show 0 ≤ (49 / 1000 : ℝ) * L by positivity); linarith)
    hTierBound hm' hq.ge_cutoff hq.nonempty hq.proper
    (hq.comparison_upper (by linarith)) hq.balanced_lower hq.balanced_upper (fun _ => by linarith)
    hq.character_bound logCellProfile_nonneg
    (fun x => (abs_of_nonneg (logCellProfile_nonneg x)).trans_le (logCellProfile_le_one x))
    hloglip logCellProfile_zero_outside hShell hcomplexReal
    (by intro p hp; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp; exact (inferInstance : Fact (q i).Prime).out)
    (fun _ => rfl) (fun j => (hμdata j).1) (fun i => (hνd i).1)
    (fun j => (hμdata j).2) (fun i => (hνd i).2) hμlower hνl
    (by intro p hp; exact List.mem_ofFn.mp hp) hq.injective hG
    (by intro j hj p hp; exact hμtier j (by omega) p hp) (fun i p hp => hBtier i p hp)
    hcuts.2 hcuts.1 hcut.2.1 hcut.2.2.1 (fun p => initialRegularPrimeRange_upper L p p.property)
    hprimeBand (fun z hz p hp j => (hpage z hz p hp).1 j) (hq.avoids_giant_page)
    hpageν (hq.avoids_bulk_page) hsmallsets hcg
  unfold scheduledCellAmplitude at hamp
  rw [hdrop, scheduledRegularPrior_prime] at hamp
  rw [movingTemplatePrimeAmplitude_regular_congr Subtype.val (List.ofFn q)
    (completedCompensationPrior Aset Bset N Y endpoint D Q top cs) childBound pivotBound V
    F logCellProfile (fun _ => G) k (scheduledSmallLength []) (b + b)
    (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
    (fun i => primeSubsetPrior Q (Qν i))
    (normalizedResidueFamily (tailDensityMask Aset N)) (normalizedResidueFamily setsReg)
    (normalizedResidueFamily (tailDensityMask Aset N)) favorable
    (fun p => (normalizedResidueFamily_primeMaskExtension Q (tailDensityMask Aset N) p p.property).symm)] at hamp
  exact hamp

end Ostmann

end OAI
