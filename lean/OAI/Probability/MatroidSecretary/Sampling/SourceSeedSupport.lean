import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# Full support of the actual source seed

All four masks and both coins remain in the source law, including coordinates
unused in the selected branch. Strictly positive atom masses justify finite
conditional reconstruction on every realizable observation fiber. No nonempty
label or positive-rank assumption is made.

Source: `sections/secretary.tex`, conditional reconstruction paragraph (lines
65–81), SHA256 `3554fe0f7296782edf63cc7f1305c377e7a7b9d8f8948b9510ea4ad02a702d63`.
These are supporting positivity obligations, not the secretary endpoint or a
replacement for the joint-law and prefix-only online-rule constructions.
-/

namespace MatroidProphet.SourceSeedSupport

open MeasureTheory Finset

lemma bitsWeight_pos {α : Type*} [DecidableEq α] (q : α → ℝ)
    (h0 : ∀ e, 0 < q e) (h1 : ∀ e, q e < 1) (V S : Finset α) :
    0 < bitsWeight q V S := by
  apply Finset.prod_pos
  intro e he
  split_ifs
  · exact h0 e
  · exact sub_pos.mpr (h1 e)

lemma bernoulliSeedLaw_singleton_pos {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 < q e) (h1 : ∀ e, q e < 1) (r : Seed bits) :
    0 < bernoulliSeedLaw q (fun e => (h0 e).le) (fun e => (h1 e).le) {r} := by
  rw [bernoulliSeedLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change 0 < ENNReal.ofReal (bitsWeight q univ (seedSet r))
  exact ENNReal.ofReal_pos.mpr (bitsWeight_pos q h0 h1 _ _)

lemma maskCoinLaw_singleton_pos (n : ℕ) (p : ℝ) (h0 : 0 < p) (h1 : p < 1)
    (r : Seed n) : 0 < maskCoinLaw n p h0.le h1.le {r} :=
  bernoulliSeedLaw_singleton_pos (fun _ => p) (fun _ => h0) (fun _ => h1) r

lemma prod_singleton_pos {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (a : α) (b : β) (ha : 0 < μ {a}) (hb : 0 < ν {b}) :
    0 < μ.prod ν {(a,b)} := by
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  exact ENNReal.mul_pos ha.ne' hb.ne'

lemma mainBlockLaw_singleton_pos (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 < q j) (h1 : ∀ j, q j < 1) (b : MainSeedBlocks n) :
    0 < mainBlockLaw n q (fun j => (h0 j).le) (fun j => (h1 j).le) {b} := by
  rcases b with ⟨H,D,C,T,b⟩
  unfold mainBlockLaw
  apply prod_singleton_pos
  · exact maskCoinLaw_singleton_pos n (q 0) (h0 0) (h1 0) H
  · apply prod_singleton_pos
    · exact maskCoinLaw_singleton_pos n (q 1) (h0 1) (h1 1) D
    · apply prod_singleton_pos
      · exact maskCoinLaw_singleton_pos n (q 2) (h0 2) (h1 2) C
      · apply prod_singleton_pos
        · exact maskCoinLaw_singleton_pos n (q 3) (h0 3) (h1 3) T
        · exact maskCoinLaw_singleton_pos 2 (q 4) (h0 4) (h1 4) b

/-- The block encoding retains every bit; it is onto even for an empty ground set. -/
lemma encodeMainSeed_surjective (n : ℕ) :
    Function.Surjective (@encodeMainSeed n) := by
  intro r
  let block (j : Fin 4) : Seed n := fun e =>
    r ⟨4 * e.val + j.val, by dsimp [mainSeedBits]; omega⟩
  let coins : Seed 2 := fun j =>
    r ⟨4 * n + j.val, by dsimp [mainSeedBits]; omega⟩
  refine ⟨(block 0, block 1, block 2, block 3, coins), ?_⟩
  funext i
  dsimp only [encodeMainSeed]
  split_ifs with hi h0 h1 h2
  all_goals
    dsimp only [block, coins]
    congr 1
    apply Fin.ext
    dsimp
    omega

lemma mainSeedLaw_singleton_pos (n : ℕ) (q : Fin 5 → ℝ)
    (h0 : ∀ j, 0 < q j) (h1 : ∀ j, q j < 1) (r : Seed (mainSeedBits n)) :
    0 < mainSeedLaw n q (fun j => (h0 j).le) (fun j => (h1 j).le) {r} := by
  obtain ⟨b, hb⟩ := encodeMainSeed_surjective n r
  rw [mainSeedLaw, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  apply lt_of_lt_of_le (mainBlockLaw_singleton_pos n q h0 h1 b)
  apply measure_mono
  intro x hx
  have hx' : x = b := Set.mem_singleton_iff.mp hx
  subst x
  exact hb

lemma sourceCoinProbability_pos (j : Fin 5) : 0 < sourceCoinProbability j := by
  unfold sourceCoinProbability
  split_ifs <;> norm_num [thinningRate]

lemma sourceCoinProbability_lt_one (j : Fin 5) : sourceCoinProbability j < 1 := by
  unfold sourceCoinProbability
  split_ifs <;> norm_num [thinningRate]

/-- Every complete source seed has positive mass, with no exceptional labels or ranks. -/
theorem sourceSeedLaw_singleton_pos (n : ℕ) (r : Seed (mainSeedBits n)) :
    0 < sourceSeedLaw n {r} :=
  mainSeedLaw_singleton_pos n sourceCoinProbability sourceCoinProbability_pos
    sourceCoinProbability_lt_one r

/-- A source observation fiber has positive probability exactly when it is realizable.
The observation may keep branch, mask, and any additional seed coordinates. -/
theorem sourceSeedLaw_fiber_pos_iff (n : ℕ) {β : Type*}
    (f : Seed (mainSeedBits n) → β) (b : β) :
    0 < sourceSeedLaw n {r | f r = b} ↔ ∃ r, f r = b := by
  constructor
  · intro h
    by_contra hn
    have he : {r | f r = b} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hr => hn ⟨r,hr⟩
    rw [he, measure_empty] at h
    exact (lt_irrefl 0) h
  · rintro ⟨r,hr⟩
    apply lt_of_lt_of_le (sourceSeedLaw_singleton_pos n r)
    apply measure_mono
    intro s hs
    have hs' : s = r := Set.mem_singleton_iff.mp hs
    subst s
    exact hr

/-- Real-valued finite conditional-kernel denominators are strictly positive. -/
theorem sourceSeedLaw_fiber_toReal_pos (n : ℕ) {β : Type*}
    (f : Seed (mainSeedBits n) → β) (r : Seed (mainSeedBits n)) :
    0 < (sourceSeedLaw n {s | f s = f r}).toReal := by
  apply ENNReal.toReal_pos
  · exact ((sourceSeedLaw_fiber_pos_iff n f (f r)).mpr ⟨r,rfl⟩).ne'
  · exact measure_ne_top _ _

/-- Every assignment of all four masks, parity, and branch is realized by a seed. -/
theorem exists_mainMasks_mainBranch {n : ℕ} (d : MainMasks n) (j : Bool) :
    ∃ r : Seed (mainSeedBits n), mainMasks r = d ∧ mainBranch r = j := by
  let coins : Seed 2 := fun k => if k = 0 then j else d.odd
  let b : MainSeedBlocks n :=
    (setSeed d.H, setSeed d.D, setSeed d.C, setSeed d.T, coins)
  refine ⟨encodeMainSeed b, ?_, ?_⟩
  · rw [mainMasks_encodeMainSeed]
    simp only [b, seedSet_setSeed, coins]
    simp
  · rw [encodeMainSeed_branch]
    simp [b, coins]

/-- The entire mask/coin assignment has positive mass, including either unused branch. -/
theorem sourceSeedLaw_masks_branch_pos {n : ℕ} (d : MainMasks n) (j : Bool) :
    0 < sourceSeedLaw n {r | mainMasks r = d ∧ mainBranch r = j} := by
  obtain ⟨r, hd, hj⟩ := exists_mainMasks_mainBranch d j
  apply lt_of_lt_of_le (sourceSeedLaw_singleton_pos n r)
  apply measure_mono
  intro s hs
  have hs' : s = r := Set.mem_singleton_iff.mp hs
  subst s
  exact ⟨hd,hj⟩

/-- Both source branches admit every sacrificed-mask fiber with positive mass. -/
theorem sourceSeedLaw_branch_mask_pos (n : ℕ) (j : Bool) (P : Finset (Fin n)) :
    0 < sourceSeedLaw n {r | mainBranch r = j ∧
      (if mainBranch r then (mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C
        else (mainMasks r).H) = P} := by
  let d : MainMasks n := ⟨P, ∅, ∅, ∅, false⟩
  apply lt_of_lt_of_le (sourceSeedLaw_masks_branch_pos d j)
  apply measure_mono
  intro r hr
  exact ⟨hr.2, by simp [hr.1, d]⟩

/-- The positivity statement for the actual algorithmic sacrificed mask, rather
than a surrogate observation map. -/
theorem sourceSeedLaw_actual_branch_mask_pos {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (j : Bool) (P : Finset (Fin n)) :
    0 < sourceSeedLaw n {r | mainBranch r = j ∧ (completeHiddenRule M hE).mask r = P} := by
  simpa only [completeHiddenRule, branchHiddenRule, MainAlgorithm.hidden,
    roundedMaximumHidden, Maximum.maximumHidden] using sourceSeedLaw_branch_mask_pos n j P

/-- The four masks, parity, and branch determine every original seed coordinate. -/
theorem mainMasks_mainBranch_injective (n : ℕ) :
    Function.Injective (fun r : Seed (mainSeedBits n) => (mainMasks r, mainBranch r)) := by
  intro r s hrs
  have hd : mainMasks r = mainMasks s := congrArg Prod.fst hrs
  have hb : mainBranch r = mainBranch s := congrArg Prod.snd hrs
  have hm (j : Fin 4) : seedMask r j = seedMask s j := by
    fin_cases j
    · exact congrArg MainMasks.H hd
    · exact congrArg MainMasks.D hd
    · exact congrArg MainMasks.C hd
    · exact congrArg MainMasks.T hd
  funext i
  by_cases hi : i.val < 4*n
  · let e : Fin n := ⟨i.val / 4, by omega⟩
    let j : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩
    have he := congrArg (fun P : Finset (Fin n) => e ∈ P) (hm j)
    simp only [seedMask, Finset.mem_filter, Finset.mem_univ, true_and] at he
    apply Bool.eq_iff_iff.mpr
    have hx : (⟨4*e.val+j.val, by dsimp [mainSeedBits]; omega⟩ : Fin (mainSeedBits n)) = i := by
      apply Fin.ext
      dsimp [e,j]
      omega
    simpa only [hx] using (iff_of_eq he)
  · have hival := i.isLt
    dsimp [mainSeedBits] at hival
    by_cases hlast : i.val = 4*n
    · have hx : (⟨4*n, by dsimp [mainSeedBits]; omega⟩ : Fin (mainSeedBits n)) = i := by
        apply Fin.ext
        exact hlast.symm
      simpa only [mainBranch, hx] using hb
    · have hlast' : i.val = 4*n+1 := by omega
      have hx : (⟨4*n+1, by dsimp [mainSeedBits]; omega⟩ : Fin (mainSeedBits n)) = i := by
        apply Fin.ext
        exact hlast'.symm
      have ho := congrArg MainMasks.odd hd
      simpa only [mainMasks, hx] using ho

/-- Every statistic of the complete source seed can be written using all masks and coins. -/
theorem source_statistic_factors {n : ℕ} {β : Type*}
    (f : Seed (mainSeedBits n) → β) :
    ∃ g : MainMasks n → Bool → β, ∀ r, g (mainMasks r) (mainBranch r) = f r := by
  classical
  let chooseSeed (d : MainMasks n) (j : Bool) :=
    Classical.choose (exists_mainMasks_mainBranch d j)
  have choose_spec (d : MainMasks n) (j : Bool) :
      (mainMasks (chooseSeed d j), mainBranch (chooseSeed d j)) = (d,j) := by
    exact Prod.ext (Classical.choose_spec (exists_mainMasks_mainBranch d j)).1
      (Classical.choose_spec (exists_mainMasks_mainBranch d j)).2
  refine ⟨fun d j => f (chooseSeed d j), ?_⟩
  intro r
  exact congrArg f (mainMasks_mainBranch_injective n
    (choose_spec (mainMasks r) (mainBranch r)))

/-- Since there are no null source atoms, almost-sure seed properties are pointwise. -/
theorem sourceSeedLaw_ae_iff (n : ℕ) (P : Seed (mainSeedBits n) → Prop) :
    (∀ᵐ r ∂sourceSeedLaw n, P r) ↔ ∀ r, P r := by
  rw [ae_iff_of_countable]
  exact ⟨fun h r => h r (sourceSeedLaw_singleton_pos n r).ne', fun h r _ => h r⟩

end MatroidProphet.SourceSeedSupport

end OAI
