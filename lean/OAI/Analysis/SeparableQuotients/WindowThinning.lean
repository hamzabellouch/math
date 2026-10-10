import OAI.Analysis.SeparableQuotients.TailBlocks

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

lemma FamilyL_mono (f : Family) : Monotone f.L := by
  intro i j hij
  exact (Parameters.L_strict f.s_ge_two).monotone (Nat.sub_le_sub_right hij 1)

lemma tail_sub_mul_le {f : Family} (x y : Γ →₀ ℝ) (T U : ℕ) (hTU : T ≤ U) :
    vectorL1 (x-y) * tail (fun j => 1/(f.m j : ℝ)) (U+1) ≤
    vectorL1 x * tail (fun j => 1/(f.m j : ℝ)) (T+1) +
    vectorL1 y * tail (fun j => 1/(f.m j : ℝ)) (U+1) := by
  have hn : ∀ j, 0 ≤ 1/(f.m j : ℝ) := fun _ => by positivity
  calc
    _ ≤ (vectorL1 x+vectorL1 y) * tail (fun j => 1/(f.m j : ℝ)) (U+1) :=
      mul_le_mul_of_nonneg_right (vectorL1_sub_le x y) (tail_nonneg _ hn _)
    _ = vectorL1 x * tail (fun j => 1/(f.m j : ℝ)) (U+1) +
      vectorL1 y * tail (fun j => 1/(f.m j : ℝ)) (U+1) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (tail_antitone _ f.m_inv_summable hn (Nat.add_le_add_right hTU 1)) (vectorL1_nonneg x)) le_rfl

/-- Window blocks with partition estimates, pathwise nullity, and coherent support bounds. -/
structure WindowBlocks {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (a : ℕ) where
  blocks : BlockSequence f
  lower : ℕ → ℕ
  upper : ℕ → ℕ
  mem_tail : ∀ n, blocks.vector n ∈ z.tailSpan a
  lower_norm : ∀ n, 1 ≤ ‖blocks.embed n‖
  upper_norm : ∀ n, ‖blocks.embed n‖ ≤ 2
  prescribed : ∀ n, J < lower n
  order : ∀ n, lower n ≤ upper n
  separated : ∀ i j, i < j → upper i < lower j
  coherence : ∀ i j k, j < i → k < i → ∀ α ∈ (blocks.vector j).support,
    ∀ β ∈ (blocks.vector k).support, rho (min α β) (max α β) < lower i
  partition : ∀ n, PartitionBound (blocks.embed n) (f.L (lower n)) 16 f.r
  tail_small : ∀ n, vectorL1 (blocks.vector n) * tail (fun j => 1/(f.m j : ℝ)) (upper n+1) ≤ ε
  tail_vanish : Tendsto (fun n => vectorL1 (blocks.vector n) * tail (fun j => 1/(f.m j : ℝ)) (upper n+1)) atTop (𝓝 0)
  path_null : ∀ P : InfinitePath f, Tendsto (fun n => pathFunctional P (blocks.embed n)) atTop (𝓝 0)

lemma exists_windowBlocks {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a : ℕ) :
    Nonempty (WindowBlocks z J ε a) := by
  let d := preliminaryData z J ε hε a
  let u := preliminaryBlocks z J ε hε a
  have hu (n : ℕ) : ‖u.embed n‖ = 1 := (d n).unit
  obtain ⟨φ, hφ, hC⟩ := u.all_paths_cauchy 1 (fun n => (hu n).le)
  let v := u.subsequence φ hφ
  have hv (n : ℕ) : ‖v.embed n‖ = 1 := hu (φ n)
  let x := v.pairDifferences hv
  let lo (n : ℕ) := (d (φ (2*n))).lower
  let up (n : ℕ) := (d (φ (2*n+1))).upper
  have hx (n : ℕ) : x.vector n = (d (φ (2*n))).vector - (d (φ (2*n+1))).vector := rfl
  have hord {i j : ℕ} (hij : i < j) : (d i).upper < (d j).lower :=
    preliminaryData_order z J ε hε a i j hij
  have hfin {i j : ℕ} (hij : i < j) : (d i).finish ≤ (d j).start :=
    preliminaryData_finish_le_start z J ε hε a i j hij
  have hstart (n : ℕ) : a ≤ (d n).start := by
    rw [← preliminaryData_start_zero z J ε hε a]
    exact preliminaryData_start_mono z J ε hε a (Nat.zero_le n)
  have hup (n : ℕ) : (d (φ (2*n))).upper ≤ (d (φ (2*n+1))).upper :=
    (hord (hφ (by omega))).le.trans (d (φ (2*n+1))).order
  have htail (n : ℕ) : vectorL1 (x.vector n) * tail (fun j => 1/(f.m j : ℝ)) (up n+1) ≤
      vectorL1 (d (φ (2*n))).vector * tail (fun j => 1/(f.m j : ℝ)) ((d (φ (2*n))).upper+1) +
      vectorL1 (d (φ (2*n+1))).vector * tail (fun j => 1/(f.m j : ℝ)) ((d (φ (2*n+1))).upper+1) := by
    rw [hx]
    exact tail_sub_mul_le _ _ _ _ (hup n)
  have hdec (n : ℕ) : vectorL1 (x.vector n) * tail (fun j => 1/(f.m j : ℝ)) (up n+1) ≤ 2/(n+1 : ℝ) := by
    have he : (n : ℝ)+1 ≤ (φ (2*n) : ℝ)+1 := by exact_mod_cast (show n+1 ≤ φ (2*n)+1 by
      have hh : 2*n ≤ φ (2*n) := hφ.id_le (2*n)
      omega)
    have ho : (n : ℝ)+1 ≤ (φ (2*n+1) : ℝ)+1 := by exact_mod_cast (show n+1 ≤ φ (2*n+1)+1 by
      have hh : 2*n+1 ≤ φ (2*n+1) := hφ.id_le (2*n+1)
      omega)
    calc
      _ ≤ 1/(φ (2*n)+1 : ℝ) + 1/(φ (2*n+1)+1 : ℝ) :=
        (htail n).trans (add_le_add (d (φ (2*n))).tail_vanish (d (φ (2*n+1))).tail_vanish)
      _ ≤ 1/(n+1 : ℝ) + 1/(n+1 : ℝ) := add_le_add (one_div_le_one_div_of_le (by positivity) he)
        (one_div_le_one_div_of_le (by positivity) ho)
      _ = _ := by ring
  refine ⟨{
    blocks := x
    lower := lo
    upper := up
    mem_tail := ?_
    lower_norm := fun n => (v.pairDifferences_norm hv n).1
    upper_norm := fun n => (v.pairDifferences_norm hv n).2
    prescribed := fun n => (d (φ (2*n))).prescribed
    order := ?_
    separated := ?_
    coherence := ?_
    partition := ?_
    tail_small := ?_
    tail_vanish := ?_
    path_null := v.pairDifferences_path_null hv hC }⟩
  · intro n
    rw [hx]
    exact (z.tailSpan a).sub_mem (z.tailSpan_mono (hstart _) (d _).mem)
      (z.tailSpan_mono (hstart _) (d _).mem)
  · intro n
    exact ((d (φ (2*n))).order.trans (hup n))
  · intro i j hij
    exact hord (hφ (by omega : 2*i+1 < 2*j))
  · intro i j k hji hki α hα β hβ
    have hprefix (t : ℕ) (hti : t < i) {γ : Γ} (hγ : γ ∈ (x.vector t).support) : γ ∈ z.prefixSupport (d (φ (2*i))).start := by
      rw [hx] at hγ
      rcases Finset.mem_union.mp (Finsupp.support_sub hγ) with hh | hh
      · exact z.prefixSupport_mono (hfin (hφ (by omega))) ((d _).support hh)
      · exact z.prefixSupport_mono (hfin (hφ (by omega))) ((d _).support hh)
    exact (z.le_prefixRho _ (hprefix j hji hα) (hprefix k hki hβ)).trans_lt (d (φ (2*i))).coherence
  · intro n
    have hLow : (d (φ (2*n))).lower ≤ (d (φ (2*n+1))).lower :=
      (d (φ (2*n))).order.trans (hord (hφ (by omega : 2*n < 2*n+1))).le
    have hL := FamilyL_mono f hLow
    have hh := (d (φ (2*n))).partition.sub ((d (φ (2*n+1))).partition.mono hL)
    change PartitionBound (norming.includeFinite (x.vector n)) _ 16 _
    rw [hx, map_sub]
    simpa only [lo, show (8 : ℝ)+8 = 16 by norm_num] using hh
  · intro n
    exact (htail n).trans (by linarith [(d (φ (2*n))).tail_small, (d (φ (2*n+1))).tail_small])
  · have ht : Tendsto (fun n : ℕ => 2/(n+1 : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/(n+1 : ℝ)) atTop (𝓝 0)))
    apply squeeze_zero _ hdec ht
    intro n
    exact mul_nonneg (vectorL1_nonneg _) (tail_nonneg _ (fun _ => by positivity) _)

lemma WindowBlocks.four_hits {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : WindowBlocks z J ε a) (δ : ℝ) (hδ : 0 < δ) (N : Set ℕ) (hN : N.Infinite) :
    ∃ W ⊆ N, W.Infinite ∧ ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ W → S.card = 4 →
      ¬ ∃ P : LegalFinitePath f, ∀ i ∈ S, WindowHit P (w.blocks.vector i) (w.lower i) (w.upper i) δ := by
  apply four_hits_thinning _ _ _ w.order w.separated
    (fun i j hij α hα β hβ => (w.blocks.successive i j hij α hα β hβ).1)
    (fun i j hij α hα β hβ => (w.coherence j i i hij hij α hα β hβ).le)
    2 16 δ w.upper_norm (by norm_num) hδ _ w.tail_vanish w.path_null N hN
  intro i e he hj
  exact typeI_eval_le_of_partition _ _ _ (by norm_num) (w.partition i) e he (FamilyL_mono f hj.le)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.AdaptiveThinning
open scoped Classical

variable (R : ℕ → ℕ → Set ℕ → Prop)
variable (hR : ∀ n i (N : Set ℕ), N.Infinite → ∃ W ⊆ N, W.Infinite ∧ R n i W)

structure Step (n : ℕ) (N : Set ℕ) where
  index : ℕ
  mem : index ∈ N
  rest : Set ℕ
  infinite : rest.Infinite
  subset : rest ⊆ N
  later : ∀ i ∈ rest, index < i
  good : R n index rest

include hR in
lemma exists_step (n : ℕ) (N : Set ℕ) (hN : N.Infinite) : Nonempty (Step R n N) := by
  obtain ⟨i, hi⟩ := hN.nonempty
  have htail : (N \ Set.Iic i).Infinite := hN.sdiff (Set.finite_Iic i)
  obtain ⟨W, hW, hWi, hWR⟩ := hR n i _ htail
  refine ⟨⟨i, hi, W, hWi, fun j hj => (hW hj).1, ?_, hWR⟩⟩
  intro j hj
  have := (hW hj).2
  simpa using this

noncomputable def choice (n : ℕ) (N : Set ℕ) (hN : N.Infinite) : Step R n N :=
  Classical.choice (exists_step R hR n N hN)

structure State (n : ℕ) where
  index : ℕ
  rest : Set ℕ
  infinite : rest.Infinite
  later : ∀ i ∈ rest, index < i
  good : R n index rest

noncomputable def initial : State R 0 :=
  let s := choice R hR 0 Set.univ Set.infinite_univ
  ⟨s.index, s.rest, s.infinite, s.later, s.good⟩

noncomputable def next {n : ℕ} (s : State R n) : State R (n+1) :=
  let t := choice R hR (n+1) s.rest s.infinite
  ⟨t.index, t.rest, t.infinite, t.later, t.good⟩

lemma next_mem {n : ℕ} (s : State R n) : (next R hR s).index ∈ s.rest :=
  (choice R hR (n+1) s.rest s.infinite).mem

lemma next_subset {n : ℕ} (s : State R n) : (next R hR s).rest ⊆ s.rest :=
  (choice R hR (n+1) s.rest s.infinite).subset

noncomputable def state : (n : ℕ) → State R n
  | 0 => initial R hR
  | n+1 => next R hR (state n)

lemma index_strict : StrictMono (fun n => (state R hR n).index) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (state R hR n).later _ (next_mem R hR (state R hR n))

lemma rest_antitone : Antitone (fun n => (state R hR n).rest) := by
  apply antitone_nat_of_succ_le
  intro n
  exact next_subset R hR (state R hR n)

lemma later_mem {n m : ℕ} (hnm : n < m) : (state R hR m).index ∈ (state R hR n).rest := by
  have hm : 0 < m := Nat.zero_lt_of_lt hnm
  have hh : m = (m-1)+1 := by omega
  rw [hh]
  exact rest_antitone R hR (show n ≤ m-1 by omega) (next_mem R hR (state R hR (m-1)))

include hR in
/-- Repeated infinite thinning where the new relation can depend on the already
selected index and its position. No uniform-threshold or countability assumption
on the predicate R is required. -/
theorem exists_adaptive : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ W : ℕ → Set ℕ,
    (∀ n, R n (φ n) (W n)) ∧ (∀ n m, n < m → φ m ∈ W n) := by
  exact ⟨fun n => (state R hR n).index, index_strict R hR,
    fun n => (state R hR n).rest, fun n => (state R hR n).good,
    fun _ _ h => later_mem R hR h⟩

end SeparableQuotient.AdaptiveThinning

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

noncomputable def WindowBlocks.subsequence {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : WindowBlocks z J ε a) (φ : ℕ → ℕ) (hφ : StrictMono φ) : WindowBlocks z J ε a where
  blocks := w.blocks.subsequence φ hφ
  lower n := w.lower (φ n)
  upper n := w.upper (φ n)
  mem_tail n := w.mem_tail (φ n)
  lower_norm n := w.lower_norm (φ n)
  upper_norm n := w.upper_norm (φ n)
  prescribed n := w.prescribed (φ n)
  order n := w.order (φ n)
  separated i j h := w.separated (φ i) (φ j) (hφ h)
  coherence i j k hji hki := w.coherence (φ i) (φ j) (φ k) (hφ hji) (hφ hki)
  partition n := w.partition (φ n)
  tail_small n := w.tail_small (φ n)
  tail_vanish := w.tail_vanish.comp hφ.tendsto_atTop
  path_null P := (w.path_null P).comp hφ.tendsto_atTop

/-- Successively thinned windows. The threshold indexed by n is used strictly after n. -/
structure ThinnedWindows {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (a : ℕ)
    extends WindowBlocks z J ε a where
  threshold : ℕ → ℝ
  threshold_pos : ∀ n, 0 < threshold n
  threshold_charge_succ : ∀ n, (upper n+1 : ℝ) * threshold n = ε * (1/2 : ℝ)^(n+1)
  threshold_charge : ∀ n, (upper n : ℝ) * threshold n ≤ ε * (1/2 : ℝ)^(n+1)
  four_hits_after : ∀ n (S : Finset ℕ), (∀ i ∈ S, n < i) → S.card = 4 →
    ¬ ∃ P : LegalFinitePath f, ∀ i ∈ S,
      WindowHit P (blocks.vector i) (lower i) (upper i) (threshold n)

lemma exists_thinnedWindows {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ)
    (hε : 0 < ε) (a : ℕ) : Nonempty (ThinnedWindows z J ε a) := by
  obtain ⟨w⟩ := exists_windowBlocks z J ε hε a
  let δ (n i : ℕ) : ℝ := ε / (w.upper i+1 : ℝ) * (1/2 : ℝ)^(n+1)
  have hδ (n i : ℕ) : 0 < δ n i := by dsimp [δ]; positivity
  let R (n i : ℕ) (W : Set ℕ) : Prop := ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ W → S.card = 4 →
    ¬ ∃ P : LegalFinitePath f, ∀ k ∈ S,
      WindowHit P (w.blocks.vector k) (w.lower k) (w.upper k) (δ n i)
  have hR (n i : ℕ) (N : Set ℕ) (hN : N.Infinite) : ∃ W ⊆ N, W.Infinite ∧ R n i W :=
    w.four_hits (δ n i) (hδ n i) N hN
  obtain ⟨φ, hφ, W, hW, hlater⟩ := AdaptiveThinning.exists_adaptive R hR
  refine ⟨{
    toWindowBlocks := w.subsequence φ hφ
    threshold n := δ n (φ n)
    threshold_pos n := hδ n (φ n)
    threshold_charge_succ := ?_
    threshold_charge := ?_
    four_hits_after := ?_ }⟩
  · intro n
    change (w.upper (φ n)+1 : ℝ) * (ε / (w.upper (φ n)+1 : ℝ) * (1/2 : ℝ)^(n+1)) = _
    field_simp
  · intro n
    change (w.upper (φ n) : ℝ) * (ε / (w.upper (φ n)+1 : ℝ) * (1/2 : ℝ)^(n+1)) ≤ _
    have hh : (w.upper (φ n) : ℝ) * (ε / (w.upper (φ n)+1 : ℝ)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < w.upper (φ n)+1)]
      nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (by positivity : (0 : ℝ) ≤ (1/2 : ℝ)^(n+1))
  · intro n S hn hcard hh
    apply hW n (S.image φ) _ _
    · obtain ⟨P, hP⟩ := hh
      refine ⟨P, ?_⟩
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      exact hP i hi
    · intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      exact hlater n i (hn i hi)
    · rw [Finset.card_image_of_injective _ hφ.injective, hcard]

lemma ThinnedWindows.hits_after_le_three {f : Family} {z : BlockSequence f} {J a : ℕ} {ε : ℝ}
    (w : ThinnedWindows z J ε a) (n : ℕ) (s : Finset ℕ) (P : LegalFinitePath f) :
    (s.filter (fun i => n < i ∧ WindowHit P (w.blocks.vector i) (w.lower i) (w.upper i) (w.threshold n))).card ≤ 3 := by
  by_contra! h
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (show 4 ≤ (s.filter (fun i => n < i ∧
    WindowHit P (w.blocks.vector i) (w.lower i) (w.upper i) (w.threshold n))).card by omega)
  exact w.four_hits_after n S (fun i hi => (Finset.mem_filter.mp (hS hi)).2.1) hcard
    ⟨P, fun i hi => (Finset.mem_filter.mp (hS hi)).2.2⟩

end SeparableQuotient.ActualSpace

end

end OAI
