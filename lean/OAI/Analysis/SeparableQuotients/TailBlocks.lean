import OAI.Analysis.SeparableQuotients.BlockEstimates

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

lemma BlockSequence.support_mem_tail {f : Family} (z : BlockSequence f) (a : ℕ)
    {x : Γ →₀ ℝ} (hx : x ∈ z.tailSpan a) {α : Γ} (hα : α ∈ x.support) :
    ∃ n, a ≤ n ∧ α ∈ (z.vector n).support := by
  have hprop : ∀ (u : Γ →₀ ℝ), u ∈ z.tailSpan a →
      ∀ α ∈ u.support, ∃ n, a ≤ n ∧ α ∈ (z.vector n).support := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, rfl⟩ := hy
      intro α hα
      exact ⟨n+a, by omega, hα⟩
    | zero => simp
    | add u v _ _ hu hv =>
      intro α hα
      rcases Finset.mem_union.mp (Finsupp.support_add hα) with h | h
      · exact hu α h
      · exact hv α h
    | smul c u _ hu =>
      intro α hα
      exact hu α (Finsupp.support_smul hα)
  exact hprop x hx α hα

noncomputable def BlockSequence.prefixSupport {f : Family} (z : BlockSequence f) (b : ℕ) : Finset Γ :=
  (Finset.range b).biUnion (fun n => (z.vector n).support)

lemma BlockSequence.prefixSupport_mono {f : Family} (z : BlockSequence f) : Monotone z.prefixSupport := by
  intro a b hab
  exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono hab)

lemma BlockSequence.support_subset_prefix {f : Family} (z : BlockSequence f) (a : ℕ)
    {x : Γ →₀ ℝ} (hx : x ∈ z.tailSpan a) : ∃ b, a ≤ b ∧ x.support ⊆ z.prefixSupport b := by
  have hprop : ∀ (u : Γ →₀ ℝ), u ∈ z.tailSpan a →
      ∃ b, a ≤ b ∧ u.support ⊆ z.prefixSupport b := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, rfl⟩ := hy
      refine ⟨n+a+1, by omega, ?_⟩
      intro α hα
      exact Finset.mem_biUnion.mpr ⟨n+a, Finset.mem_range.mpr (by omega), hα⟩
    | zero => exact ⟨a, le_rfl, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨b, hb, hbu⟩ := hu
      obtain ⟨c, hc, hcv⟩ := hv
      refine ⟨max b c, hb.trans (le_max_left _ _), ?_⟩
      intro α hα
      rcases Finset.mem_union.mp (Finsupp.support_add hα) with h | h
      · exact z.prefixSupport_mono (le_max_left _ _) (hbu h)
      · exact z.prefixSupport_mono (le_max_right _ _) (hcv h)
    | smul c u _ hu =>
      obtain ⟨b, hb, hbu⟩ := hu
      exact ⟨b, hb, fun _ h => hbu (Finsupp.support_smul h)⟩
  exact hprop x hx

lemma BlockSequence.prefix_tail_successive {f : Family} (z : BlockSequence f) (b : ℕ)
    {x y : Γ →₀ ℝ} (hx : x.support ⊆ z.prefixSupport b) (hy : y ∈ z.tailSpan b) :
    ∀ α ∈ x.support, ∀ β ∈ y.support,
      α < β ∧ (f = .mixed → Colors.color α < Colors.color β) := by
  intro α hα β hβ
  obtain ⟨i, hi, hiα⟩ := Finset.mem_biUnion.mp (hx hα)
  obtain ⟨j, hj, hjβ⟩ := z.support_mem_tail b hy hβ
  exact z.successive i j (lt_of_lt_of_le (Finset.mem_range.mp hi) hj) α hiα β hjβ

lemma BlockSequence.tailSpan_mono {f : Family} (z : BlockSequence f) {a b : ℕ} (hab : a ≤ b) :
    z.tailSpan b ≤ z.tailSpan a := by
  apply Submodule.span_le.mpr
  rintro u ⟨n, rfl⟩
  apply Submodule.subset_span
  refine ⟨n+(b-a), ?_⟩
  change z.vector (n+(b-a)+a) = z.vector (n+b)
  rw [show n+(b-a)+a = n+b by omega]

lemma BlockSequence.tail_pure_color {f : Family} (z : BlockSequence f) (a : ℕ)
    {x : Γ →₀ ℝ} (hx : x ∈ z.tailSpan a) (c : ℕ) (hc : f = .pure c) :
    ∀ α ∈ x.support, Colors.color α = c := by
  intro α hα
  obtain ⟨n, _, hn⟩ := z.support_mem_tail a hx hα
  exact z.pure_color c hc n α hn

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

noncomputable def BlockSequence.prefixRho {f : Family} (z : BlockSequence f) (a : ℕ) : ℕ :=
  (z.prefixSupport a ×ˢ z.prefixSupport a).sup (fun p => rho (min p.1 p.2) (max p.1 p.2))

lemma BlockSequence.le_prefixRho {f : Family} (z : BlockSequence f) (a : ℕ) {α β : Γ}
    (hα : α ∈ z.prefixSupport a) (hβ : β ∈ z.prefixSupport a) :
    rho (min α β) (max α β) ≤ z.prefixRho a :=
  Finset.le_sup (b := (α, β)) (f := fun p => rho (min p.1 p.2) (max p.1 p.2)) (Finset.mem_product.mpr ⟨hα, hβ⟩)

/-- The recursively selected unit blocks, before pathwise-Cauchy differences.
No weak compactness hypothesis is smuggled into this structure. -/
structure PreliminaryData {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (n : ℕ) where
  vector : Γ →₀ ℝ
  start : ℕ
  finish : ℕ
  lower : ℕ
  upper : ℕ
  mem : vector ∈ z.tailSpan start
  support : vector.support ⊆ z.prefixSupport finish
  finish_ge : start ≤ finish
  unit : ‖norming.includeFinite vector‖ = 1
  prescribed : J < lower
  order : lower ≤ upper
  coherence : z.prefixRho start < lower
  partition : PartitionBound (norming.includeFinite vector) (f.L lower) 8 f.r
  tail_small : vectorL1 vector * tail (fun j => 1/(f.m j : ℝ)) (upper+1) ≤ ε/2
  tail_vanish : vectorL1 vector * tail (fun j => 1/(f.m j : ℝ)) (upper+1) ≤ 1/(n+1 : ℝ)

lemma exists_preliminaryData {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (n a B : ℕ) : ∃ d : PreliminaryData z J ε n, d.start = a ∧ B < d.lower := by
  let j := B+J+z.prefixRho a+1
  obtain ⟨u, hu, hunit, hpart⟩ := z.exists_partition_unit a (f.L j) (f.L_pos j)
  obtain ⟨b, hb, hbu⟩ := z.support_subset_prefix a hu
  have ht : Tendsto (fun t => vectorL1 u * tail (fun l => 1/(f.m l : ℝ)) (t+1)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((tendsto_tail (fun l => 1/(f.m l : ℝ))).comp (tendsto_add_atTop_nat 1)))
  have hmin : 0 < min (ε/2) (1/(n+1 : ℝ)) := lt_min (by linarith) (by positivity)
  obtain ⟨T, hTj, hT⟩ := (eventually_ge_atTop j |>.and (ht.eventually (eventually_lt_nhds hmin))).exists
  let d : PreliminaryData z J ε n := {
    vector := u
    start := a
    finish := b
    lower := j
    upper := T
    mem := hu
    support := hbu
    finish_ge := hb
    unit := hunit
    prescribed := by dsimp [j]; omega
    order := hTj
    coherence := by dsimp [j]; omega
    partition := hpart
    tail_small := hT.le.trans (min_le_left _ _)
    tail_vanish := hT.le.trans (min_le_right _ _) }
  exact ⟨d, rfl, by change B < j; dsimp [j]; omega⟩

noncomputable def preliminaryChoice {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (n a B : ℕ) : PreliminaryData z J ε n := (exists_preliminaryData z J ε hε n a B).choose

lemma preliminaryChoice_spec {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (n a B : ℕ) : (preliminaryChoice z J ε hε n a B).start = a ∧
      B < (preliminaryChoice z J ε hε n a B).lower := (exists_preliminaryData z J ε hε n a B).choose_spec

noncomputable def preliminaryData {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (a : ℕ) : (n : ℕ) → PreliminaryData z J ε n
  | 0 => preliminaryChoice z J ε hε 0 a 0
  | n+1 => preliminaryChoice z J ε hε (n+1) (preliminaryData z J ε hε a n).finish
      (preliminaryData z J ε hε a n).upper

lemma preliminaryData_start_zero {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a : ℕ) :
    (preliminaryData z J ε hε a 0).start = a := (preliminaryChoice_spec z J ε hε 0 a 0).1

lemma preliminaryData_start_succ {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a n : ℕ) :
    (preliminaryData z J ε hε a (n+1)).start = (preliminaryData z J ε hε a n).finish :=
  (preliminaryChoice_spec z J ε hε (n+1) _ _).1

lemma preliminaryData_order_succ {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a n : ℕ) :
    (preliminaryData z J ε hε a n).upper < (preliminaryData z J ε hε a (n+1)).lower :=
  (preliminaryChoice_spec z J ε hε (n+1) _ _).2

lemma preliminaryData_start_mono {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a : ℕ) :
    Monotone (fun n => (preliminaryData z J ε hε a n).start) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [preliminaryData_start_succ]
  exact (preliminaryData z J ε hε a n).finish_ge

lemma preliminaryData_finish_le_start {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (a i j : ℕ) (hij : i < j) :
    (preliminaryData z J ε hε a i).finish ≤ (preliminaryData z J ε hε a j).start := by
  rw [← preliminaryData_start_succ]
  exact preliminaryData_start_mono z J ε hε a (by omega)

lemma preliminaryData_order {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (a i j : ℕ) (hij : i < j) :
    (preliminaryData z J ε hε a i).upper < (preliminaryData z J ε hε a j).lower := by
  have hlow : StrictMono (fun n => (preliminaryData z J ε hε a n).lower) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (preliminaryData z J ε hε a n).order.trans_lt (preliminaryData_order_succ z J ε hε a n)
  exact (preliminaryData_order_succ z J ε hε a i).trans_le (hlow.monotone (by omega))

noncomputable def preliminaryBlocks {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε) (a : ℕ) :
    BlockSequence f where
  vector n := (preliminaryData z J ε hε a n).vector
  nonzero n := by
    intro hz
    have hh := (preliminaryData z J ε hε a n).unit
    simp [hz] at hh
  successive i j hij := z.prefix_tail_successive _ (preliminaryData z J ε hε a i).support
    (z.tailSpan_mono (preliminaryData_finish_le_start z J ε hε a i j hij) (preliminaryData z J ε hε a j).mem)
  pure_color c hc n := z.tail_pure_color _ (preliminaryData z J ε hε a n).mem c hc

lemma preliminaryData_coherence {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (hε : 0 < ε)
    (a i j : ℕ) (hij : i < j) {α β : Γ}
    (hα : α ∈ (preliminaryData z J ε hε a i).vector.support)
    (hβ : β ∈ (preliminaryData z J ε hε a i).vector.support) :
    rho (min α β) (max α β) < (preliminaryData z J ε hε a j).lower := by
  apply lt_of_le_of_lt (z.le_prefixRho _ ?_ ?_) (preliminaryData z J ε hε a j).coherence
  · exact z.prefixSupport_mono (preliminaryData_finish_le_start z J ε hε a i j hij)
      ((preliminaryData z J ε hε a i).support hα)
  · exact z.prefixSupport_mono (preliminaryData_finish_le_start z J ε hε a i j hij)
      ((preliminaryData z J ε hε a i).support hβ)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.SeriesTails
open Filter
open scoped Topology Classical

lemma tail_antitone (a : ℕ → ℝ) (ha : Summable a) (hn : ∀ n, 0 ≤ a n) : Antitone (tail a) := by
  intro N M hNM
  have hs := ((summable_nat_add_iff N).mpr ha).sum_add_tsum_nat_add (M-N)
  have hid : (∑' k, a (k+(M-N)+N)) = tail a M := by
    apply tsum_congr
    intro k
    rw [show k+(M-N)+N = k+M by omega]
  rw [hid] at hs
  have hpos : 0 ≤ ∑ k ∈ Finset.range (M-N), a (k+N) := Finset.sum_nonneg (fun _ _ => hn _)
  change tail a M ≤ ∑' k, a (k+N)
  linarith

end SeparableQuotient.SeriesTails

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

lemma vectorL1_eq_sum {x : Γ →₀ ℝ} {s : Finset Γ} (hs : x.support ⊆ s) :
    vectorL1 x = ∑ a ∈ s, |x a| := by
  apply Finset.sum_subset hs
  intro a _ ha
  rw [Finsupp.notMem_support_iff.mp ha, abs_zero]

lemma vectorL1_sub_le (x y : Γ →₀ ℝ) : vectorL1 (x-y) ≤ vectorL1 x + vectorL1 y := by
  rw [vectorL1_eq_sum Finsupp.support_sub,
    vectorL1_eq_sum (Finset.subset_union_left : x.support ⊆ x.support ∪ y.support),
    vectorL1_eq_sum (Finset.subset_union_right : y.support ⊆ x.support ∪ y.support), ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => abs_sub _ _)

lemma PartitionBound.mono {x : E} {N M : ℕ} {A r : ℝ} (h : PartitionBound x N A r) (hMN : M ≤ N) :
    PartitionBound x M A r := fun d hd hdM => h d hd (hdM.trans hMN)

lemma PartitionBound.sub {x y : E} {N : ℕ} {A B r : ℝ}
    (hx : PartitionBound x N A r) (hy : PartitionBound y N B r) :
    PartitionBound (x-y) N (A+B) r := by
  intro d hd hdN I hI hIs
  calc
    _ ≤ ∑ b, (‖intervalProjection (I b) (hI b) x‖ + ‖intervalProjection (I b) (hI b) y‖) := by
      apply Finset.sum_le_sum
      intro b _
      rw [map_sub]
      exact norm_sub_le _ _
    _ = (∑ b, ‖intervalProjection (I b) (hI b) x‖) + (∑ b, ‖intervalProjection (I b) (hI b) y‖) := Finset.sum_add_distrib
    _ ≤ A * (d : ℝ)^(1/r) + B * (d : ℝ)^(1/r) := add_le_add (hx d hd hdN I hI hIs) (hy d hd hdN I hI hIs)
    _ = _ := by ring

noncomputable def BlockSequence.subsequence {f : Family} (z : BlockSequence f) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    BlockSequence f where
  vector n := z.vector (φ n)
  nonzero n := z.nonzero (φ n)
  successive i j hij := z.successive (φ i) (φ j) (hφ hij)
  pure_color c hc n := z.pure_color c hc (φ n)

lemma BlockSequence.norm_sub_ge_one {f : Family} (z : BlockSequence f) {i j : ℕ} (hij : i < j)
    (hi : ‖z.embed i‖ = 1) : 1 ≤ ‖norming.includeFinite (z.vector i-z.vector j)‖ := by
  have hne := Finsupp.support_nonempty_iff.mpr (z.nonzero i)
  let I := ordinalHull (z.vector i).support hne
  have hI : Set.OrdConnected I := ordinalHull_connected _ _
  have hfix : intervalProjection I hI (z.embed i) = z.embed i :=
    intervalProjection_fixed I hI _ (fun _ ha => mem_ordinalHull hne ha)
  have hzero : intervalProjection I hI (z.embed j) = 0 := by
    apply intervalProjection_eq_zero
    intro a ha haI
    have hlt := (z.successive i j hij _ ((z.vector i).support.max'_mem hne) a ha).1
    exact (not_lt_of_ge haI.2) hlt
  have heq : intervalProjection I hI (norming.includeFinite (z.vector i-z.vector j)) = z.embed i := by
    rw [map_sub]
    change intervalProjection I hI (z.embed i-z.embed j) = z.embed i
    rw [map_sub, hfix, hzero, sub_zero]
  calc
    1 = ‖intervalProjection I hI (norming.includeFinite (z.vector i-z.vector j))‖ := by rw [heq, hi]
    _ ≤ _ := norm_projection_le _ _

noncomputable def BlockSequence.pairDifferences {f : Family} (z : BlockSequence f)
    (hz : ∀ n, ‖z.embed n‖ = 1) : BlockSequence f where
  vector n := z.vector (2*n)-z.vector (2*n+1)
  nonzero n := by
    intro hh
    have hi := z.norm_sub_ge_one (by omega : 2*n < 2*n+1) (hz (2*n))
    simp [hh] at hi
    norm_num at hi
  successive i j hij a ha b hb := by
    have ha' := Finset.mem_union.mp (Finsupp.support_sub ha)
    have hb' := Finset.mem_union.mp (Finsupp.support_sub hb)
    rcases ha' with ha | ha <;> rcases hb' with hb | hb
    all_goals exact z.successive _ _ (by omega) a ha b hb
  pure_color c hc n a ha := by
    rcases Finset.mem_union.mp (Finsupp.support_sub ha) with ha | ha
    · exact z.pure_color c hc (2*n) a ha
    · exact z.pure_color c hc (2*n+1) a ha

lemma BlockSequence.pairDifferences_norm {f : Family} (z : BlockSequence f)
    (hz : ∀ n, ‖z.embed n‖ = 1) (n : ℕ) :
    1 ≤ ‖(z.pairDifferences hz).embed n‖ ∧ ‖(z.pairDifferences hz).embed n‖ ≤ 2 := by
  refine ⟨z.norm_sub_ge_one (by omega) (hz (2*n)), ?_⟩
  change ‖norming.includeFinite (z.vector (2*n)-z.vector (2*n+1))‖ ≤ 2
  rw [map_sub]
  exact (norm_sub_le _ _).trans (by change ‖z.embed (2*n)‖+‖z.embed (2*n+1)‖≤2; rw [hz, hz]; norm_num)

lemma BlockSequence.pairDifferences_path_null {f : Family} (z : BlockSequence f)
    (hz : ∀ n, ‖z.embed n‖ = 1) (hC : ∀ P : InfinitePath f, CauchySeq (fun n => pathFunctional P (z.embed n))) :
    ∀ P : InfinitePath f, Tendsto (fun n => pathFunctional P ((z.pairDifferences hz).embed n)) atTop (𝓝 0) := by
  intro P
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (hC P)
  have he : StrictMono (fun n : ℕ => 2*n) := by intro i j h; dsimp; omega
  have ho : StrictMono (fun n : ℕ => 2*n+1) := by intro i j h; dsimp; omega
  have ht := (ha.comp he.tendsto_atTop).sub (ha.comp ho.tendsto_atTop)
  simpa only [BlockSequence.embed, BlockSequence.pairDifferences, map_sub, sub_self, Function.comp_apply] using ht

end SeparableQuotient.ActualSpace

end

end OAI
