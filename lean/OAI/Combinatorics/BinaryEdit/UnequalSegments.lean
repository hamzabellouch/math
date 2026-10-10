import OAI.Combinatorics.BinaryEdit.UnequalCounting
import OAI.Combinatorics.BinaryEdit.CodeTrimming
import OAI.Combinatorics.BinaryEdit.MatchingSegments

namespace OAI

namespace TreeEdit.BinaryLower.Code

/-- Concrete separation of segments in a selected pair of width-`P` blocks.
The words here are indexed functions solely to avoid casts in total length. -/
def BlockSegmentSeparation {α : Type*} {M P : ℕ}
    (x y : Fin (M * P) → α) (bad : ℕ × ℕ → Prop) (a₀ : ℕ) : Prop :=
  ∀ b : ℕ × ℕ, bad b → b.1 < M → b.2 < M →
    ∀ i j a : ℕ, b.1 * P ≤ i → i + a ≤ (b.1 + 1) * P →
      b.2 * P ≤ j → j + a ≤ (b.2 + 1) * P → a₀ ≤ a →
      ∀ w : List α,
        w.Sublist (((List.ofFn x).drop i).take a) →
        w.Sublist (((List.ofFn y).drop j).take a) →
        100 * w.length ≤ 99 * a

/-- Endpoint descriptions give the literal (untruncated) lengths of the
contiguous spans in the corresponding word. -/
theorem ofFn_segment_length_of_span {α : Type*} {r n : ℕ}
    (x : Fin n → α) (f : Fin r → Fin n) {β : Type*} [DecidableEq β]
    (label : Fin r → β) (b : β) (i j : Fin r)
    (hcard : (matchingSpan f label b).card = (f j).val + 1 - (f i).val)
    (hij : f i ≤ f j) :
    (((List.ofFn x).drop (f i).val).take (matchingSpan f label b).card).length =
      (matchingSpan f label b).card := by
  simp only [List.length_take, List.length_drop, List.length_ofFn]
  apply min_eq_left
  have hj := (f j).isLt
  change (f i).val ≤ (f j).val at hij
  omega

/-- Local charge for a visited bad block pair, using only actual contiguous
segments of the two binary words. -/
theorem block_pair_charge_of_segment_separation
    {α : Type*} {r M P : ℕ} (hP : 0 < P)
    (x y : Fin (M * P) → α)
    (f g : Fin r → Fin (M * P)) (hf : StrictMono f) (hg : StrictMono g)
    (hmatch : ∀ t, x (f t) = y (g t))
    (bad : ℕ × ℕ → Prop) (a₀ : ℕ)
    (hsep : BlockSegmentSeparation x y bad a₀)
    (b : ℕ × ℕ) (hb : bad b)
    (hvisit : ∃ t, ((f t).val / P, (g t).val / P) = b)
    (hlarge : a₀ ≤
      (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card) :
    (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card ≤
      100 * (((matchingSpan f (fun t => ((f t).val / P, (g t).val / P)) b).card -
        (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card) +
        ((matchingSpan g (fun t => ((f t).val / P, (g t).val / P)) b).card -
        (Finset.univ.filter (fun t => ((f t).val / P, (g t).val / P) = b)).card)) := by
  classical
  let label := fun t => ((f t).val / P, (g t).val / P)
  let S := Finset.univ.filter (fun t => label t = b)
  have hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i := by
    intro i j k hij hjk heq
    exact block_pair_fiber_convex P f g hf.monotone hg.monotone hij hjk heq
  obtain ⟨i, j, hi, hj, hij, hspanx, hcardx⟩ :=
    matchingSpan_exists_endpoints f hf.monotone label b hvisit
  obtain ⟨u, v, hu, hv, huv, hspany, hcardy⟩ :=
    matchingSpan_exists_endpoints g hg.monotone label b hvisit
  let sx := (matchingSpan f label b).card
  let sy := (matchingSpan g label b).card
  have hSx : S.card ≤ sx := matchingSpan_fiber_card_le f hf label hc b
  have hSy : S.card ≤ sy := matchingSpan_fiber_card_le g hg label hc b
  have hix : f i ≤ f j := hf.monotone hij
  have hiy : g u ≤ g v := hg.monotone huv
  have hSlo : ∀ t ∈ S, (f i).val ≤ (f t).val := by
    intro t ht
    have hmem := matchingSpan_contains_match f label (Finset.mem_filter.mp ht).2
    rw [hspanx] at hmem
    exact (Finset.mem_Icc.mp hmem).1
  have hShi : ∀ t ∈ S, (f t).val < (f i).val + sx := by
    intro t ht
    have hmem := matchingSpan_contains_match f label (Finset.mem_filter.mp ht).2
    rw [hspanx] at hmem
    have h := (Finset.mem_Icc.mp hmem).2
    change (f t).val ≤ (f j).val at h
    dsimp [sx]
    change (f i).val ≤ (f j).val at hix
    omega
  have hTlo : ∀ t ∈ S, (g u).val ≤ (g t).val := by
    intro t ht
    have hmem := matchingSpan_contains_match g label (Finset.mem_filter.mp ht).2
    rw [hspany] at hmem
    exact (Finset.mem_Icc.mp hmem).1
  have hThi : ∀ t ∈ S, (g t).val < (g u).val + sy := by
    intro t ht
    have hmem := matchingSpan_contains_match g label (Finset.mem_filter.mp ht).2
    rw [hspany] at hmem
    have h := (Finset.mem_Icc.mp hmem).2
    change (g t).val ≤ (g v).val at h
    dsimp [sy]
    change (g u).val ≤ (g v).val at hiy
    omega
  obtain ⟨z, hzx, hzy, hzlen⟩ := common_sublist_subset_ofFn_segments
    x y f g hf hg hmatch S (f i).val (g u).val sx sy hSlo hShi hTlo hThi
  have hlenx := ofFn_segment_length_of_span x f label b i j hcardx hix
  have hleny := ofFn_segment_length_of_span y g label b u v hcardy hiy
  have hi1 : (f i).val / P = b.1 := congrArg Prod.fst hi
  have hj1 : (f j).val / P = b.1 := congrArg Prod.fst hj
  have hu2 : (g u).val / P = b.2 := congrArg Prod.snd hu
  have hv2 : (g v).val / P = b.2 := congrArg Prod.snd hv
  have hb1 : b.1 < M := by
    rw [← hi1]
    exact (Nat.div_lt_iff_lt_mul hP).mpr (f i).isLt
  have hb2 : b.2 < M := by
    rw [← hu2]
    exact (Nat.div_lt_iff_lt_mul hP).mpr (g u).isLt
  have hlx : b.1 * P ≤ (f i).val := by simpa [hi1] using Nat.div_mul_le_self (f i).val P
  have hly : b.2 * P ≤ (g u).val := by simpa [hu2] using Nat.div_mul_le_self (g u).val P
  have hhx : (f i).val + S.card ≤ (b.1 + 1) * P := by
    have h := Nat.lt_mul_div_succ (f j).val hP
    rw [hj1, Nat.mul_comm P (b.1 + 1)] at h
    dsimp [sx] at hSx
    change (f i).val ≤ (f j).val at hix
    omega
  have hhy : (g u).val + S.card ≤ (b.2 + 1) * P := by
    have h := Nat.lt_mul_div_succ (g v).val hP
    rw [hv2, Nat.mul_comm P (b.2 + 1)] at h
    dsimp [sy] at hSy
    change (g u).val ≤ (g v).val at hiy
    omega
  have hcharge := trim_separation_charge hzx hzy (by
    intro w hwx hwy
    have hwx' : w.Sublist (((List.ofFn x).drop (f i).val).take S.card) := by
      simpa [hzlen, List.take_take, min_eq_left hSx] using hwx
    have hwy' : w.Sublist (((List.ofFn y).drop (g u).val).take S.card) := by
      simpa [hzlen, List.take_take, min_eq_left hSy] using hwy
    simpa [hzlen] using hsep b hb hb1 hb2 (f i).val (g u).val S.card
      hlx hhx hly hhy hlarge w hwx' hwy')
  simpa [hzlen, hlenx, hleny, sx, sy, S, label] using hcharge

/-- The manuscript's unequal-label estimate for an arbitrary increasing bit
matching, from concrete separation of the segments in bad block pairs. -/
theorem unequal_matches_le_of_segment_separation
    {α : Type*} {r M P : ℕ} (hP : 0 < P)
    (x y : Fin (M * P) → α)
    (f g : Fin r → Fin (M * P)) (hf : StrictMono f) (hg : StrictMono g)
    (hmatch : ∀ t, x (f t) = y (g t))
    (bad : ℕ × ℕ → Prop) [DecidablePred bad] (a₀ : ℕ)
    (hsep : BlockSegmentSeparation x y bad a₀) :
    (Finset.univ.filter (fun t => bad ((f t).val / P, (g t).val / P))).card ≤
      200 * (M * P - r) + 2 * M * a₀ := by
  apply block_pair_bad_count_le hP f g hf hg bad a₀
  intro b hb hlarge
  obtain ⟨himage, hbad⟩ := Finset.mem_filter.mp hb
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp himage
  exact block_pair_charge_of_segment_separation hP x y f g hf hg hmatch
    bad a₀ hsep b hbad ⟨t, ht⟩ hlarge

end TreeEdit.BinaryLower.Code

end OAI
