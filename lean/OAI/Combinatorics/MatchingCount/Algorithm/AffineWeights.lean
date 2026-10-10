import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.PathStrength

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}
theorem erasePair_weight_of_lt [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (m : Mate V) (a b : V) (h : m.1 a = b) (hab : a < b) :
    weight w (erasePair m a b) =
      ∏ v ∈ Finset.univ.erase a, if v < m.1 v then w v (m.1 v) else 1 := by
  have hba : m.1 b = a := by rw [← h, mate_mate]
  unfold weight
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  simp only [erasePair_apply m a b a h, true_or, ite_true, lt_self_iff_false, ite_false,
    mul_one]
  apply Finset.prod_congr rfl
  intro v hv
  have hva := (Finset.mem_erase.mp hv).1
  by_cases hvb : v = b
  · subst v
    simp [hba, erasePair_apply, h, hab.not_gt]
  · simp [erasePair_apply, h, hva, hvb]

theorem sum_erased_weights [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (S : Finset V) (a b : V)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) :
    ∑ m ∈ (matchings S).filter (fun m => m.1 a = b), weight w (erasePair m a b) =
      partition w (insert a (insert b S)) := by
  let A := (matchings S).filter (fun m => m.1 a = b)
  let f := fun m : Mate V => erasePair m a b
  have hi : Set.InjOn f A := by
    intro m hm n hn he
    have hm' := (Finset.mem_filter.mp hm).2
    have hn' := (Finset.mem_filter.mp hn).2
    have h := congrArg (fun p => withEdge p a b) he
    simpa [f, withEdge_erasePair, hm', hn'] using h
  have himg : A.image f = matchings (insert a (insert b S)) := by
    ext m
    constructor
    · intro hm
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨hnS,hnab⟩ := Finset.mem_filter.mp hn
      exact (mem_matchings _ _).mpr
        (erasePair_holes n S ((mem_matchings n S).mp hnS) a b hnab)
    · intro hm
      have hholes := (mem_matchings m (insert a (insert b S))).mp hm
      have hma : m.1 a = a := (hholes a).mpr (by simp)
      have hmb : m.1 b = b := (hholes b).mpr (by simp)
      refine Finset.mem_image.mpr ⟨withEdge m a b, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply (mem_matchings _ _).mpr
          have hh := withEdge_holes m (insert a (insert b S)) hholes a b
            (by simp) (by simp) hab
          have he : insert a (insert b S) \ {a,b} = S := by
            ext v
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            grind
          rwa [he] at hh
        · simp [hma,hmb]
      · exact erasePair_withEdge m a b hma hmb
  change ∑ m ∈ A, weight w (f m) = _
  rw [← Finset.sum_image hi, himg]
  rfl

def affineWeights (w d : V → V → ℝ) (t : ℝ) (a b : V) : ℝ := w a b + t * d a b

theorem weight_hasDerivAt [Fintype V] [LinearOrder V]
    (w d : V → V → ℝ) (m : Mate V) (t : ℝ) :
    HasDerivAt (fun s => weight (affineWeights w d s) m)
      (∑ a, if a < m.1 a then d a (m.1 a) *
        weight (affineWeights w d t) (erasePair m a (m.1 a)) else 0) t := by
  have hf : ∀ a ∈ (Finset.univ : Finset V),
      HasDerivAt (fun s => if a < m.1 a then affineWeights w d s a (m.1 a) else 1)
        (if a < m.1 a then d a (m.1 a) else 0) t := by
    intro a _
    by_cases ha : a < m.1 a
    · simp only [ha, ite_true, affineWeights]
      exact (hasDerivAt_mul_const (x := t) (d a (m.1 a))).const_add (w a (m.1 a))
    · simp only [ha, ite_false]
      exact hasDerivAt_const t 1
  have hh := HasDerivAt.fun_finsetProd hf
  apply hh.congr_deriv
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a < m.1 a
  · simp only [ha, ite_true, smul_eq_mul]
    rw [erasePair_weight_of_lt _ m a (m.1 a) rfl ha]
    ring
  · simp [ha]

theorem mate_endpoints_not_holes [DecidableEq V] (m : Mate V) (S : Finset V)
    (hm : HasHoles m S) (a b : V) (h : m.1 a = b) (hab : a ≠ b) :
    a ∉ S ∧ b ∉ S := by
  constructor
  · intro ha
    exact hab (((hm a).mpr ha).symm.trans h)
  · intro hb
    have hba : m.1 b = a := by rw [← h, mate_mate]
    exact hab (hba.symm.trans ((hm b).mpr hb))

noncomputable def edgeSum [Fintype V] [LinearOrder V]
    (S : Finset V) (f : V → V → ℝ) : ℝ :=
  ∑ a, ∑ b, if a < b ∧ a ∉ S ∧ b ∉ S then f a b else 0

theorem partition_hasDerivAt [Fintype V] [LinearOrder V]
    (w d : V → V → ℝ) (S : Finset V) (t : ℝ) :
    HasDerivAt (fun s => partition (affineWeights w d s) S)
      (edgeSum S (fun a b => d a b *
        partition (affineWeights w d t) (insert a (insert b S)))) t := by
  have hh := HasDerivAt.fun_sum (fun m (_ : m ∈ matchings S) => weight_hasDerivAt w d m t)
  change HasDerivAt (fun s => partition (affineWeights w d s) S) _ t at hh
  convert hh using 1
  unfold edgeSum
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_fiberwise (matchings S) (fun m => m.1 a)
    (fun m => if a < m.1 a then d a (m.1 a) *
      weight (affineWeights w d t) (erasePair m a (m.1 a)) else 0)]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a < b
  · by_cases hS : a ∉ S ∧ b ∉ S
    · simp only [hab, hS.1, hS.2, and_self]
      rw [← sum_erased_weights (affineWeights w d t) S a b hS.1 hS.2 hab.ne,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have he := (Finset.mem_filter.mp hm).2
      simp [he,hab]
    · have hempty : (matchings S).filter (fun m => m.1 a = b) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro m hm
        obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
        exact hS (mate_endpoints_not_holes m S ((mem_matchings m S).mp hm) a b he hab.ne)
      simp [hS,hempty]
  · simp only [hab, false_and, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro m hm
    have he := (Finset.mem_filter.mp hm).2
    simp [he,hab]

theorem weight_mono [Fintype V] [LinearOrder V] (w u : V → V → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hwu : ∀ a b, w a b ≤ u a b) (m : Mate V) :
    weight w m ≤ weight u m := by
  apply Finset.prod_le_prod₀
  · intro a _
    split_ifs
    · exact hw a (m.1 a)
    · norm_num
  · intro a _
    split_ifs
    · exact hwu a (m.1 a)
    · rfl

theorem partition_mono [Fintype V] [LinearOrder V] (w u : V → V → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hwu : ∀ a b, w a b ≤ u a b) (S : Finset V) :
    partition w S ≤ partition u S :=
  Finset.sum_le_sum (fun m _ => weight_mono w u hw hwu m)

theorem edgeSum_div [Fintype V] [LinearOrder V] (S : Finset V)
    (f : V → V → ℝ) (c : ℝ) :
    edgeSum S (fun a b => f a b / c) = edgeSum S f / c := by
  simp only [edgeSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

theorem edgeSum_nonneg [Fintype V] [LinearOrder V] (S : Finset V)
    (f : V → V → ℝ) (hf : ∀ a b, a < b → a ∉ S → b ∉ S → 0 ≤ f a b) :
    0 ≤ edgeSum S f := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split_ifs with h
  · exact hf a b h.1 h.2.1 h.2.2
  · rfl

theorem holeRatio_hasDerivAt [Fintype V] [LinearOrder V]
    (w d : V → V → ℝ) (S : Finset V) (t : ℝ)
    (hz : partition (affineWeights w d t) ∅ ≠ 0) :
    HasDerivAt (fun s => holeRatio (affineWeights w d s) S)
      (edgeSum S (fun a b => d a b *
          holeRatio (affineWeights w d t) (insert a (insert b S))) -
        holeRatio (affineWeights w d t) S *
          edgeSum ∅ (fun a b => d a b * holeRatio (affineWeights w d t) {a,b})) t := by
  have hh := (partition_hasDerivAt w d S t).div (partition_hasDerivAt w d ∅ t) hz
  apply hh.congr_deriv
  simp only [holeRatio, ← mul_div_assoc, edgeSum_div, Finset.insert_empty]
  field_simp

theorem affine_partition_pos [Fintype V] [LinearOrder V]
    (w d : V → V → ℝ) (hw : ∀ a b, 0 ≤ w a b) (hd : ∀ a b, 0 ≤ d a b)
    (hz : 0 < partition w ∅) (t : ℝ) (ht : 0 ≤ t) :
    0 < partition (affineWeights w d t) ∅ := by
  apply hz.trans_le (partition_mono w _ hw _ ∅)
  intro a b
  exact le_add_of_nonneg_right (mul_nonneg ht (hd a b))

theorem finite_family_barrier {I : Type*} [Fintype I]
    (f f' : I → ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hf : ∀ i, ContinuousOn (f i) (Set.Icc 0 1))
    (hinit : ∀ i, f i 0 ≤ 1)
    (hderiv : ∀ t ∈ Set.Ioo 0 1, (∀ i, f i t < 2) →
      ∀ i, HasDerivAt (f i) (f' i t) t ∧ f' i t ≤ c) :
    ∀ t ∈ Set.Icc 0 1, ∀ i, f i t < 2 := by
  classical
  let S : Set ℝ := {t | t ∈ Set.Icc 0 1 ∧ ∃ i, 2 ≤ f i t}
  have hsclosed : IsClosed S := by
    have he : S = ⋃ i, {t | t ∈ Set.Icc 0 1 ∧ 2 ≤ f i t} := by
      ext t
      simp only [S, Set.mem_ofPred_eq, Set.mem_iUnion]
      aesop
    rw [he]
    apply isClosed_iUnion_of_finite
    intro i
    exact (hf i).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  by_contra hfail
  push Not at hfail
  obtain ⟨t,ht,i,hi⟩ := hfail
  obtain ⟨x,hx,hxmin⟩ := (isCompact_Icc.of_isClosed_subset hsclosed
    (show S ⊆ Set.Icc (0:ℝ) 1 from fun _ h => h.1)).exists_isLeast ⟨t,ht,i,hi⟩
  obtain ⟨j,hj⟩ := hx.2
  have hxpos : 0 < x := by
    have := hinit j
    rcases hx.1.1.eq_or_lt with h | h
    · rw [← h] at hj
      linarith
    · exact h
  have hbefore : ∀ y ∈ Set.Ioo 0 x, ∀ k, f k y < 2 := by
    intro y hy k
    by_contra h
    have hym : y ∈ S := ⟨⟨hy.1.le,hy.2.le.trans hx.1.2⟩,k,le_of_not_gt h⟩
    exact (not_le_of_gt hy.2) (hxmin hym)
  have hdiff : ∀ y ∈ Set.Ioo 0 x, HasDerivAt (f j) (f' j y) y := by
    intro y hy
    exact (hderiv y ⟨hy.1,hy.2.trans_le hx.1.2⟩ (hbefore y hy) j).1
  obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope (f j) (f' j) hxpos
    ((hf j).mono (Set.Icc_subset_Icc_right hx.1.2)) hdiff
  have hbound := (hderiv y ⟨hy.1,hy.2.trans_le hx.1.2⟩ (hbefore y hy) j).2
  rw [he, sub_zero] at hbound
  have hbound' := (div_le_iff₀ hxpos).mp hbound
  have hcx := mul_le_of_le_one_right hc hx.1.2
  have := hinit j
  linarith

noncomputable def holeScale (V : Type*) [Fintype V] : ℝ :=
  100000000 * ((Fintype.card V : ℝ) + 1)^4

theorem holeScale_pos [Fintype V] : 0 < holeScale V := by
  unfold holeScale
  positivity

noncomputable def holeAugmentation [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) : ℝ := bottleneck w a b / holeScale V

theorem holeAugmentation_nonneg [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) : 0 ≤ holeAugmentation w a b :=
  div_nonneg (le_trans (by norm_num) (one_le_bottleneck w a b)) holeScale_pos.le

theorem edgeSum_le_card_sq [Fintype V] [LinearOrder V] (S : Finset V)
    (f : V → V → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ a b, a < b → a ∉ S → b ∉ S → f a b ≤ c) :
    edgeSum S f ≤ (Fintype.card V : ℝ)^2 * c := by
  calc
    _ ≤ ∑ _a : V, ∑ _b : V, c := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      split_ifs with h
      · exact hf a b h.1 h.2.1 h.2.2
      · exact hc
    _ = _ := by simp; ring

theorem augmented_hole_summand [Fintype V] [LinearOrder V]
    (hn : 2 ≤ Fintype.card V) (w u : V → V → ℝ)
    (hu : ∀ a b, 0 ≤ u a b) (hz : 0 < partition u ∅)
    (hwu : ∀ a b, w a b ≤ u a b)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hn u a) (hrhi : ∀ a, rowMax hn u a ≤ 4)
    (S : Finset V) (hS : S.card = 0 ∨ S.card = 2)
    (a b : V) (hab : a < b) (ha : a ∉ S) (hb : b ∉ S) :
    holeAugmentation w a b * holeRatio u (insert a (insert b S)) ≤
      100000 * Fintype.card V / holeScale V := by
  have hcard : (insert a (insert b S)).card = 2 ∨
      (insert a (insert b S)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [ha,hab.ne]),
      Finset.card_insert_of_notMem hb]
    omega
  have h := hole_relocation hn w u hu hz hwu hrlo hrhi
    (insert a (insert b S)) hcard a b (by simp) (by simp) hab.ne
  have hB : 0 < bottleneck w a b := lt_of_lt_of_le (by norm_num) (one_le_bottleneck w a b)
  have hmul : bottleneck w a b * holeRatio u (insert a (insert b S)) ≤
      100000 * Fintype.card V := by
    have hh := (le_div_iff₀ hB).mp h
    simpa only [mul_comm] using hh
  unfold holeAugmentation
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hmul holeScale_pos.le

theorem augmented_hole_rate_le [Fintype V] [LinearOrder V]
    (hn : 2 ≤ Fintype.card V) (w u : V → V → ℝ)
    (hu : ∀ a b, 0 ≤ u a b) (hz : 0 < partition u ∅)
    (hwu : ∀ a b, w a b ≤ u a b)
    (hrlo : ∀ a, (1:ℝ)/8 ≤ rowMax hn u a) (hrhi : ∀ a, rowMax hn u a ≤ 4)
    (S : Finset V) (hS : S.card = 0 ∨ S.card = 2) :
    edgeSum S (fun a b => holeAugmentation w a b *
      holeRatio u (insert a (insert b S))) ≤ (1:ℝ)/1000 := by
  have hsum := edgeSum_le_card_sq S _ _
    (show 0 ≤ 100000 * (Fintype.card V : ℝ) / holeScale V by
      exact div_nonneg (by positivity) holeScale_pos.le)
    (augmented_hole_summand hn w u hu hz hwu hrlo hrhi S hS)
  apply hsum.trans
  rw [← mul_div_assoc, div_le_iff₀ holeScale_pos]
  have hnon : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hp : (Fintype.card V : ℝ)^3 ≤ ((Fintype.card V : ℝ)+1)^4 := by
    calc
      _ ≤ ((Fintype.card V : ℝ)+1)^3 := pow_le_pow_left₀ hnon (by linarith) 3
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  unfold holeScale
  nlinarith only [hp]

theorem row_lower_of_partition_inflation [Fintype V] [LinearOrder V]
    (hn : 2 ≤ Fintype.card V) (w u : V → V → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hz : 0 < partition w ∅) (huZ : 0 < partition u ∅)
    (hwu : ∀ a b, w a b ≤ u a b) (hinfl : partition u ∅ ≤ 2 * partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/4 ≤ rowMax hn w a) :
    ∀ a, (1:ℝ)/8 ≤ rowMax hn u a := by
  intro a
  obtain ⟨b,hba,hb⟩ := rowMax_attained hn w a
  apply le_trans _ (holeRatio_le_rowMax hn u a b hba.symm)
  have hg0 : (1:ℝ)/4 ≤ holeRatio w {a,b} := by rw [hb]; exact hrlo a
  have hnum := partition_mono w u hw hwu {a,b}
  rw [holeRatio, le_div_iff₀ hz] at hg0
  rw [holeRatio, le_div_iff₀ huZ]
  linarith

theorem normalized_partition_hasDerivAt [Fintype V] [LinearOrder V]
    (w d : V → V → ℝ) (t : ℝ) (hz0 : partition w ∅ ≠ 0)
    (hzt : partition (affineWeights w d t) ∅ ≠ 0) :
    HasDerivAt (fun s => partition (affineWeights w d s) ∅ / partition w ∅)
      ((edgeSum ∅ (fun a b => d a b * holeRatio (affineWeights w d t) {a,b})) *
        (partition (affineWeights w d t) ∅ / partition w ∅)) t := by
  have hh := (partition_hasDerivAt w d ∅ t).div_const (partition w ∅)
  apply hh.congr_deriv
  simp only [holeRatio, ← mul_div_assoc, edgeSum_div, Finset.insert_empty]
  field_simp

theorem logical_inflation [Fintype V] [LinearOrder V]
    (hn : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/4 ≤ rowMax hn w a) (hrhi : ∀ a, rowMax hn w a ≤ 1) :
    partition (affineWeights w (holeAugmentation w) 1) ∅ < 2 * partition w ∅ := by
  let d := holeAugmentation w
  let u := affineWeights w d
  have hd : ∀ a b, 0 ≤ d a b := holeAugmentation_nonneg w
  have hwu : ∀ t, 0 ≤ t → ∀ a b, w a b ≤ u t a b := by
    intro t ht a b
    exact le_add_of_nonneg_right (mul_nonneg ht (hd a b))
  have hun : ∀ t, 0 ≤ t → ∀ a b, 0 ≤ u t a b := by
    intro t ht a b
    exact (hw a b).trans (hwu t ht a b)
  have huz : ∀ t, 0 ≤ t → 0 < partition (u t) ∅ := by
    intro t ht
    exact affine_partition_pos w d hw hd hz t ht
  let I := Option {p : V × V // p.1 ≠ p.2}
  let f : I → ℝ → ℝ := fun i t => match i with
    | none => partition (u t) ∅ / partition w ∅
    | some p => holeRatio (u t) {p.1.1,p.1.2}
  have hf : ∀ i, ContinuousOn (f i) (Set.Icc 0 1) := by
    intro i t ht
    cases i with
    | none =>
      exact ((partition_hasDerivAt w d ∅ t).div_const (partition w ∅)).continuousAt.continuousWithinAt
    | some p =>
      exact (holeRatio_hasDerivAt w d _ t (huz t ht.1).ne').continuousAt.continuousWithinAt
  have hinit : ∀ i, f i 0 ≤ 1 := by
    intro i
    cases i with
    | none =>
      change partition (u 0) ∅ / partition w ∅ ≤ 1
      have he : u 0 = w := by funext a b; simp [u,affineWeights]
      rw [he,div_self hz.ne']
    | some p =>
      change holeRatio (u 0) {p.1.1,p.1.2} ≤ 1
      have he : u 0 = w := by funext a b; simp [u,affineWeights]
      rw [he]
      exact (holeRatio_le_rowMax hn w p.1.1 p.1.2 p.2).trans (hrhi p.1.1)
  have hderiv : ∀ t ∈ Set.Ioo 0 1, (∀ i, f i t < 2) →
      ∀ i, HasDerivAt (f i) (deriv (f i) t) t ∧ deriv (f i) t ≤ (1:ℝ)/500 := by
    intro t ht hstay
    have hZ : partition (u t) ∅ < 2 * partition w ∅ :=
      (div_lt_iff₀ hz).mp (hstay none)
    have hl := row_lower_of_partition_inflation hn w (u t) hw hz (huz t ht.1.le)
      (hwu t ht.1.le) hZ.le hrlo
    have hh : ∀ a, rowMax hn (u t) a ≤ 4 := by
      intro a
      obtain ⟨b,hba,hb⟩ := rowMax_attained hn (u t) a
      have hh := hstay (some ⟨(a,b),hba.symm⟩)
      change holeRatio (u t) {a,b} < 2 at hh
      rw [hb] at hh
      linarith
    let rate := edgeSum ∅ (fun a b => d a b * holeRatio (u t) {a,b})
    have hrate0 : 0 ≤ rate := edgeSum_nonneg ∅ _ (fun a b _ _ _ =>
      mul_nonneg (hd a b) (holeRatio_nonneg (u t) (hun t ht.1.le) {a,b}))
    have hrate : rate ≤ (1:ℝ)/1000 := by
      simpa only [Finset.insert_empty] using
        augmented_hole_rate_le hn w (u t) (hun t ht.1.le) (huz t ht.1.le)
          (hwu t ht.1.le) hl hh ∅ (Or.inl rfl)
    intro i
    cases i with
    | none =>
      have hdf := normalized_partition_hasDerivAt w d t hz.ne' (huz t ht.1.le).ne'
      change HasDerivAt (f none) (rate * f none t) t at hdf
      refine ⟨hdf.differentiableAt.hasDerivAt, ?_⟩
      rw [hdf.deriv]
      have hle : rate * f none t ≤ rate * 2 := mul_le_mul_of_nonneg_left (hstay none).le hrate0
      linarith
    | some p =>
      have hdf := holeRatio_hasDerivAt w d {p.1.1,p.1.2} t (huz t ht.1.le).ne'
      change HasDerivAt (f (some p)) _ t at hdf
      refine ⟨hdf.differentiableAt.hasDerivAt, ?_⟩
      rw [hdf.deriv]
      have hpcard : ({p.1.1,p.1.2} : Finset V).card = 2 := by simp [p.2]
      have hnum := augmented_hole_rate_le hn w (u t) (hun t ht.1.le) (huz t ht.1.le)
        (hwu t ht.1.le) hl hh {p.1.1,p.1.2} (Or.inr hpcard)
      have hg := holeRatio_nonneg (u t) (hun t ht.1.le) {p.1.1,p.1.2}
      have hprod := mul_nonneg hg hrate0
      change 0 ≤ holeRatio (u t) {p.1.1,p.1.2} * rate at hprod
      change edgeSum {p.1.1,p.1.2} (fun a b => d a b *
        holeRatio (u t) (insert a (insert b {p.1.1,p.1.2}))) -
        holeRatio (u t) {p.1.1,p.1.2} * rate ≤ (1:ℝ)/500
      change edgeSum {p.1.1,p.1.2} (fun a b => d a b *
        holeRatio (u t) (insert a (insert b {p.1.1,p.1.2}))) ≤ (1:ℝ)/1000 at hnum
      linarith
  have hstay := finite_family_barrier f (fun i => deriv (f i)) ((1:ℝ)/500)
    (by norm_num) (by norm_num) hf hinit hderiv 1 (by constructor <;> norm_num) none
  exact (div_lt_iff₀ hz).mp hstay

end MatchingFPRAS.Switching

end OAI
