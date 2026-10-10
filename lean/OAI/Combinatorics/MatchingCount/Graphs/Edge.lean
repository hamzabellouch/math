import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Mate

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}
theorem switched_holes [Fintype V] [DecidableEq V]
    (m n : Mate V) (S T : Finset V) (hm : HasHoles m S) (hn : HasHoles n T)
    (a : V) (ha : a ∈ S) (hTa : a ∉ T) :
    ∃ b, b ≠ a ∧ b ∈ S ∆ T ∧
      HasHoles (switched m n a) (S ∆ {a, b}) ∧
      HasHoles (switched n m a) (T ∆ {a, b}) := by
  classical
  have hma : m.1 a = a := (hm a).mpr ha
  have hna : n.1 a ≠ a := fun h => hTa ((hn a).mp h)
  have ham : m.1 a ≠ n.1 a := by rw [hma]; exact Ne.symm hna
  obtain ⟨b, hba, hab, he⟩ := active_component_endpoints m n a hma hna
  have hnBoth : ∀ v, (overlay m n).Reachable a v → ¬(v ∈ S ∧ v ∈ T) := by
    intro v hv ⟨hs, ht⟩
    exact mates_ne_of_reachable m n hv ham (((hm v).mpr hs).trans ((hn v).mpr ht).symm)
  have hb : b ∈ S ∨ b ∈ T := by
    simpa only [hm b, hn b] using (he b hab).mpr (Or.inr rfl)
  refine ⟨b, hba, ?_, ?_, ?_⟩
  · simp only [Finset.mem_symmDiff]
    have := hnBoth b hab
    tauto
  · intro v
    by_cases hv : (overlay m n).Reachable a v
    · have hvEnd : (v ∈ S ∨ v ∈ T) ↔ (v = a ∨ v = b) := by
        simpa only [hm v, hn v] using he v hv
      have hnb := hnBoth v hv
      simp only [switched_apply, ite_eq_left hv, hn v, Finset.mem_symmDiff,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    · have hva : v ≠ a := by rintro rfl; exact hv .rfl
      have hvb : v ≠ b := by rintro rfl; exact hv hab
      simp [switched_apply, hv, hm v, Finset.mem_symmDiff, hva, hvb]
  · intro v
    by_cases hv : (overlay m n).Reachable a v
    · have hvEnd : (v ∈ S ∨ v ∈ T) ↔ (v = a ∨ v = b) := by
        simpa only [hm v, hn v] using he v hv
      have hnb := hnBoth v hv
      simp only [switched_apply, overlay_comm n m, ite_eq_left hv, hm v,
        Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · have hva : v ≠ a := by rintro rfl; exact hv .rfl
      have hvb : v ≠ b := by rintro rfl; exact hv hab
      simp [switched_apply, overlay_comm n m, hv, hn v, Finset.mem_symmDiff, hva, hvb]

theorem mixed_hole_partition_comparison [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (S T : Finset V)
    (a : V) (ha : a ∈ S) (hTa : a ∉ T) :
    partition w S * partition w T ≤
      ∑ b ∈ (S ∆ T).erase a,
        partition w (S ∆ {a, b}) * partition w (T ∆ {a, b}) := by
  classical
  let H := (S ∆ T).erase a
  let inputs := (matchings S) ×ˢ (matchings T)
  let Q := fun b : V => (matchings (S ∆ {a, b})) ×ˢ (matchings (T ∆ {a, b}))
  let f := fun p : Mate V × Mate V => (switched p.1 p.2 a, switched p.2 p.1 a)
  let W := fun p : Mate V × Mate V => weight w p.1 * weight w p.2
  have hi : Function.Injective f := switch_injective a
  have hd : (↑H : Set V).PairwiseDisjoint Q := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpb : HasHoles p.1 (S ∆ {a, b}) :=
      (mem_matchings p.1 _).mp (Finset.mem_product.mp hp).1
    have hpc : HasHoles p.1 (S ∆ {a, c}) :=
      (mem_matchings p.1 _).mp (Finset.mem_product.mp hq).1
    have heq : (S ∆ {a, b}) = (S ∆ {a, c}) := hasHoles_unique p.1 hpb hpc
    have habc : ({a, b} : Finset V) = {a, c} := symmDiff_right_injective S heq
    have hbm : b ∈ ({a, c} : Finset V) := by rw [← habc]; simp
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbm
    exact hbc (hbm.resolve_left hba)
  have himage : inputs.image f ⊆ H.biUnion Q := by
    intro p hp
    obtain ⟨⟨m, n⟩, hmn, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hm, hn⟩ := Finset.mem_product.mp hmn
    obtain ⟨b, hba, hb, hmb, hnb⟩ := switched_holes m n S T
      ((mem_matchings m S).mp hm) ((mem_matchings n T).mp hn) a ha hTa
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩,
      Finset.mem_product.mpr ⟨(mem_matchings _ _).mpr hmb, (mem_matchings _ _).mpr hnb⟩⟩
  calc
    partition w S * partition w T = ∑ p ∈ inputs, W p := by
      simp only [inputs, W, partition, Finset.sum_product, Finset.sum_mul_sum]
    _ = ∑ p ∈ inputs.image f, W p := by
      rw [Finset.sum_image hi.injOn]
      apply Finset.sum_congr rfl
      intro p _
      exact (switched_weight w p.1 p.2 a).symm
    _ ≤ ∑ p ∈ H.biUnion Q, W p :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun p _ _ => mul_nonneg (weight_nonneg w hw p.1) (weight_nonneg w hw p.2))
    _ = _ := by
      rw [Finset.sum_biUnion hd]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Q, W, partition, Finset.sum_product, Finset.sum_mul_sum]

noncomputable def withEdge (m : Mate V) (a b : V) : Mate V := by
  classical
  by_cases h : m.1 a = a ∧ m.1 b = b
  · refine ⟨fun v => if v = a then b else if v = b then a else m.1 v, ?_⟩
    intro v
    by_cases hva : v = a
    · subst v
      by_cases hab : a = b <;> simp [hab]
    by_cases hvb : v = b
    · subst v
      by_cases hab : a = b <;> simp [hab, hva]
    have hma : m.1 v ≠ a := by
      intro hv
      have he := congrArg m.1 hv
      rw [mate_mate, h.1] at he
      exact hva he
    have hmb : m.1 v ≠ b := by
      intro hv
      have he := congrArg m.1 hv
      rw [mate_mate, h.2] at he
      exact hvb he
    simp [hva, hvb, hma, hmb]
  · exact m

@[simp] theorem withEdge_apply (m : Mate V) (a b v : V)
    (ha : m.1 a = a) (hb : m.1 b = b) :
    (withEdge m a b).1 v = if v = a then b else if v = b then a else m.1 v := by
  classical
  simp [withEdge, ha, hb]

theorem withEdge_holes [DecidableEq V] (m : Mate V) (S : Finset V)
    (hm : HasHoles m S) (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    HasHoles (withEdge m a b) (S \ {a, b}) := by
  classical
  intro v
  rw [withEdge_apply m a b v ((hm a).mpr ha) ((hm b).mpr hb)]
  by_cases hva : v = a
  · subst v
    simp [hab, Ne.symm hab]
  by_cases hvb : v = b
  · subst v
    simp [hab, Ne.symm hab]
  simp [hva, hvb, hm v]

theorem withEdge_injOn [Fintype V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S) :
    Set.InjOn (fun m : Mate V => withEdge m a b) (matchings S) := by
  classical
  intro m hm n hn he
  have hm := (mem_matchings m S).mp hm
  have hn := (mem_matchings n S).mp hn
  apply Subtype.ext
  funext v
  by_cases hva : v = a
  · subst v
    exact ((hm a).mpr ha).trans ((hn a).mpr ha).symm
  by_cases hvb : v = b
  · subst v
    exact ((hm b).mpr hb).trans ((hn b).mpr hb).symm
  have hv := congrArg (fun p : Mate V => p.1 v) he
  simpa [withEdge_apply, (hm a).mpr ha, (hm b).mpr hb,
    (hn a).mpr ha, (hn b).mpr hb, hva, hvb] using hv

def edgeActivity [LinearOrder V] (w : V → V → ℝ) (a b : V) : ℝ :=
  if a < b then w a b else w b a

theorem edgeActivity_comm [LinearOrder V] (w : V → V → ℝ) (a b : V) :
    edgeActivity w a b = edgeActivity w b a := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [edgeActivity, h, h.not_gt]
  · rfl
  · simp [edgeActivity, h, h.not_gt]

theorem withEdge_comm (m : Mate V) (a b : V) : withEdge m a b = withEdge m b a := by
  classical
  by_cases h : m.1 a = a ∧ m.1 b = b
  · apply Subtype.ext
    funext v
    simp only [withEdge_apply, h.1, h.2]
    by_cases hv : v = a
    · subst v
      by_cases hab : a = b <;> simp [hab]
    · simp [hv]
  · have h' : ¬(m.1 b = b ∧ m.1 a = a) := by tauto
    simp [withEdge, h, h']

theorem withEdge_weight_of_lt [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (m : Mate V) (a b : V)
    (ha : m.1 a = a) (hb : m.1 b = b) (hab : a < b) :
    weight w (withEdge m a b) = w a b * weight w m := by
  classical
  have hf : ∀ v : V,
      (if v < (withEdge m a b).1 v then w v ((withEdge m a b).1 v) else 1) =
      (if v = a then w a b else 1) * (if v < m.1 v then w v (m.1 v) else 1) := by
    intro v
    by_cases hva : v = a
    · subst v
      simp [withEdge_apply, ha, hb, hab]
    by_cases hvb : v = b
    · subst v
      simp [withEdge_apply, ha, hb, hab.ne', hab.not_gt]
    simp [withEdge_apply, ha, hb, hva, hvb]
  simp only [weight, hf, Finset.prod_mul_distrib]
  simp

theorem withEdge_weight [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (m : Mate V) (a b : V)
    (ha : m.1 a = a) (hb : m.1 b = b) (hab : a ≠ b) :
    weight w (withEdge m a b) = edgeActivity w a b * weight w m := by
  rcases lt_or_gt_of_ne hab with h | h
  · simpa [edgeActivity, h] using withEdge_weight_of_lt w m a b ha hb h
  · rw [withEdge_comm, edgeActivity_comm]
    simpa [edgeActivity, h] using withEdge_weight_of_lt w m b a hb ha h

theorem edge_fill_partition [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (S : Finset V)
    (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    edgeActivity w a b * partition w S ≤ partition w (S \ {a, b}) := by
  classical
  let f := fun m : Mate V => withEdge m a b
  have hi := withEdge_injOn S a b ha hb
  have hsub : (matchings S).image f ⊆ matchings (S \ {a, b}) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    exact (mem_matchings _ _).mpr
      (withEdge_holes n S ((mem_matchings n S).mp hn) a b ha hb hab)
  calc
    edgeActivity w a b * partition w S = ∑ m ∈ matchings S, weight w (f m) := by
      rw [partition, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hh := (mem_matchings m S).mp hm
      exact (withEdge_weight w m a b ((hh a).mpr ha) ((hh b).mpr hb) hab).symm
    _ = ∑ m ∈ (matchings S).image f, weight w m := (Finset.sum_image hi).symm
    _ ≤ partition w (S \ {a, b}) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => weight_nonneg w hw m)

noncomputable def holeRatio [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (U : Finset V) : ℝ := partition w U / partition w ∅

theorem holeRatio_nonneg [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (U : Finset V) :
    0 ≤ holeRatio w U := div_nonneg (partition_nonneg w hw U) (partition_nonneg w hw ∅)

theorem holeRatio_empty [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hz : 0 < partition w ∅) : holeRatio w ∅ = 1 := div_self hz.ne'

theorem holeRatio_pair_comm [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (a b : V) : holeRatio w {a, b} = holeRatio w {b, a} := by
  rw [Finset.pair_comm]

theorem holeRatio_comparison [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (U : Finset V) (a : V) (ha : a ∈ U) :
    holeRatio w U ≤ ∑ b ∈ U.erase a, holeRatio w (U \ {a, b}) * holeRatio w {a, b} := by
  have h := hole_partition_comparison w hw U a ha
  have hzz : 0 ≤ partition w ∅ * partition w ∅ := mul_nonneg hz.le hz.le
  calc
    holeRatio w U = (partition w U * partition w ∅) / (partition w ∅ * partition w ∅) := by
      unfold holeRatio
      field_simp
    _ ≤ (∑ b ∈ U.erase a, partition w (U \ {a, b}) * partition w {a, b}) /
          (partition w ∅ * partition w ∅) := div_le_div_of_nonneg_right h hzz
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      exact mul_div_mul_comm _ _ _ _

theorem four_holes [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    holeRatio w {a, b, c, d} ≤
      holeRatio w {a, b} * holeRatio w {c, d} +
      holeRatio w {a, c} * holeRatio w {b, d} +
      holeRatio w {a, d} * holeRatio w {b, c} := by
  classical
  have h := holeRatio_comparison w hw hz {a,b,c,d} a (by simp)
  have he : ({a,b,c,d} : Finset V).erase a = {b,c,d} := by
    ext v
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    grind
  have hab' : ({a,b,c,d} : Finset V) \ {a,b} = {c,d} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  have hac' : ({a,b,c,d} : Finset V) \ {a,c} = {b,d} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  have had' : ({a,b,c,d} : Finset V) \ {a,d} = {b,c} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  rw [he, Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_insert (by simp [hcd]), Finset.sum_singleton,
    hab', hac', had'] at h
  nlinarith only [h]

theorem mixed_holeRatio_comparison [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (S T : Finset V) (a : V) (ha : a ∈ S) (hTa : a ∉ T) :
    holeRatio w S * holeRatio w T ≤
      ∑ b ∈ (S ∆ T).erase a,
        holeRatio w (S ∆ {a, b}) * holeRatio w (T ∆ {a, b}) := by
  have h := mixed_hole_partition_comparison w hw S T a ha hTa
  have hzz : 0 ≤ partition w ∅ * partition w ∅ := mul_nonneg hz.le hz.le
  calc
    holeRatio w S * holeRatio w T =
        (partition w S * partition w T) / (partition w ∅ * partition w ∅) :=
      (mul_div_mul_comm _ _ _ _).symm
    _ ≤ (∑ b ∈ (S ∆ T).erase a,
        partition w (S ∆ {a, b}) * partition w (T ∆ {a, b})) /
          (partition w ∅ * partition w ∅) := div_le_div_of_nonneg_right h hzz
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      exact mul_div_mul_comm _ _ _ _

theorem edge_fill_holeRatio [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (S : Finset V) (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    edgeActivity w a b * holeRatio w S ≤ holeRatio w (S \ {a, b}) := by
  simpa only [holeRatio, mul_div_assoc] using
    div_le_div_of_nonneg_right (edge_fill_partition w hw S a b ha hb hab) hz.le

noncomputable def rowMax [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ) (a : V) : ℝ :=
  ((Finset.univ.erase a).sup' (by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    omega) fun b => holeRatio w {a,b})

theorem holeRatio_le_rowMax [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ) (a b : V) (hab : a ≠ b) :
    holeRatio w {a,b} ≤ rowMax hcard w a := by
  exact Finset.le_sup' (fun b => holeRatio w {a,b}) (by simp [Ne.symm hab])

theorem rowMax_attained [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ) (a : V) :
    ∃ b, b ≠ a ∧ holeRatio w {a,b} = rowMax hcard w a := by
  unfold rowMax
  obtain ⟨b,hb,he⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.univ.erase a).Nonempty by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
      omega) (fun b => holeRatio w {a,b})
  exact ⟨b,(Finset.mem_erase.mp hb).1,he.symm⟩

theorem two_holes_le_four [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hr : ∀ a, rowMax hcard w a ≤ 4) (U : Finset V) (hU : U.card = 2) :
    holeRatio w U ≤ 4 := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hU
  exact (holeRatio_le_rowMax hcard w a b hab).trans (hr a)

theorem four_holes_le_fortyeight [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hr : ∀ a, rowMax hcard w a ≤ 4) (U : Finset V) (hU : U.card = 4) :
    holeRatio w U ≤ 48 := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := Finset.card_eq_four.mp hU
  have hpair : ∀ a b : V, a ≠ b → holeRatio w {a,b} ≤ 4 :=
    fun a b hab => (holeRatio_le_rowMax hcard w a b hab).trans (hr a)
  have hmul : ∀ (a b c d : V), a ≠ b → c ≠ d →
      holeRatio w {a,b} * holeRatio w {c,d} ≤ 16 := by
    intro a b c d hab hcd
    have h := mul_le_mul (hpair a b hab) (hpair c d hcd)
      (holeRatio_nonneg w hw {c,d}) (by norm_num : (0:ℝ) ≤ 4)
    norm_num at h ⊢
    exact h
  have hf := four_holes w hw hz a b c d hab hac had hbc hbd hcd
  have h1 := hmul a b c d hab hcd
  have h2 := hmul a c b d hac hbd
  have h3 := hmul a d b c had hbc
  linarith

theorem zero_or_two_holes_le_four [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ) (hz : 0 < partition w ∅)
    (hr : ∀ a, rowMax hcard w a ≤ 4) (U : Finset V)
    (hU : U.card = 0 ∨ U.card = 2) : holeRatio w U ≤ 4 := by
  rcases hU with h | h
  · have he : U = ∅ := Finset.card_eq_zero.mp h
    rw [he, holeRatio_empty w hz]
    norm_num
  · exact two_holes_le_four hcard w hr U h

theorem small_holes_le_fortyeight [Fintype V] [LinearOrder V]
    (hcard : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ v z, 0 ≤ w v z) (hz : 0 < partition w ∅)
    (hr : ∀ a, rowMax hcard w a ≤ 4) (U : Finset V)
    (hU : U.card = 0 ∨ U.card = 2 ∨ U.card = 4) : holeRatio w U ≤ 48 := by
  rcases hU with h | h | h
  · exact (zero_or_two_holes_le_four hcard w hz hr U (Or.inl h)).trans (by norm_num)
  · exact (two_holes_le_four hcard w hr U h).trans (by norm_num)
  · exact four_holes_le_fortyeight hcard w hw hz hr U h

theorem symmDiff_pair_of_mem_mem [DecidableEq V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S) : S ∆ {a,b} = S \ {a,b} := by
  ext v
  simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  grind

theorem symmDiff_pair_of_mem_notMem [DecidableEq V] (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∉ S) : S ∆ {a,b} = insert b (S.erase a) := by
  ext v
  simp only [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  grind

end MatchingFPRAS.Switching

end OAI
