import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Construction.Construction

namespace OAI

namespace Balanced.Configuration.BlockPartitions

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {C : Configuration F}

omit [Fintype F] [DecidableEq F] in

theorem line_eq_of_direction_eq {p : Point F} {l m : Line F}
    (hl : OnLine p l) (hm : OnLine p m) (hd : l.1 = m.1) : l = m := by
  apply Prod.ext hd
  exact hl.symm.trans ((congrArg (fun d => lineEval d p) hd).trans hm)

theorem split_direction (hV : C.Valid) (s : Slot F) : (C.choice s).line.1 = s.1 :=
  (hV.2 s).1

theorem split_not_constituent (hV : C.Valid) (s : Slot F) :
    (C.choice s).line ∉ constituentLines C.merged := (hV.2 s).2.1

theorem tuple_injective (hV : C.Valid) (s : Slot F) :
    Function.Injective (tuplePoint C.merged (C.choice s).tuple) :=
  (hV.2 s).2.2.2.2.1

theorem tuple_on_split (hV : C.Valid) (s : Slot F) (i : Fin 4) :
    OnLine (tuplePoint C.merged (C.choice s).tuple i) (C.choice s).line :=
  (hV.2 s).2.2.2.2.2.1 i

theorem point_on_split_designated (hC : C.Compatible) {p : Point F}
    (hp : p ∈ C.points) (s : Slot F) (hs : OnLine p (C.choice s).line) :
    p ∈ designated C.merged (C.choice s) := by
  classical
  rcases Finset.mem_union.mp hp with hp | hp
  · have hr := (Finset.mem_filter.mp hp).2
    exact (hr _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩) hs).elim
  · rcases Finset.mem_biUnion.mp hp with ⟨t, ht, hp⟩
    by_cases hst : s = t
    · simpa [hst] using hp
    · exact (hC.1 s t hst p hp hs).elim

theorem split_line_injective (hV : C.Valid) (hC : C.Compatible) :
    Function.Injective (fun s => (C.choice s).line) := by
  intro s t hst
  by_contra hne
  apply hC.1 s t hne (tuplePoint C.merged (C.choice t).tuple 0)
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · change (C.choice s).line = (C.choice t).line at hst
    rw [hst]
    exact tuple_on_split hV t 0

theorem split_block_onLine (hV : C.Valid) {p : Point F} (s : Slot F) (b : Bool)
    (hp : p ∈ C.blockPoints (Sum.inr (Sum.inr (s, b)))) :
    OnLine p (C.choice s).line := by
  cases b <;> simp only [blockPoints, Finset.mem_insert, Finset.mem_singleton] at hp
  all_goals rcases hp with rfl | rfl
  all_goals exact tuple_on_split hV _ _

theorem split_block_side_unique (hV : C.Valid) {p : Point F}
    (s : Slot F) (b c : Bool)
    (hb : p ∈ C.blockPoints (Sum.inr (Sum.inr (s, b))))
    (hc : p ∈ C.blockPoints (Sum.inr (Sum.inr (s, c)))) : b = c := by
  cases b <;> cases c
  · rfl
  · simp only [blockPoints, Finset.mem_insert, Finset.mem_singleton] at hb hc
    rcases hb with hb | hb <;> rcases hc with hc | hc
    all_goals have h := tuple_injective hV s (hb.symm.trans hc)
    all_goals have hv := congrArg Fin.val h
    all_goals norm_num at hv
  · simp only [blockPoints, Finset.mem_insert, Finset.mem_singleton] at hb hc
    rcases hb with hb | hb <;> rcases hc with hc | hc
    all_goals have h := tuple_injective hV s (hb.symm.trans hc)
    all_goals have hv := congrArg Fin.val h
    all_goals norm_num at hv
  · rfl

omit [Field F] in
theorem constituent_mem (d : Direction F) (b : Bool) :
    constituent C.merged d b ∈ constituentLines C.merged := by
  exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, rfl⟩

theorem regular_block_onLine {p : Point F} {l : Line F}
    (hp : p ∈ C.blockPoints (Sum.inl l)) : OnLine p l :=
  (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).2

theorem merged_block_onLine {p : Point F} {d : Direction F}
    (hp : p ∈ C.blockPoints (Sum.inr (Sum.inl d))) :
    ∃ b, OnLine p (constituent C.merged d b) := by
  rcases Finset.mem_union.mp (Finset.mem_inter.mp hp).1 with h | h
  · exact ⟨false, (Finset.mem_filter.mp h).2⟩
  · exact ⟨true, (Finset.mem_filter.mp h).2⟩

theorem regular_split_disjoint (hV : C.Valid) {p : Point F} {l : Line F}
    (hl : C.IsBlockLabel (Sum.inl l)) (s : Slot F) (b : Bool)
    (hd : l.1 = s.1)
    (hp : p ∈ C.blockPoints (Sum.inl l))
    (hs : p ∈ C.blockPoints (Sum.inr (Sum.inr (s, b)))) : False := by
  have heq := line_eq_of_direction_eq (regular_block_onLine hp)
    (split_block_onLine hV s b hs) (hd.trans (split_direction hV s).symm)
  apply hl
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, heq.symm⟩)

theorem regular_merged_disjoint {p : Point F} {l : Line F}
    (hl : C.IsBlockLabel (Sum.inl l)) (d : Direction F)
    (hd : l.1 = d)
    (hp : p ∈ C.blockPoints (Sum.inl l))
    (hm : p ∈ C.blockPoints (Sum.inr (Sum.inl d))) : False := by
  obtain ⟨b, hb⟩ := merged_block_onLine hm
  have heq := line_eq_of_direction_eq (regular_block_onLine hp) hb hd
  apply hl
  apply Finset.mem_union_right
  rw [heq]
  exact constituent_mem d b

theorem merged_split_disjoint (hV : C.Valid) {p : Point F}
    (d : Direction F) (s : Slot F) (b : Bool) (hd : d = s.1)
    (hm : p ∈ C.blockPoints (Sum.inr (Sum.inl d)))
    (hs : p ∈ C.blockPoints (Sum.inr (Sum.inr (s, b)))) : False := by
  obtain ⟨c, hc⟩ := merged_block_onLine hm
  have heq := line_eq_of_direction_eq hc (split_block_onLine hV s b hs)
    (hd.trans (split_direction hV s).symm)
  apply split_not_constituent hV s
  rw [← heq]
  exact constituent_mem d c

theorem block_unique (hV : C.Valid) (hC : C.Compatible)
    {p : Point F} {d : Direction F} {b c : BlockLabel F}
    (hb : b ∈ C.labelsInDirection d) (hc : c ∈ C.labelsInDirection d)
    (hpb : p ∈ C.blockPoints b) (hpc : p ∈ C.blockPoints c) : b = c := by
  classical
  simp only [labelsInDirection, blockLabels, Finset.mem_filter,
    Finset.mem_univ, true_and] at hb hc
  have hdir := hb.2.trans hc.2.symm
  rcases b with l | (g | ⟨s, u⟩) <;> rcases c with m | (h | ⟨t, v⟩)
  · exact congrArg Sum.inl (line_eq_of_direction_eq
      (regular_block_onLine hpb) (regular_block_onLine hpc) hdir)
  · exact (regular_merged_disjoint hb.1 h hdir hpb hpc).elim
  · exact (regular_split_disjoint hV hb.1 t v hdir hpb hpc).elim
  · exact (regular_merged_disjoint hc.1 g hdir.symm hpc hpb).elim
  · exact congrArg (fun g => Sum.inr (Sum.inl g)) hdir
  · exact (merged_split_disjoint hV g t v hdir hpb hpc).elim
  · exact (regular_split_disjoint hV hc.1 s u hdir.symm hpc hpb).elim
  · exact (merged_split_disjoint hV h s u hdir.symm hpc hpb).elim
  · have hline := line_eq_of_direction_eq (split_block_onLine hV s u hpb)
      (split_block_onLine hV t v hpc)
      ((split_direction hV s).trans (hdir.trans (split_direction hV t).symm))
    have hst := split_line_injective hV hC hline
    subst t
    have huv := split_block_side_unique hV s u v hpb hpc
    rw [huv]

theorem block_exists (hV : C.Valid) (hC : C.Compatible)
    {p : Point F} (hp : p ∈ C.points) (d : Direction F) :
    ∃ b ∈ C.labelsInDirection d, p ∈ C.blockPoints b := by
  classical
  let l := lineThrough d p
  have hl : OnLine p l := rfl
  have hld : l.1 = d := rfl
  by_cases hs : l ∈ C.splitLines
  · rcases Finset.mem_image.mp hs with ⟨s, _, hsl⟩
    have hd : s.1 = d := (split_direction hV s).symm.trans
      ((congrArg Prod.fst hsl).trans hld)
    have hps : OnLine p (C.choice s).line := by rw [hsl]; exact hl
    have hdes := point_on_split_designated hC hp s hps
    rcases Finset.mem_image.mp hdes with ⟨i, _, hi⟩
    refine ⟨Sum.inr (Sum.inr (s, decide (i.val % 2 = 1))), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩, hd⟩
    · fin_cases i <;> simp [blockPoints, ← hi]
  · by_cases hm : l ∈ constituentLines C.merged
    · rcases Finset.mem_image.mp hm with ⟨⟨g, b⟩, _, hgl⟩
      have hgd : g = d := (congrArg Prod.fst hgl).trans hld
      refine ⟨Sum.inr (Sum.inl d), ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩, rfl⟩
      · apply Finset.mem_inter.mpr
        refine ⟨?_, hp⟩
        have hconst : OnLine p (constituent C.merged d b) := by
          rw [← hgd, hgl]
          exact hl
        have hmem : p ∈ linePoints (constituent C.merged d b) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconst⟩
        cases b
        · exact Finset.mem_union_left _ hmem
        · exact Finset.mem_union_right _ hmem
    · refine ⟨Sum.inl l, ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, fun hmem => (Finset.mem_union.mp hmem).elim hs hm⟩, hld⟩
      · exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, hp⟩

theorem existsUnique_block (hV : C.Valid) (hC : C.Compatible)
    {p : Point F} (hp : p ∈ C.points) (d : Direction F) :
    ∃! b, b ∈ C.labelsInDirection d ∧ p ∈ C.blockPoints b := by
  obtain ⟨b, hb, hpb⟩ := block_exists hV hC hp d
  refine ⟨b, ⟨hb, hpb⟩, ?_⟩
  intro c hc
  exact block_unique hV hC hc.1 hb hc.2 hpb

noncomputable def pointLabel (hV : C.Valid) (hC : C.Compatible)
    (d : Direction F) (p : {p // p ∈ C.points}) :
    {b // b ∈ C.labelsInDirection d} :=
  ⟨Classical.choose (block_exists hV hC p.property d),
    (Classical.choose_spec (block_exists hV hC p.property d)).1⟩

theorem pointLabel_mem (hV : C.Valid) (hC : C.Compatible)
    (d : Direction F) (p : {p // p ∈ C.points}) :
    p.val ∈ C.blockPoints (pointLabel hV hC d p).val :=
  (Classical.choose_spec (block_exists hV hC p.property d)).2

theorem pointLabel_eq_iff (hV : C.Valid) (hC : C.Compatible)
    (d : Direction F) (p : {p // p ∈ C.points})
    (b : {b // b ∈ C.labelsInDirection d}) :
    pointLabel hV hC d p = b ↔ p.val ∈ C.blockPoints b.val := by
  constructor
  · intro h
    rw [← h]
    exact pointLabel_mem hV hC d p
  · intro h
    apply Subtype.ext
    exact block_unique hV hC (pointLabel hV hC d p).property b.property
      (pointLabel_mem hV hC d p) h

end Balanced.Configuration.BlockPartitions

end OAI
