import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.Combinatorics.BalancedRyser.Construction.Construction
import OAI.Combinatorics.BalancedRyser.Probability.FourCycle

namespace OAI

namespace Balanced

variable {F : Type*} [Field F]

namespace SplitGeometry

theorem adjacent_symm {M : MergedPairs F} {S : Line F} {p r : Point F}
    (h : Adjacent M S p r) : Adjacent M S r p := by
  rcases h with ⟨hp, hr, hne, d, hd, h⟩
  refine ⟨hr, hp, hne.symm, d, hd, ?_⟩
  exact h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)

theorem intersection_on_left (l m : Line F) : OnLine (lineIntersection l m) l := by
  obtain ⟨d, b⟩ := l
  obtain ⟨e, c⟩ := m
  cases d <;> cases e <;> simp [OnLine, lineIntersection, lineEval]

theorem intersection_on_right (l m : Line F) (h : l.1 ≠ m.1) :
    OnLine (lineIntersection l m) m := by
  obtain ⟨d, b⟩ := l
  obtain ⟨e, c⟩ := m
  cases d with
  | none =>
    cases e with
    | none => exact False.elim (h rfl)
    | some e => simp [OnLine, lineIntersection, lineEval]
  | some d =>
    cases e with
    | none => rfl
    | some e =>
      have hde : d ≠ e := fun he => h (congrArg some he)
      change d * ((c - b) / (d - e)) + b - e * ((c - b) / (d - e)) = c
      field_simp [sub_ne_zero.mpr hde]
      ring

variable [Fintype F] [DecidableEq F]

variable {M : MergedPairs F} {g : Direction F} {C : SplitChoice F}

theorem valid_card_designated (h : ValidChoice M g C) : (designated M C).card = 4 := by
  exact FourCycle.card_designated (tuplePoint M C.tuple) h.2.2.2.2.1

theorem valid_no_opposite (h : ValidChoice M g C) (i : Fin 4) :
    ¬ Adjacent M C.line (tuplePoint M C.tuple i)
      (tuplePoint M C.tuple (FourCycle.opposite i)) := by
  rcases h with ⟨_, _, _, _, _, _, h0, h1, _⟩
  fin_cases i
  · simpa [FourCycle.opposite] using h0
  · simpa [FourCycle.opposite] using h1
  · simpa [FourCycle.opposite] using fun ha => h0 (adjacent_symm ha)
  · simpa [FourCycle.opposite] using fun ha => h1 (adjacent_symm ha)

theorem valid_external_unique (h : ValidChoice M g C) (p : Point F)
    (hp : OnLine p C.line) (hext : p ∉ designated M C)
    (i j : Fin 4) (hi : Adjacent M C.line p (tuplePoint M C.tuple i))
    (hj : Adjacent M C.line p (tuplePoint M C.tuple j)) : i = j := by
  apply Finset.card_le_one.mp (h.2.2.2.2.2.2.2.2 p hp hext)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hj

theorem valid_exists_uncovered (h : ValidChoice M g C) (p : Point F)
    (hp : OnLine p C.line) :
    ∃ i, tuplePoint M C.tuple i ≠ p ∧ ¬ Adjacent M C.line p (tuplePoint M C.tuple i) := by
  apply FourCycle.exists_uncovered (tuplePoint M C.tuple) h.2.2.2.2.1
    (Adjacent M C.line) (valid_no_opposite h) p
  intro hext i j hi hj
  apply valid_external_unique h p hp ?_ i j hi hj
  intro hm
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
  exact hext k hk

theorem valid_not_covered (h : ValidChoice M g C) (p : Point F)
    (hp : OnLine p C.line) (Covered : Point F → Prop)
    (htrace : ∀ x ∈ designated M C, Covered x → x = p ∨ Adjacent M C.line p x) :
    ¬ ∀ x ∈ designated M C, Covered x := by
  obtain ⟨i, hne, hna⟩ := valid_exists_uncovered h p hp
  have hi : tuplePoint M C.tuple i ∈ designated M C :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  intro hall
  exact (htrace _ hi (hall _ hi)).elim hne hna

theorem valid_consecutive_adjacent (h : ValidChoice M g C) (i : Fin 4) :
    Adjacent M C.line (tuplePoint M C.tuple i) (tuplePoint M C.tuple (i + 1)) := by
  rcases h with ⟨hdir, _, hgen, havoid, hpoints, hon, _, _, _⟩
  have hnext : i ≠ i + 1 := by fin_cases i <;> decide
  have hd : (constituent M (C.tuple.generator i) (C.tuple.side i)).1 ≠
      (constituent M (C.tuple.generator (i + 1)) (!(C.tuple.side (i + 1)))).1 :=
    fun he => hnext (hgen he)
  have hi := intersection_on_right
    (constituent M (C.tuple.generator i) (C.tuple.side i))
    (constituent M (C.tuple.generator (i + 1)) (!(C.tuple.side (i + 1)))) hd
  have hj := intersection_on_left
    (constituent M (C.tuple.generator (i + 1)) (C.tuple.side (i + 1)))
    (constituent M (C.tuple.generator ((i + 1) + 1))
      (!(C.tuple.side ((i + 1) + 1))))
  change OnLine (tuplePoint M C.tuple i)
    (constituent M (C.tuple.generator (i + 1)) (!(C.tuple.side (i + 1)))) at hi
  change OnLine (tuplePoint M C.tuple (i + 1))
    (constituent M (C.tuple.generator (i + 1)) (C.tuple.side (i + 1))) at hj
  refine ⟨hon i, hon (i + 1), fun he => hnext (hpoints he),
    C.tuple.generator (i + 1), ?_, ?_⟩
  · simpa only [hdir] using havoid (i + 1)
  · cases hb : C.tuple.side (i + 1)
    · right
      simpa only [hb, Bool.not_false] using And.intro hi hj
    · left
      simpa only [hb, Bool.not_true] using And.intro hi hj

theorem adjacent_mem_merged {M : MergedPairs F} {S : Line F} {p r : Point F}
    (h : Adjacent M S p r) : ∃ d, p ∈ mergedPoints M d ∧ r ∈ mergedPoints M d := by
  rcases h with ⟨_, _, _, d, _, h⟩
  refine ⟨d, ?_⟩
  simp only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact h.elim (fun h => ⟨Or.inl h.1, Or.inr h.2⟩)
    (fun h => ⟨Or.inr h.1, Or.inl h.2⟩)

theorem valid_common_block_or_merged (h : ValidChoice M g C)
    {x y : Point F} (hx : x ∈ designated M C) (hy : y ∈ designated M C) :
    (x ∈ FourCycle.evenBlock (tuplePoint M C.tuple) ∧
      y ∈ FourCycle.evenBlock (tuplePoint M C.tuple)) ∨
    (x ∈ FourCycle.oddBlock (tuplePoint M C.tuple) ∧
      y ∈ FourCycle.oddBlock (tuplePoint M C.tuple)) ∨
    ∃ d, x ∈ mergedPoints M d ∧ y ∈ mergedPoints M d := by
  have hpair := FourCycle.common_block_or_adjacent (tuplePoint M C.tuple)
    (Adjacent M C.line) (fun _ _ => adjacent_symm)
    (valid_consecutive_adjacent h) hx hy
  exact hpair.imp_right (Or.imp_right adjacent_mem_merged)

theorem selected_designated_mem_points (C : Configuration F) (s : Slot F)
    {x : Point F} (hx : x ∈ designated C.merged (C.choice s)) : x ∈ C.points := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hx⟩

theorem selected_pair_common_block (C : Configuration F) (h : C.Valid)
    (s : Slot F) {x y : Point F}
    (hx : x ∈ designated C.merged (C.choice s))
    (hy : y ∈ designated C.merged (C.choice s)) :
    ∃ b ∈ C.blockLabels, x ∈ C.blockPoints b ∧ y ∈ C.blockPoints b := by
  classical
  rcases valid_common_block_or_merged (h.2 s) hx hy with he | ho | hm
  · refine ⟨Sum.inr (Sum.inr (s, false)), ?_, he⟩
    simp [Configuration.blockLabels, Configuration.IsBlockLabel]
  · refine ⟨Sum.inr (Sum.inr (s, true)), ?_, ho⟩
    simp [Configuration.blockLabels, Configuration.IsBlockLabel]
  · obtain ⟨d, hxM, hyM⟩ := hm
    refine ⟨Sum.inr (Sum.inl d), ?_, ?_, ?_⟩
    · simp [Configuration.blockLabels, Configuration.IsBlockLabel]
    · exact Finset.mem_inter.mpr ⟨hxM, selected_designated_mem_points C s hx⟩
    · exact Finset.mem_inter.mpr ⟨hyM, selected_designated_mem_points C s hy⟩

end SplitGeometry
end Balanced

end OAI
