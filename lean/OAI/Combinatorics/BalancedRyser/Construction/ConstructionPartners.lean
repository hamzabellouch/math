import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Construction.ConstructionStructure
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Probability.ConfigurationStructure

namespace OAI

namespace Balanced.ConstructionPartners

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

private theorem designated_on_line (hV : C.Valid) (s : Slot F)
    {x : Point F} (hx : x ∈ designated C.merged (C.choice s)) :
    OnLine x (C.choice s).line := by
  rcases hV.2 s with ⟨_, _, _, _, _, hon, _⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact hon i

theorem partner_adjacent (hV : C.Valid) (s : Slot F) (p x : Point F)
    (hp : OnLine p (C.choice s).line)
    (hpnot : p ∉ designated C.merged (C.choice s))
    (hx : x ∈ C.partnerSet p ∩ designated C.merged (C.choice s)) :
    Adjacent C.merged (C.choice s).line p x := by
  classical
  obtain ⟨hxZ, hxF⟩ := Finset.mem_inter.mp hx
  obtain ⟨_, ⟨⟨d, b⟩, hpM, hxM⟩⟩ := Finset.mem_filter.mp hxZ
  have hxS := designated_on_line C hV s hxF
  have hne : p ≠ x := by
    intro heq
    subst x
    exact hpnot hxF
  have hd : d ≠ (C.choice s).line.1 := by
    intro heq
    have hline : (C.choice s).line = constituent C.merged d b := by
      apply Prod.ext heq.symm
      change (C.choice s).line.2 = C.merged d b
      change lineEval (C.choice s).line.1 p = (C.choice s).line.2 at hp
      change lineEval d p = C.merged d b at hpM
      calc
        (C.choice s).line.2 = lineEval (C.choice s).line.1 p := hp.symm
        _ = lineEval d p := by rw [heq]
        _ = C.merged d b := hpM
    apply (hV.2 s).2.1
    rw [hline]
    exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, rfl⟩
  refine ⟨hp, hxS, hne, d, hd, ?_⟩
  cases b with
  | false => exact Or.inl ⟨hpM, hxM⟩
  | true => exact Or.inr ⟨hpM, hxM⟩

theorem partner_inter_designated_card_le_one (hV : C.Valid)
    (s : Slot F) (p : Point F) (hp : OnLine p (C.choice s).line)
    (hpnot : p ∉ designated C.merged (C.choice s)) :
    (C.partnerSet p ∩ designated C.merged (C.choice s)).card ≤ 1 := by
  classical
  let I : Finset (Fin 4) := Finset.univ.filter
    (fun i => Adjacent C.merged (C.choice s).line p
      (tuplePoint C.merged (C.choice s).tuple i))
  have hsub : C.partnerSet p ∩ designated C.merged (C.choice s) ⊆
      I.image (tuplePoint C.merged (C.choice s).tuple) := by
    intro x hx
    have hadj := partner_adjacent C hV s p x hp hpnot hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).2
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hi⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [hi] using hadj
  rcases hV.2 s with ⟨_, _, _, _, _, _, _, _, hext⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_image_le).trans (hext p hp hpnot))

theorem partner_inter_designated_card_le_one_of_two (hV : C.Valid)
    (hC : C.Compatible) (s : Slot F) (p : Point F)
    (hb : 2 ≤ C.splitMultiplicity p) (hp : OnLine p (C.choice s).line) :
    (C.partnerSet p ∩ designated C.merged (C.choice s)).card ≤ 1 :=
  partner_inter_designated_card_le_one C hV s p hp
    (ConfigurationStructure.center_not_designated C hC hb s)

theorem partner_card_le_splitMultiplicity (hV : C.Valid) (hC : C.Compatible)
    (p : Point F) (hb : 2 ≤ C.splitMultiplicity p) :
    (C.partnerSet p).card ≤ C.splitMultiplicity p := by
  classical
  rw [ConfigurationStructure.split_multiplicity_eq_slots C hV hC p]
  apply ConstructionStructure.partner_card_le_slots
    (Finset.univ.filter (fun s : Slot F => OnLine p (C.choice s).line))
    (fun s => designated C.merged (C.choice s)) (C.partnerSet p)
  · exact Finset.filter_subset _ _
  · intro s hs
    exact partner_inter_designated_card_le_one_of_two C hV hC s p hb
      (Finset.mem_filter.mp hs).2

theorem nonsplit_line_disjoint_designatedAt (hV : C.Valid) (hC : C.Compatible)
    (p : Point F) (hb : 2 ≤ C.splitMultiplicity p) (l : Line F)
    (hp : OnLine p l) (hl : l ∉ C.splitLinesAt p) :
    Disjoint (linePoints l) (C.designatedAt p) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxL hxF
  obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hxF
  have hpS := (Finset.mem_filter.mp hs).2
  have hS : (C.choice s).line ∈ C.splitLinesAt p :=
    Finset.mem_filter.mpr ⟨ConfigurationStructure.choice_line_mem_split C s, hpS⟩
  have hne : l ≠ (C.choice s).line := by
    intro heq
    exact hl (heq.symm ▸ hS)
  have hxp : x = p := common_point_eq_of_lines_ne l (C.choice s).line hne x p
    (Finset.mem_filter.mp hxL).2 (designated_on_line C hV s hxs) hp hpS
  exact ConfigurationStructure.center_not_designated C hC hb s (hxp ▸ hxs)

private theorem constituent_not_splitLinesAt (hV : C.Valid) (p : Point F)
    (d : Direction F) (b : Bool) :
    constituent C.merged d b ∉ C.splitLinesAt p := by
  intro h
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
  apply (hV.2 s).2.1
  rw [hs]
  exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, rfl⟩

theorem merged_inter_designatedAt_subset_partnerSet (hV : C.Valid)
    (hC : C.Compatible) (p : Point F) (hb : 2 ≤ C.splitMultiplicity p)
    (d : Direction F) (b : Bool) (hp : OnLine p (constituent C.merged d b)) :
    mergedPoints C.merged d ∩ C.designatedAt p ⊆ C.partnerSet p := by
  classical
  have hdis := nonsplit_line_disjoint_designatedAt C hV hC p hb
    (constituent C.merged d b) hp (constituent_not_splitLinesAt C hV p d b)
  intro x hx
  obtain ⟨hxM, hxF⟩ := Finset.mem_inter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hxF, (d, b), hp, ?_⟩
  cases b with
  | false =>
    rcases Finset.mem_union.mp hxM with hx0 | hx1
    · exact False.elim (Finset.disjoint_left.mp hdis hx0 hxF)
    · exact (Finset.mem_filter.mp hx1).2
  | true =>
    rcases Finset.mem_union.mp hxM with hx0 | hx1
    · exact (Finset.mem_filter.mp hx0).2
    · exact False.elim (Finset.disjoint_left.mp hdis hx1 hxF)

theorem regular_block_disjoint_designatedAt (hV : C.Valid) (hC : C.Compatible)
    (p : Point F) (hb : 2 ≤ C.splitMultiplicity p) (l : Line F)
    (hregular : C.IsBlockLabel (Sum.inl l)) (hp : OnLine p l) :
    Disjoint (C.blockPoints (Sum.inl l)) (C.designatedAt p) := by
  have hl : l ∉ C.splitLinesAt p := by
    intro h
    exact hregular (Finset.mem_union_left _ (Finset.mem_filter.mp h).1)
  exact (nonsplit_line_disjoint_designatedAt C hV hC p hb l hp hl).mono_left
    Finset.inter_subset_left

theorem merged_block_inter_designatedAt_subset_partnerSet (hV : C.Valid)
    (hC : C.Compatible) (p : Point F) (hb : 2 ≤ C.splitMultiplicity p)
    (d : Direction F) (b : Bool) (hp : OnLine p (constituent C.merged d b)) :
    C.blockPoints (Sum.inr (Sum.inl d)) ∩ C.designatedAt p ⊆ C.partnerSet p := by
  intro x hx
  apply merged_inter_designatedAt_subset_partnerSet C hV hC p hb d b hp
  exact Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1, (Finset.mem_inter.mp hx).2⟩

end
end Balanced.ConstructionPartners

end OAI
