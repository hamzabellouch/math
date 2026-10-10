import OAI.Combinatorics.BalancedRyser.Construction.ValidChoice
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Probability.ConfigurationStructure

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def NonsplitThrough (C : Configuration F) (p : Point F) : BlockLabel F → Prop
  | Sum.inl l => OnLine p l
  | Sum.inr (Sum.inl d) => ∃ s : Bool, OnLine p (constituent C.merged d s)
  | Sum.inr (Sum.inr _) => False

omit [Field F] in
private theorem constituent_mem (C : Configuration F) (d : Direction F) (s : Bool) :
    constituent C.merged d s ∈ constituentLines C.merged :=
  Finset.mem_image.mpr ⟨(d, s), Finset.mem_univ _, rfl⟩

theorem split_ne_constituent (C : Configuration F) (hV : C.Valid)
    (s : Slot F) (d : Direction F) (e : Bool) :
    (C.choice s).line ≠ constituent C.merged d e := by
  intro he
  exact (hV.2 s).2.1 (he ▸ constituent_mem C d e)

theorem nonsplit_trace (C : Configuration F) (hV : C.Valid) (s : Slot F)
    (p : Point F) (hp : OnLine p (C.choice s).line)
    (b : BlockLabel F) (hb : b ∈ C.blockLabels) (hbp : C.NonsplitThrough p b)
    {x : Point F} (hx : x ∈ designated C.merged (C.choice s))
    (hxb : x ∈ C.blockPoints b) :
    x = p ∨ Adjacent C.merged (C.choice s).line p x := by
  classical
  have hxS : OnLine x (C.choice s).line := by
    simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and]
      using ConfigurationStructure.choice_designated_subset C hV s hx
  rcases b with l | d | t
  · left
    have hl : l ∉ C.splitLines ∪ constituentLines C.merged := (Finset.mem_filter.mp hb).2
    have hne : l ≠ (C.choice s).line := by
      intro he
      apply hl
      apply Finset.mem_union_left
      rw [he]
      exact ConfigurationStructure.choice_line_mem_split C s
    have hxl : OnLine x l := (Finset.mem_filter.mp (Finset.mem_inter.mp hxb).1).2
    exact common_point_eq_of_lines_ne l (C.choice s).line hne x p hxl hxS hbp hp
  · obtain ⟨e, hpe⟩ := hbp
    by_cases hxp : x = p
    · exact Or.inl hxp
    right
    have hd : d ≠ (C.choice s).line.1 := by
      intro he
      have hlines := eq_of_onLine_same_direction p (constituent C.merged d e)
        (C.choice s).line he hpe hp
      exact split_ne_constituent C hV s d e hlines.symm
    have hxM := (Finset.mem_inter.mp hxb).1
    simp only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and] at hxM
    refine ⟨hp, hxS, Ne.symm hxp, d, hd, ?_⟩
    cases e
    · rcases hxM with hx0 | hx1
      · exact False.elim (hxp (common_point_eq_of_lines_ne
          (C.choice s).line (constituent C.merged d false)
          (split_ne_constituent C hV s d false) x p hxS hx0 hp hpe))
      · exact Or.inl ⟨hpe, hx1⟩
    · rcases hxM with hx0 | hx1
      · exact Or.inr ⟨hpe, hx0⟩
      · exact False.elim (hxp (common_point_eq_of_lines_ne
          (C.choice s).line (constituent C.merged d true)
          (split_ne_constituent C hV s d true) x p hxS hx1 hp hpe))
  · exact False.elim hbp

theorem nonsplit_pencil_not_cover (C : Configuration F) (hV : C.Valid)
    (s : Slot F) (p : Point F) (hp : OnLine p (C.choice s).line)
    (B : Finset (BlockLabel F)) (hB : B ⊆ C.blockLabels)
    (hthrough : ∀ b ∈ B, C.NonsplitThrough p b) :
    ¬ C.points ⊆ B.biUnion C.blockPoints := by
  classical
  intro hcover
  apply SplitGeometry.valid_not_covered (hV.2 s) p hp
    (fun x => x ∈ B.biUnion C.blockPoints)
  · intro x hx hc
    obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hc
    exact nonsplit_trace C hV s p hp b (hB hb) (hthrough b hb) hx hxb
  · intro x hx
    exact hcover (ConfigurationStructure.designated_subset_points C s hx)

theorem one_split_cover_impossible (C : Configuration F) (hV : C.Valid)
    (p : Point F) (hb : C.splitMultiplicity p = 1)
    (B A : Finset (BlockLabel F)) (hB : B ⊆ C.blockLabels)
    (hAsub : A ⊆ B) (hBcard : B.card ≤ Fintype.card F)
    (hAcard : Fintype.card F ≤ A.card)
    (hAthrough : ∀ b ∈ A, C.NonsplitThrough p b) :
    ¬ C.points ⊆ B.biUnion C.blockPoints := by
  classical
  have hAB : A = B := Finset.eq_of_subset_of_card_le hAsub (hBcard.trans hAcard)
  have hpos : 0 < (C.splitLinesAt p).card := by
    change 0 < C.splitMultiplicity p
    rw [hb]
    decide
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
  obtain ⟨hl, hpl⟩ := Finset.mem_filter.mp hl
  obtain ⟨s, _, hsl⟩ := Finset.mem_image.mp hl
  have hps : OnLine p (C.choice s).line := by simpa only [hsl] using hpl
  apply nonsplit_pencil_not_cover C hV s p hps B hB
  intro b hbB
  exact hAthrough b (hAB.symm ▸ hbB)

end Configuration
end Balanced

end OAI
