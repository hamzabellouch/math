import OAI.Combinatorics.BalancedRyser.Incidence.AffinePencilForcing

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

@[simp] private lemma on_line_iff_mem (p : Point F) (l : Line F) :
    p ∈ linePoints l ↔ OnLine p l := by simp [linePoints]

omit [Field F] [Fintype F] [DecidableEq F] in
lemma constituent_ne_of_direction_ne {d e : Direction F} (h : d ≠ e)
    (s t : Bool) : constituent C.merged d s ≠ constituent C.merged e t := by
  intro he
  exact h (congrArg Prod.fst he)

theorem other_block_constituent_trace_le_two (B : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ B, C.IsBlockLabel b) (d : Direction F)
    (homit : (Sum.inr (Sum.inl d) : BlockLabel F) ∉ B)
    (b : BlockLabel F) (hb : b ∈ B) (s : Bool) :
    (C.blockPoints b ∩ linePoints (constituent C.merged d s)).card ≤ 2 := by
  classical
  rcases b with l | e | ⟨slot, side⟩
  · have hne : l ≠ constituent C.merged d s := by
      intro he
      have hlabel := hlabels (Sum.inl l) hb
      apply hlabel
      exact Finset.mem_union_right _ (he.symm ▸ C.mem_constituentLines d s)
    calc
      ((linePoints l ∩ C.points) ∩ linePoints (constituent C.merged d s)).card ≤
          (linePoints l ∩ linePoints (constituent C.merged d s)).card := by
        apply Finset.card_le_card
        intro x hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1,
          (Finset.mem_inter.mp hx).2⟩
      _ ≤ 1 := distinct_line_intersection_card_le_one l _ hne
      _ ≤ 2 := by omega
  · have hed : e ≠ d := by intro he; subst e; exact homit hb
    have hsub : C.blockPoints (Sum.inr (Sum.inl e)) ∩ linePoints (constituent C.merged d s) ⊆
        (linePoints (constituent C.merged e false) ∩ linePoints (constituent C.merged d s)) ∪
        (linePoints (constituent C.merged e true) ∩ linePoints (constituent C.merged d s)) := by
      intro x hx
      have hxpair := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
      rcases Finset.mem_union.mp hxpair with hf | ht
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hf, (Finset.mem_inter.mp hx).2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ht, (Finset.mem_inter.mp hx).2⟩)
    have hf := distinct_line_intersection_card_le_one
      (constituent C.merged e false) (constituent C.merged d s)
      (C.constituent_ne_of_direction_ne hed false s)
    have ht := distinct_line_intersection_card_le_one
      (constituent C.merged e true) (constituent C.merged d s)
      (C.constituent_ne_of_direction_ne hed true s)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
  · have hsub := Finset.card_le_card
      (Finset.inter_subset_left : C.blockPoints (Sum.inr (Sum.inr (slot, side))) ∩
        linePoints (constituent C.merged d s) ⊆ C.blockPoints (Sum.inr (Sum.inr (slot, side))))
    cases side <;> exact hsub.trans Finset.card_le_two

theorem selected_merged_pencil_card_le (B : Finset (BlockLabel F))
    (p : Point F) {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap) :
    ((Finset.univ : Finset (Direction F)).filter (fun d =>
      (Sum.inr (Sum.inl d) : BlockLabel F) ∈ B ∧
      OnLine p (constituent C.merged d false))).card ≤ cap := by
  classical
  apply le_trans _ (hocc.1 p)
  apply Finset.card_le_card_of_injOn (fun d => constituent C.merged d false)
  · intro d hd
    exact Finset.mem_filter.mpr
      ⟨C.mem_constituentLines d false, (Finset.mem_filter.mp hd).2.2⟩
  · intro d hd e he hde
    exact congrArg Prod.fst hde

theorem missing_deleted_constituent_occupancy_bound
    {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F) (d : Direction F) (hpd : OnLine p (constituent C.merged d true))
    (homit : (Sum.inr (Sum.inl d) : BlockLabel F) ∉ B) :
    (linePoints (constituent C.merged d true) ∩ C.retained).card ≤
      1 + cap + 2 * (B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card := by
  classical
  let l := constituent C.merged d true
  let S := linePoints l ∩ C.retained
  let M := (Finset.univ : Finset (Direction F)).filter (fun e =>
    (Sum.inr (Sum.inl e) : BlockLabel F) ∈ B ∧ OnLine p (constituent C.merged e false))
  let E := {p} ∪ M.biUnion (fun e => linePoints (constituent C.merged e true) ∩ linePoints l)
  have hMcard : M.card ≤ cap := C.selected_merged_pencil_card_le B p hocc
  have hMne : ∀ e ∈ M, e ≠ d := by
    intro e he hed
    subst e
    exact homit (Finset.mem_filter.mp he).2.1
  have htrace : ∀ e ∈ M,
      (linePoints (constituent C.merged e true) ∩ linePoints l).card ≤ 1 := by
    intro e he
    exact distinct_line_intersection_card_le_one _ _
      (C.constituent_ne_of_direction_ne (hMne e he) true true)
  have hEcard : E.card ≤ 1 + cap := by
    have hsum := Finset.card_biUnion_le_card_mul M
      (fun e => linePoints (constituent C.merged e true) ∩ linePoints l) 1 htrace
    have hunion := Finset.card_union_le ({p} : Finset (Point F))
      (M.biUnion (fun e => linePoints (constituent C.merged e true) ∩ linePoints l))
    simp only [Finset.card_singleton, Nat.mul_one] at hsum hunion
    exact hunion.trans (Nat.add_le_add_left (hsum.trans hMcard) 1)
  have hsmall : S.card ≤ E.card +
      2 * (B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card := by
    apply pencil_cover_card_bound S E
      (B.filter (C.RepresentedThrough (Sum.inl p))) C.blockPoints
      (B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)) C.blockPoints 2
    · intro x hx
      obtain ⟨b, hb, hxb⟩ := hcover x
        (Finset.mem_union_left _ (Finset.mem_inter.mp hx).2)
      by_cases hbp : C.RepresentedThrough (Sum.inl p) b
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨b, Finset.mem_filter.mpr ⟨hb, hbp⟩, hxb⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨b, Finset.mem_filter.mpr ⟨hb, hbp⟩, hxb⟩)
    · intro b hb x hx
      obtain ⟨hbB, hbP⟩ := Finset.mem_filter.mp hb
      obtain ⟨hxb, hxs⟩ := Finset.mem_inter.mp hx
      have hxl := (on_line_iff_mem x l).mp (Finset.mem_inter.mp hxs).1
      rcases b with m | e | ⟨slot, side⟩
      · have hpm : OnLine p m := by simpa [RepresentedThrough, coreRepresentative, ThroughProjective] using hbP
        have hxm : OnLine x m := (on_line_iff_mem x m).mp (Finset.mem_inter.mp hxb).1
        have hml : m ≠ l := by
          intro he
          exact hlabels (Sum.inl m) hbB
            (Finset.mem_union_right _ (he.symm ▸ C.mem_constituentLines d true))
        have hxp := common_point_eq_of_lines_ne m l hml x p hxm hxl hpm hpd
        exact Finset.mem_union_left _ (Finset.mem_singleton.mpr hxp)
      · have hpfalse : OnLine p (constituent C.merged e false) := by
          simpa [RepresentedThrough, coreRepresentative, ThroughProjective] using hbP
        have heM : e ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbB, hpfalse⟩
        have hxpairs := (Finset.mem_inter.mp hxb).1
        rcases Finset.mem_union.mp hxpairs with hf | ht
        · have hne := C.constituent_ne_of_direction_ne (hMne e heM) false true
          have hxp := common_point_eq_of_lines_ne (constituent C.merged e false) l hne x p
            ((on_line_iff_mem x _).mp hf) hxl hpfalse hpd
          exact Finset.mem_union_left _ (Finset.mem_singleton.mpr hxp)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨e, heM, Finset.mem_inter.mpr ⟨ht, (on_line_iff_mem x l).mpr hxl⟩⟩)
      · simp [RepresentedThrough, coreRepresentative] at hbP
    · intro b hb
      have hsub : C.blockPoints b ∩ S ⊆ C.blockPoints b ∩ linePoints l := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
          (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
      exact (Finset.card_le_card hsub).trans
        (C.other_block_constituent_trace_le_two B hlabels d homit b (Finset.mem_filter.mp hb).1 true)
  exact hsmall.trans (Nat.add_le_add_right hEcard _)

theorem deleted_constituent_merged_label_selected
    {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4)
    (d : Direction F) (hpd : OnLine p (constituent C.merged d true)) :
    (Sum.inr (Sum.inl d) : BlockLabel F) ∈ B := by
  classical
  by_contra homit
  have hbound := C.missing_deleted_constituent_occupancy_bound hocc B hlabels hcover p d hpd homit
  have hboundReal : ((linePoints (constituent C.merged d true) ∩ C.retained).card : ℝ) ≤
      1 + (cap : ℝ) + 2 * ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) := by
    exact_mod_cast hbound
  have hgap := partner_pencil_gap hsize hbudget
  have hoccupancy := hocc.2.2 d
  linarith

end
end Configuration
end Balanced

end OAI
