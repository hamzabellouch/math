import OAI.Combinatorics.BalancedRyser.Local.ReusePrescriptions

namespace OAI

namespace Balanced.ReusePrescription
open Local Local.KernelBridge
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def sourcePoint (l : List (Code F)) (M : MergedPairs F)
    (x : {c : Code F // c ∈ l} × Fin 4) : Point F :=
  tuplePoint M (decodeTuple x.1.val.2) x.2

omit [Field F] in

theorem card_source_positions (l : List (Code F))
    (hnd : (l.map Prod.fst).Nodup) :
    Fintype.card ({c : Code F // c ∈ l} × Fin 4) = 4 * l.length := by
  have hl : l.Nodup := List.Nodup.of_map Prod.fst hnd
  have hc : Fintype.card {c : Code F // c ∈ l} = l.length := by
    calc
      Fintype.card {c : Code F // c ∈ l} = l.toFinset.card :=
        by
          convert Fintype.card_of_finset' (p := {c : Code F | c ∈ l})
            l.toFinset (by intro c; simp) using 1
          congr 1
          exact Subsingleton.elim _ _
      _ = l.length := List.toFinset_card_of_nodup hl
  simp [Fintype.card_prod, hc, Nat.mul_comm]

def SourceEvent (p : Point F) (l : List (Code F)) (M : MergedPairs F) : Prop :=
  AlignedExternal p l M ∧ Function.Injective (sourcePoint l M) ∧
  Function.Injective (fun c : {c : Code F // c ∈ l} => c.val.1.1) ∧
  ∀ c ∈ l, lineThrough c.1.1 p ∉ constituentLines M

omit [Field F] [Fintype F] [DecidableEq F] in
theorem tuple_eq_of_matches {l : List (Code F)} {C : Configuration F}
    (hm : Matches l C) (c : Code F) (hc : c ∈ l) :
    decodeTuple c.2 = (C.choice c.1).tuple := by
  rw [← hm c hc, decode_encode_tuple]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem code_eq_of_matches_slot_eq {l : List (Code F)} {C : Configuration F}
    (hm : Matches l C) {c d : Code F} (hc : c ∈ l) (hd : d ∈ l)
    (he : c.1 = d.1) : c = d := by
  apply Prod.ext he
  exact (hm c hc).symm.trans ((congrArg (fun s => encodeTuple (C.choice s).tuple) he).trans
    (hm d hd))

theorem target_line_eq_of_matches {l : List (Code F)} {C : Configuration F}
    (hv : C.Valid) (p : Point F) (ha : AlignedExternal p l C.merged)
    (hm : Matches l C) (c : Code F) (hc : c ∈ l) :
    (C.choice c.1).line = lineThrough c.1.1 p := by
  apply eq_of_onLine_same_direction (tuplePoint C.merged (C.choice c.1).tuple 0)
  · exact (hv.2 c.1).1
  · exact (hv.2 c.1).2.2.2.2.2.1 0
  · simpa only [tuple_eq_of_matches hm c hc] using (ha c hc).1 0

theorem sourcePoint_injective_of_matches {l : List (Code F)} {C : Configuration F}
    (hv : C.Valid) (hcompat : C.Compatible) (hm : Matches l C) :
    Function.Injective (sourcePoint l C.merged) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ he
  have hp : tuplePoint C.merged (C.choice c.val.1).tuple i =
      tuplePoint C.merged (C.choice d.val.1).tuple j := by
    simpa only [sourcePoint, tuple_eq_of_matches hm c.val c.property,
      tuple_eq_of_matches hm d.val d.property] using he
  have hs : c.val.1 = d.val.1 := by
    apply ConfigurationStructure.designated_slot_unique C hcompat
      (p := tuplePoint C.merged (C.choice c.val.1).tuple i)
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · rw [hp]
      exact (hv.2 d.val.1).2.2.2.2.2.1 j
  have hcd : c = d := Subtype.ext (code_eq_of_matches_slot_eq hm c.property d.property hs)
  subst d
  have hij : i = j := (hv.2 c.val.1).2.2.2.2.1 hp
  exact Prod.ext rfl hij

theorem target_injective_of_matches {l : List (Code F)} {C : Configuration F}
    (hv : C.Valid) (hcompat : C.Compatible) (p : Point F)
    (ha : AlignedExternal p l C.merged) (hm : Matches l C) :
    Function.Injective (fun c : {c : Code F // c ∈ l} => c.val.1.1) := by
  intro c d he
  change c.val.1.1 = d.val.1.1 at he
  have hl : (C.choice c.val.1).line = (C.choice d.val.1).line := by
    rw [target_line_eq_of_matches hv p ha hm c.val c.property,
      target_line_eq_of_matches hv p ha hm d.val d.property, he]
  have hs := ConfigurationStructure.choice_line_injective C hv hcompat hl
  exact Subtype.ext (code_eq_of_matches_slot_eq hm c.property d.property hs)

theorem sourceEvent_of_matches {l : List (Code F)} {C : Configuration F}
    (hv : C.Valid) (hcompat : C.Compatible) (p : Point F)
    (ha : AlignedExternal p l C.merged) (hm : Matches l C) :
    SourceEvent p l C.merged := by
  refine ⟨ha, sourcePoint_injective_of_matches hv hcompat hm,
    target_injective_of_matches hv hcompat p ha hm, ?_⟩
  intro c hc
  rw [← target_line_eq_of_matches hv p ha hm c hc]
  exact (hv.2 c.1).2.1

theorem exists_source_witness (C : Configuration F)
    (hv : C.Valid) (hc : C.Compatible) (p : Point F)
    (hb : 2 ≤ C.splitMultiplicity p) (hr : 3 ≤ reuseCount C p) :
    ∃ l : List (Code F), l.length ≤ 6 ∧ Eligible l ∧
      SourceEvent p l C.merged ∧ Matches l C := by
  obtain ⟨l, hlen, hel, ha, hm⟩ := exists_of_configuration C hv hc p hb hr
  exact ⟨l, hlen, hel, sourceEvent_of_matches hv hc p ha hm, hm⟩

theorem selected_source_list_le (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (p : Point F) (l : List (Code F))
    (hnd : (l.map Prod.fst).Nodup) :
    selectedProbability w (fun C => SourceEvent p l C.merged ∧ Matches l C) ≤
      (K / Fintype.card F) ^ l.length * offsetProbability (SourceEvent p l) := by
  calc
    _ ≤ selectedProbability w (fun C => SourceEvent p l C.merged ∧
        ∀ s ∈ slots l, encodeTuple (C.choice s).tuple = codeAt l s) :=
      selectedProbability_mono w hw.1 (fun _ h => ⟨h.1, matches_codeAt h.2⟩)
    _ ≤ (K / Fintype.card F) ^ (slots l).card * offsetProbability (SourceEvent p l) :=
      selected_prescription_and_offset_le Q w K hw (slots l)
        (fun _ => codeAt l) (SourceEvent p l)
    _ = _ := by rw [slots_card hnd]

theorem selected_reuse_le_source_witness_sum
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (p : Point F) :
    selectedProbability w (fun C => 2 ≤ C.splitMultiplicity p ∧ 3 ≤ reuseCount C p) ≤
      ∑ l ∈ witnesses F,
        (K / Fintype.card F) ^ l.length * offsetProbability (SourceEvent p l) := by
  calc
    _ ≤ ∑ l ∈ witnesses F,
        selectedProbability w (fun C => SourceEvent p l C.merged ∧ Matches l C) := by
      apply selected_union_le (witnesses F) w hw.1
      intro M v hpos hevent
      obtain ⟨hv, hc, _⟩ := hw.2.2.1 M v hpos
      obtain ⟨l, hlen, hel, he, hm⟩ :=
        exists_source_witness (configuration M v) hv hc p hevent.1 hevent.2
      exact ⟨l, (mem_witnesses l).mpr ⟨hlen, hel⟩, he, hm⟩
    _ ≤ _ := Finset.sum_le_sum (fun l hl =>
      selected_source_list_le Q w K hw p l ((mem_witnesses l).mp hl).2.1)

theorem source_witness_sum_le_relaxed (K : ℝ) (hK : 0 ≤ K) (p : Point F) :
    (∑ l ∈ witnesses F,
      (K / Fintype.card F) ^ l.length * offsetProbability (SourceEvent p l)) ≤
    ∑ l ∈ witnesses F,
      (K / Fintype.card F) ^ l.length * offsetProbability (AlignedExternal p l) := by
  apply Finset.sum_le_sum
  intro l _
  exact mul_le_mul_of_nonneg_left (offsetProbability_mono (fun _ h => h.1))
    (pow_nonneg (div_nonneg hK (Nat.cast_nonneg _)) _)
end
end Balanced.ReusePrescription

end OAI
