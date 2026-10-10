import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.LabelCycle

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*} [Fintype V] [DecidableEq E]

variable (inc : E → V → Prop)

abbrev PM := {M : Finset E // MatchingOn inc M Finset.univ}

@[ext] structure RawDemand where
  first : PM inc
  second : PM inc
  anchor : E
  corners : Fin 4 → V
  flags : Fin 64

structure DemandEncoding (d : RawDemand inc) where
  first : PM inc
  second : PM inc
  added : Multiset E
  dropped : Multiset E
  added_card : added.card ≤ 4
  dropped_card : dropped.card ≤ 4
  conservation : d.first.val.val + d.second.val.val + added =
    first.val.val + second.val.val + dropped
  outside : ∀ e ∈ d.first.val ∪ d.second.val,
    ¬ (overlayLineGraph inc (d.first.val ∪ d.second.val)).Reachable d.anchor e →
    (e ∈ d.first.val ↔ e ∈ first.val)

abbrev DemandTag := E × (Fin 4 → V) × Fin 64 × Bool × (Fin 4 → Option E) × (Fin 4 → Option E)

noncomputable def padOccurrences (m : Multiset E) : Fin 4 → Option E :=
  fun i => m.toList[i.val]?

omit [DecidableEq E] in
lemma padOccurrences_recovers {m n : Multiset E} (hm : m.card ≤ 4) (hn : n.card ≤ 4)
    (h : padOccurrences m = padOccurrences n) : m = n := by
  have hl : m.toList = n.toList := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 4
    · exact congrFun h ⟨i, hi⟩
    · have hm' : m.toList.length ≤ i := by rw [Multiset.length_toList]; omega
      have hn' : n.toList.length ≤ i := by rw [Multiset.length_toList]; omega
      rw [List.getElem?_eq_none hm', List.getElem?_eq_none hn']
  simpa only [Multiset.coe_toList] using congrArg (fun l : List E => (l : Multiset E)) hl

omit [DecidableEq E] in
lemma tag_card [Fintype E] : Fintype.card (DemandTag (V := V) (E := E)) =
    Fintype.card E * Fintype.card V ^ 4 * 128 * (Fintype.card E + 1) ^ 8 := by
  simp only [DemandTag, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_option]
  ring

omit [DecidableEq E] in
lemma tag_card_bound [Fintype E] (N : ℕ) (hN : 2 ≤ N) (hV : Fintype.card V ≤ N)
    (hE : Fintype.card E ≤ 2 * N^2) :
    Fintype.card (DemandTag (V := V) (E := E)) ≤ (10*N)^30 := by
  rw [tag_card]
  have hp : 1 ≤ N^2 := Nat.one_le_pow 2 N (by omega)
  have he : Fintype.card E + 1 ≤ 3 * N^2 := by omega
  calc
    _ ≤ (2*N^2) * N^4 * 128 * (3*N^2)^8 := by gcongr
    _ = (2*128*3^8) * N^22 := by ring
    _ ≤ 10^30 * N^30 := by
      exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    _ = _ := by ring

namespace DemandEncoding

variable {inc}

def code {d : RawDemand inc} (a : DemandEncoding inc d) :=
  (a.first, a.second, d.anchor, d.corners, d.flags,
   decide (d.anchor ∈ d.first.val), a.added, a.dropped)

theorem code_recovers {d e : RawDemand inc} (a : DemandEncoding inc d)
    (b : DemandEncoding inc e) (h : a.code = b.code) : d = e := by
  simp only [code, Prod.mk.injEq] at h
  obtain ⟨hf,hs,ha,hc,hfl,hbit,had,hdr⟩ := h
  have hu : d.first.val.val + d.second.val.val = e.first.val.val + e.second.val.val := by
    have hh := a.conservation
    rw [hf, hs, hdr, ← b.conservation, ← had] at hh
    exact add_right_cancel hh
  have hunion := union_eq_of_multiset_union_eq hu
  have hb : d.anchor ∈ d.first.val ↔ d.anchor ∈ e.first.val := by
    rw [← ha] at hbit
    exact decide_eq_decide.mp hbit
  have hp := pair_reconstruction inc d.first.property d.second.property
    e.first.property e.second.property hu d.anchor hb (fun f hfu hnr => by
      have hm := a.outside f hfu hnr
      have hn := b.outside f (hunion ▸ hfu) (by simpa only [← ha, ← hunion] using hnr)
      rw [hf] at hm
      exact hm.trans hn.symm)
  exact RawDemand.ext (Subtype.ext hp.1) (Subtype.ext hp.2) ha hc hfl

noncomputable def tag {d : RawDemand inc} (a : DemandEncoding inc d) : DemandTag (V := V) (E := E) :=
  (d.anchor, d.corners, d.flags, decide (d.anchor ∈ d.first.val),
   padOccurrences a.added, padOccurrences a.dropped)

noncomputable def finiteCode {d : RawDemand inc} (a : DemandEncoding inc d) :=
  (a.first, a.second, a.tag)

theorem finiteCode_recovers {d e : RawDemand inc} (a : DemandEncoding inc d)
    (b : DemandEncoding inc e) (h : a.finiteCode = b.finiteCode) : d = e := by
  simp only [finiteCode, tag, Prod.mk.injEq] at h
  obtain ⟨hf,hs,ha,hc,hfl,hbit,had,hdr⟩ := h
  apply code_recovers a b
  simp only [code, Prod.mk.injEq]
  exact ⟨hf,hs,ha,hc,hfl,hbit,
    padOccurrences_recovers a.added_card b.added_card had,
    padOccurrences_recovers a.dropped_card b.dropped_card hdr⟩

theorem code_injective (P : RawDemand inc → Prop)
    (encode : ∀ d : {d : RawDemand inc // P d}, DemandEncoding inc d.val) :
    Function.Injective (fun d => (encode d).finiteCode) := by
  intro d e h
  exact Subtype.ext (finiteCode_recovers (encode d) (encode e) h)

end DemandEncoding

end

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

structure EmbeddedCell (d : RawDemand inc) where
  cell : CellPaths inc
  orientation : Bool
  first_pattern : cell.orientation orientation ⊆ d.first.val
  second_pattern : cell.orientation (!orientation) ⊆ d.second.val
  reach : ∀ e ∈ cell.orientation true ∪ cell.orientation false,
    (overlayLineGraph inc (d.first.val ∪ d.second.val)).Reachable d.anchor e

namespace EmbeddedCell

variable {inc} {d : RawDemand inc} (c : EmbeddedCell inc d)

variable (hinc : ∀ e, ∃ v, inc e v)

def outsideFirst : Finset E := d.first.val \ c.cell.orientation c.orientation

def outsideSecond : Finset E := d.second.val \ c.cell.orientation (!c.orientation)

lemma outsideFirst_matching : MatchingOn inc c.outsideFirst (Finset.univ \ c.cell.vertices) :=
  d.first.property.sdiff (c.cell.orientation_matching c.orientation) c.first_pattern

lemma outsideSecond_matching : MatchingOn inc c.outsideSecond (Finset.univ \ c.cell.vertices) :=
  d.second.property.sdiff (c.cell.orientation_matching (!c.orientation)) c.second_pattern

lemma context_vertices_disjoint : Disjoint (Finset.univ \ c.cell.vertices) c.cell.vertices :=
  Finset.sdiff_disjoint

def attachFirst (p : Finset E) (hp : MatchingOn inc p c.cell.vertices) : PM inc :=
  ⟨c.outsideFirst ∪ p, by
    have h := c.outsideFirst_matching.union hp c.context_vertices_disjoint
    simpa only [Finset.sdiff_union_of_subset (Finset.subset_univ _)] using h⟩

def attachSecond (p : Finset E) (hp : MatchingOn inc p c.cell.vertices) : PM inc :=
  ⟨c.outsideSecond ∪ p, by
    have h := c.outsideSecond_matching.union hp c.context_vertices_disjoint
    simpa only [Finset.sdiff_union_of_subset (Finset.subset_univ _)] using h⟩

include hinc in
lemma attachFirst_val (p : Finset E) (hp : MatchingOn inc p c.cell.vertices) :
    (c.attachFirst p hp).val.val = c.outsideFirst.val + p.val :=
  union_val_add (c.outsideFirst_matching.disjoint_edges hp hinc c.context_vertices_disjoint)

include hinc in
lemma attachSecond_val (p : Finset E) (hp : MatchingOn inc p c.cell.vertices) :
    (c.attachSecond p hp).val.val = c.outsideSecond.val + p.val :=
  union_val_add (c.outsideSecond_matching.disjoint_edges hp hinc c.context_vertices_disjoint)

include hinc in
lemma source_first_val : d.first.val.val =
    c.outsideFirst.val + (c.cell.orientation c.orientation).val := by
  have h := c.attachFirst_val hinc _ (c.cell.orientation_matching c.orientation)
  have he : (c.attachFirst _ (c.cell.orientation_matching c.orientation)).val = d.first.val := by
    exact Finset.sdiff_union_of_subset c.first_pattern
  rwa [he] at h

include hinc in
lemma source_second_val : d.second.val.val =
    c.outsideSecond.val + (c.cell.orientation (!c.orientation)).val := by
  have h := c.attachSecond_val hinc _ (c.cell.orientation_matching (!c.orientation))
  have he : (c.attachSecond _ (c.cell.orientation_matching (!c.orientation))).val = d.second.val := by
    exact Finset.sdiff_union_of_subset c.second_pattern
  rwa [he] at h

include hinc in
lemma attach_outside (p : Finset E) (hp : MatchingOn inc p c.cell.vertices)
    (e : E) (he : e ∈ d.first.val ∪ d.second.val)
    (hn : ¬ (overlayLineGraph inc (d.first.val ∪ d.second.val)).Reachable d.anchor e) :
    e ∈ d.first.val ↔ e ∈ (c.attachFirst p hp).val := by
  have hnot (b : Bool) : e ∉ c.cell.orientation b := by
    intro hm
    apply hn
    apply c.reach e
    cases b
    · exact Finset.mem_union_right _ hm
    · exact Finset.mem_union_left _ hm
  have hnp : e ∉ p := by
    intro hm
    obtain ⟨v,hv⟩ := hinc e
    have hvc := hp.1 e hm v hv
    rcases Finset.mem_union.mp he with he | he
    · exact hnot _ (d.first.property.edge_mem_of_incident
        (c.cell.orientation_matching c.orientation) c.first_pattern he hvc hv)
    · exact hnot _ (d.second.property.edge_mem_of_incident
        (c.cell.orientation_matching (!c.orientation)) c.second_pattern he hvc hv)
  change e ∈ d.first.val ↔ e ∈ c.outsideFirst ∪ p
  simp only [outsideFirst, Finset.mem_union, Finset.mem_sdiff, hnot, hnp, not_false_eq_true,
    and_true, or_false]

def encode (p q : Finset E) (hp : MatchingOn inc p c.cell.vertices)
    (hq : MatchingOn inc q c.cell.vertices) (add drop : Multiset E)
    (ha : add.card ≤ 4) (hd : drop.card ≤ 4)
    (hcons : (c.cell.orientation true).val + (c.cell.orientation false).val + add =
      p.val + q.val + drop) : DemandEncoding inc d where
  first := c.attachFirst p hp
  second := c.attachSecond q hq
  added := add
  dropped := drop
  added_card := ha
  dropped_card := hd
  conservation := by
    rw [c.source_first_val hinc, c.source_second_val hinc,
      c.attachFirst_val hinc p hp, c.attachSecond_val hinc q hq]
    have ho : (c.cell.orientation c.orientation).val +
        (c.cell.orientation (!c.orientation)).val =
        (c.cell.orientation true).val + (c.cell.orientation false).val := by
      cases c.orientation <;> simp only [Bool.not_false, Bool.not_true]
      ac_rfl
    calc
      _ = c.outsideFirst.val + c.outsideSecond.val +
          ((c.cell.orientation c.orientation).val + (c.cell.orientation (!c.orientation)).val + add) := by ac_rfl
      _ = c.outsideFirst.val + c.outsideSecond.val + (p.val + q.val + drop) := by rw [ho,hcons]
      _ = _ := by ac_rfl
  outside := c.attach_outside hinc p hp

def switchEncoding (b r : Bool) (repair : Fin 4 → E) (hr : c.cell.Repairs r repair) :
    DemandEncoding inc d :=
  c.encode hinc (c.cell.switched b) (c.cell.repaired r repair)
    (c.cell.switched_matching b) (c.cell.repaired_matching r repair hr)
    (c.cell.additions b r repair) (c.cell.drops r)
    (by rw [← (c.cell.modification_cards b r repair).1]; exact (c.cell.modification_cards b r repair).2)
    (c.cell.modification_cards b r repair).2
    (c.cell.switch_conservation b r repair hr hinc)

def errorZeroEncoding (b : Bool) (repair : Fin 4 → E) (hr : c.cell.Repairs b repair) :
    DemandEncoding inc d :=
  c.encode hinc (c.cell.orientation b) (c.cell.guide b repair)
    (c.cell.orientation_matching b) (c.cell.guide_matching b repair hr)
    (c.cell.additions b b repair) (c.cell.drops b)
    (by rw [← (c.cell.modification_cards b b repair).1]; exact (c.cell.modification_cards b b repair).2)
    (c.cell.modification_cards b b repair).2
    (c.cell.guide_conservation b repair hr hinc)

def errorOneEncoding (b : Bool) (repair : Fin 4 → E) (hr : c.cell.Repairs b repair)
    (Y : Fin 4) (hY : CellPaths.sideBit Y = b) : DemandEncoding inc d :=
  c.encode hinc (c.cell.contextOne b Y) (c.cell.guideOne b repair Y)
    (c.cell.context_one_properties b repair hr Y hY hinc).1
    (c.cell.context_one_properties b repair hr Y hY hinc).2.1
    (c.cell.additions b b repair) (c.cell.drops b)
    (by rw [← (c.cell.modification_cards b b repair).1]; exact (c.cell.modification_cards b b repair).2)
    (c.cell.modification_cards b b repair).2 (by
      rw [(c.cell.context_one_properties b repair hr Y hY hinc).2.2]
      exact c.cell.guide_conservation b repair hr hinc)

lemma zero_guide_contains (b : Bool) (repair : Fin 4 → E) (hr : c.cell.Repairs b repair)
    (X : Fin 4) (hX : CellPaths.sideBit X = b) :
    (c.cell.side X).closed (c.cell.chord X) ⊆
      (c.errorZeroEncoding hinc b repair hr).second.val := by
  intro e he
  exact Finset.mem_union_right _ (c.cell.closed_subset_guide b repair X hX he)

lemma one_guide_contains (b : Bool) (repair : Fin 4 → E) (hr : c.cell.Repairs b repair)
    (X Y : Fin 4) (hX : CellPaths.sideBit X = b) (hY : CellPaths.sideBit Y = b)
    (hne : X ≠ Y) :
    (c.cell.side X).closed (c.cell.chord X) ⊆
      (c.errorOneEncoding hinc b repair hr Y hY).second.val := by
  intro e he
  exact Finset.mem_union_right _ (c.cell.closed_subset_guide_one b repair X Y hX hY hne hinc he)

end EmbeddedCell

end

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

namespace IndexedCycle.Corners

variable {c : IndexedCycle inc} (k : c.Corners)

def rawDemand (M N : PM inc) (flags : Fin 64) : RawDemand inc :=
  ⟨M, N, c.edgeAt 0, (fun i => c.vertexAt (k.start i)), flags⟩

noncomputable def embeddedPair (M N : PM inc)
    (hU : ∀ i, c.edgeAt i ∈ M.val ∪ N.val)
    (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (flags : Fin 64) : EmbeddedCell inc (k.rawDemand M N flags) := by
  classical
  let a : ℕ := if c.edgeAt 0 ∈ M.val then 0 else 1
  have ha : a < 2 := by dsimp [a]; split <;> omega
  have hM : ∀ t, t % 2 = a → c.edgeAt t ∈ M.val := by
    intro t ht
    apply (c.cycle_edge_mem_parity M.property N.property hU t).mpr
    dsimp [a] at ht
    split_ifs at ht ⊢ <;> omega
  have hN : ∀ t, t % 2 = 1-a → c.edgeAt t ∈ N.val := by
    intro t ht
    apply (c.cycle_edge_mem_complement M.property N.property hU t).mpr
    rw [c.cycle_edge_mem_parity M.property N.property hU t]
    dsimp [a] at ht
    split_ifs at ht ⊢ <;> first | omega | tauto
  have hb : decide (k.a₀ % 2 = 1-a) = !decide (k.a₀ % 2 = a) := by
    by_cases h : k.a₀ % 2 = a
    · have hn : k.a₀ % 2 ≠ 1-a := by omega
      simp [h]
      omega
    · have hn : k.a₀ % 2 = 1-a := by omega
      simp [hn]
      omega
  refine ⟨k.cellPaths chord hc, decide (k.a₀ % 2 = a),
    k.cell_orientation_subset chord hc M.val a ha hM, ?_, ?_⟩
  · rw [← hb]
    exact k.cell_orientation_subset chord hc N.val (1-a) (by omega) hN
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact k.cell_orientation_reachable chord hc _ hU true e he
    · exact k.cell_orientation_reachable chord hc _ hU false e he

end IndexedCycle.Corners

end

variable {V E : Type*} [Fintype V]

variable {inc : E → V → Prop}

noncomputable def matchingWeight (w : E → ℝ) (M : PM inc) : ℝ := ∏ e ∈ M.val, w e

lemma matchingWeight_pos (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM inc) :
    0 < matchingWeight w M := Finset.prod_pos (fun e _ => hw e)

variable [Fintype E]

noncomputable def partition (w : E → ℝ) : ℝ := by
  classical
  exact ∑ M : PM inc, matchingWeight w M

lemma partition_pos (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM inc) :
    0 < partition (inc := inc) w := by
  classical
  exact Finset.sum_pos' (fun A _ => le_of_lt (matchingWeight_pos w hw A))
    ⟨M, Finset.mem_univ _, matchingWeight_pos w hw M⟩

noncomputable def gibbs (w : E → ℝ) (M : PM inc) : ℝ :=
  matchingWeight w M / partition (inc := inc) w

lemma gibbs_pos (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM inc) :
    0 < gibbs w M := div_pos (matchingWeight_pos w hw M) (partition_pos w hw M)

lemma gibbs_sum (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM inc) :
    letI : Fintype (PM inc) := Fintype.ofFinite _
    ∑ A : PM inc, gibbs w A = 1 := by
  classical
  simp only [gibbs, ← Finset.sum_div]
  have hp := ne_of_gt (partition_pos w hw M)
  convert div_self hp using 1
  congr 1
  unfold partition
  congr 1
  ext A
  simp

end MatchingFPRAS.Transport

end OAI
