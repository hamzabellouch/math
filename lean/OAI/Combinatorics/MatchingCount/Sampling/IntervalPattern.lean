import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.PM

namespace OAI

namespace MatchingFPRAS.Transport
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
variable {inc : E → V → Prop}
namespace DemandEncoding

variable {d : RawDemand inc} (enc : DemandEncoding inc d)

lemma gibbs_bound (w : E → ℝ) (hw : ∀ e, 0 < w e) (A : ℝ) (hA : 1 ≤ A)
    (hcard : enc.dropped.card = enc.added.card)
    (hcompare : ∀ e ∈ enc.dropped, ∀ f ∈ enc.added, w e ≤ A * w f) :
    gibbs w d.first * gibbs w d.second ≤ A^4 * gibbs w enc.first * gibbs w enc.second := by
  have h := four_edge_weight_bound w hw A hA
    (d.first.val.val + d.second.val.val) (enc.first.val.val + enc.second.val.val)
    enc.dropped enc.added enc.conservation hcard enc.dropped_card hcompare
  simp only [Multiset.map_add, Multiset.prod_add, ← Finset.prod_eq_multiset_prod] at h
  have h' : matchingWeight w d.first * matchingWeight w d.second ≤
      A^4 * (matchingWeight w enc.first * matchingWeight w enc.second) := h
  have hp : 0 ≤ partition (inc := inc) w * partition (inc := inc) w := mul_self_nonneg _
  have hh := div_le_div_of_nonneg_right h' hp
  dsimp only [gibbs]
  calc
    _ = (matchingWeight w d.first * matchingWeight w d.second) /
        (partition (inc := inc) w * partition (inc := inc) w) := div_mul_div_comm _ _ _ _
    _ ≤ A^4 * (matchingWeight w enc.first * matchingWeight w enc.second) /
        (partition (inc := inc) w * partition (inc := inc) w) := hh
    _ = _ := by
      field_simp [ne_of_gt (partition_pos w hw d.first)]

end DemandEncoding

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.IndexedCycle

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

include hheight hstep

theorem actual_switch_encoding
    (M N : PM (BagEdge.Incident (bags := bags)))
    (hU : ∀ i, c.edgeAt i ∈ M.val ∪ N.val)
    {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y) (hy : y < c.size)
    (flags : Fin 64) (b : Bool) (D : ℝ) (hD : 1 ≤ D)
    (w : BagEdge bags → ℝ)
    (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)
    (lo hi : ℝ) (hlo : 0 < lo) (_hlohi : lo ≤ hi) :
    let k := c.cellCorners hbags hc hy
    let emb := k.embeddedPair M N hU (c.cellChords hbags hc hy)
      (c.cellChords_incidence hbags hc hy) flags
    let wt := fun e => max lo (min hi (w e))
    ∃ enc : DemandEncoding BagEdge.Incident (k.rawDemand M N flags),
      enc.first.val = emb.outsideFirst ∪ (c.pathsOfCell hbags hc hy).switched b ∧
      gibbs wt M * gibbs wt N ≤
        (1000*D)^4 * gibbs wt enc.first * gibbs wt enc.second := by
  classical
  dsimp only
  let k := c.cellCorners hbags hc hy
  let emb := k.embeddedPair M N hU (c.cellChords hbags hc hy)
    (c.cellChords_incidence hbags hc hy) flags
  obtain ⟨r, hg⟩ := c.cell_has_good_pair hbags hc hy
  have hr := c.cell_actual_repairs hbags hc hy r hg
  let enc := emb.switchEncoding BagEdge.exists_incident b r (c.leafRepair hbags k) hr
  refine ⟨enc, rfl, ?_⟩
  apply enc.gibbs_bound (fun e => max lo (min hi (w e)))
    (fun e => lt_of_lt_of_le hlo (le_max_left _ _)) (1000*D) (by linarith)
  · exact ((c.pathsOfCell hbags hc hy).modification_cards b r (c.leafRepair hbags k)).1
  · intro e he f hf
    exact c.cell_clamp_comparability hbags height hheight hstep hc hy D hD w hw lo hi
      (le_of_lt hlo) (c.drops_local hbags hc hy r he)
      (c.additions_local hbags hc hy b r hg hf)

theorem actual_error_encodings
    (M N : PM (BagEdge.Incident (bags := bags)))
    (hU : ∀ i, c.edgeAt i ∈ M.val ∪ N.val)
    {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y) (hy : y < c.size)
    (flags : Fin 64) (b : Bool) (X Y : Fin 4)
    (hX : CellPaths.sideBit X = b) (hY : CellPaths.sideBit Y = b) (hne : X ≠ Y)
    (hl : ∀ i : Fin 4, CellPaths.sideBit i = b → (c.cellCorners hbags hc hy).length i ≠ 1)
    (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)
    (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)
    (lo hi : ℝ) (hlo : 0 < lo) (_hlohi : lo ≤ hi) :
    let k := c.cellCorners hbags hc hy
    let emb := k.embeddedPair M N hU (c.cellChords hbags hc hy)
      (c.cellChords_incidence hbags hc hy) flags
    let cp := c.pathsOfCell hbags hc hy
    let wt := fun e => max lo (min hi (w e))
    ∃ enc₀ enc₁ : DemandEncoding BagEdge.Incident (k.rawDemand M N flags),
      enc₀.first.val = emb.outsideFirst ∪ cp.orientation b ∧
      enc₁.first.val = emb.outsideFirst ∪ cp.contextOne b Y ∧
      (cp.side X).closed (cp.chord X) ⊆ enc₀.second.val ∧
      (cp.side X).closed (cp.chord X) ⊆ enc₁.second.val ∧
      gibbs wt M * gibbs wt N ≤ (1000*D)^4 * gibbs wt enc₀.first * gibbs wt enc₀.second ∧
      gibbs wt M * gibbs wt N ≤ (1000*D)^4 * gibbs wt enc₁.first * gibbs wt enc₁.second := by
  classical
  dsimp only
  let k := c.cellCorners hbags hc hy
  let emb := k.embeddedPair M N hU (c.cellChords hbags hc hy)
    (c.cellChords_incidence hbags hc hy) flags
  have hg := c.cell_long_opposite_good hbags hc hy b hl
  have hr := c.cell_actual_repairs hbags hc hy b hg
  let enc₀ := emb.errorZeroEncoding BagEdge.exists_incident b (c.leafRepair hbags k) hr
  let enc₁ := emb.errorOneEncoding BagEdge.exists_incident b (c.leafRepair hbags k) hr Y hY
  refine ⟨enc₀, enc₁, rfl, rfl,
    emb.zero_guide_contains BagEdge.exists_incident b _ hr X hX,
    emb.one_guide_contains BagEdge.exists_incident b _ hr X Y hX hY hne, ?_, ?_⟩
  all_goals
    first
    | apply enc₀.gibbs_bound (fun e => max lo (min hi (w e)))
        (fun e => lt_of_lt_of_le hlo (le_max_left _ _)) (1000*D) (by linarith)
    | apply enc₁.gibbs_bound (fun e => max lo (min hi (w e)))
        (fun e => lt_of_lt_of_le hlo (le_max_left _ _)) (1000*D) (by linarith)
    · exact ((c.pathsOfCell hbags hc hy).modification_cards b b (c.leafRepair hbags k)).1
    · intro e he f hf
      exact c.cell_clamp_comparability hbags height hheight hstep hc hy D hD w hw lo hi
        (le_of_lt hlo) (c.drops_local hbags hc hy b he)
        (c.additions_local hbags hc hy b b hg hf)

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Transport

section

variable {V E : Type*}

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

lemma edgeAt_periodic (i : ℕ) : c.edgeAt (i + c.size) = c.edgeAt i := by
  simp [edgeAt, index]

variable [DecidableEq E]

def intervalPattern (x y a : ℕ) : Finset E :=
  ((Finset.Ico x y).filter (fun i => i % 2 = a)).image c.edgeAt

def parityPattern (a : ℕ) : Finset E := c.intervalPattern 0 c.size a

lemma mem_intervalPattern (e : E) (x y a : ℕ) :
    e ∈ c.intervalPattern x y a ↔ ∃ i, x ≤ i ∧ i < y ∧ i % 2 = a ∧ c.edgeAt i = e := by
  simp only [intervalPattern, Finset.mem_image, Finset.mem_filter, Finset.mem_Ico]
  aesop

lemma intervalPattern_union {x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) (a : ℕ) :
    c.intervalPattern x y a ∪ c.intervalPattern y z a = c.intervalPattern x z a := by
  ext e
  simp only [Finset.mem_union, c.mem_intervalPattern]
  constructor
  · rintro (⟨i,hi,hj,hp,he⟩ | ⟨i,hi,hj,hp,he⟩)
    · exact ⟨i,hi,by omega,hp,he⟩
    · exact ⟨i,by omega,hj,hp,he⟩
  · rintro ⟨i,hi,hj,hp,he⟩
    by_cases h : i < y
    · exact Or.inl ⟨i,hi,h,hp,he⟩
    · exact Or.inr ⟨i,by omega,hj,hp,he⟩

lemma intervalPattern_periodic {x y : ℕ} (a : ℕ) :
    c.intervalPattern (x + c.size) (y + c.size) a = c.intervalPattern x y a := by
  ext e
  simp only [c.mem_intervalPattern]
  constructor
  · rintro ⟨i,hi,hj,hp,he⟩
    have hn : c.size ≤ i := by omega
    refine ⟨i-c.size,by omega,by omega,?_,?_⟩
    · have hh := c.even
      omega
    · have eq : i - c.size + c.size = i := by omega
      rw [← c.edgeAt_periodic, eq]
      exact he
  · rintro ⟨i,hi,hj,hp,he⟩
    refine ⟨i+c.size,by omega,by omega,?_,?_⟩
    · have hh := c.even
      omega
    · rw [c.edgeAt_periodic]; exact he

lemma rotatedPattern {x : ℕ} (hx : x ≤ c.size) (a : ℕ) :
    c.intervalPattern x (x+c.size) a = c.parityPattern a := by
  rw [← c.intervalPattern_union hx (by omega) a]
  have hh : c.intervalPattern c.size (x+c.size) a = c.intervalPattern 0 x a := by
    simpa only [zero_add] using (c.intervalPattern_periodic (x := 0) (y := x) a)
  rw [hh, Finset.union_comm, c.intervalPattern_union (by omega) hx a]
  rfl

lemma arc_through (x l : ℕ) (hx : x < c.size) (hl : 0 < l)
    (hlt : l < c.size) (ho : l % 2 = 1) :
    (c.arc x l hx hl hlt ho).through = c.intervalPattern x (x+l) (x%2) := by
  ext e
  simp only [OddPath.through, pathPattern, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Ico, c.mem_intervalPattern]
  dsimp only [arc]
  constructor
  · rintro ⟨j,⟨⟨_,hj⟩,hp⟩,he⟩
    exact ⟨x+j,by omega,by omega,by omega,he⟩
  · rintro ⟨i,hi,hj,hp,he⟩
    refine ⟨i-x,⟨⟨by omega,by omega⟩,by omega⟩,?_⟩
    simpa only [Nat.add_sub_of_le hi] using he

lemma arc_interior (x l : ℕ) (hx : x < c.size) (hl : 0 < l)
    (hlt : l < c.size) (ho : l % 2 = 1) :
    (c.arc x l hx hl hlt ho).interior = c.intervalPattern x (x+l) (1-x%2) := by
  ext e
  simp only [OddPath.interior, pathPattern, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Ico, c.mem_intervalPattern]
  dsimp only [arc]
  constructor
  · rintro ⟨j,⟨⟨hj₀,hj₁⟩,hp⟩,he⟩
    exact ⟨x+j,by omega,by omega,by omega,he⟩
  · rintro ⟨i,hi,hj,hp,he⟩
    refine ⟨i-x,⟨⟨by omega,by omega⟩,by omega⟩,?_⟩
    simpa only [Nat.add_sub_of_le hi] using he

variable [DecidableEq V]

namespace Corners

variable {c} (k : c.Corners)

lemma cell_piece_interval (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (b : Bool) (i : Fin 4) :
    (k.cellPaths chord hc).orientationPieces b i =
      c.intervalPattern (k.start i) (k.stop i) (if b then k.a₀%2 else 1-k.a₀%2) := by
  have hs := k.parity_start i
  have hb := k.bounds i
  have he : k.start i + k.length i = k.stop i := by dsimp [length]; omega
  change (if CellPaths.sideBit i = b then (k.side i).through else (k.side i).interior) = _
  by_cases h : CellPaths.sideBit i = b
  · rw [ite_eq_left h]
    rw [show (k.side i).through = _ from c.arc_through _ _ _ _ _ _, he]
    cases b <;> simp_all
  · rw [ite_eq_right h]
    rw [show (k.side i).interior = _ from c.arc_interior _ _ _ _ _ _, he]
    cases b <;> cases hi : CellPaths.sideBit i <;> simp_all
    congr 1
    omega

lemma cell_orientation_parity (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (b : Bool) :
    (k.cellPaths chord hc).orientation b =
      c.parityPattern (if b then k.a₀%2 else 1-k.a₀%2) := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have h₃ := k.lt₃
  unfold CellPaths.orientation CellPaths.assemble
  simp only [k.cell_piece_interval, start, stop, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  rw [show c.size + k.a₀ = k.a₀ + c.size by omega]
  have h := c.rotatedPattern (x := k.a₀) (by omega) (if b then k.a₀%2 else 1-k.a₀%2)
  rw [← h]
  ext e
  simp only [Finset.mem_union, c.mem_intervalPattern]
  constructor
  · rintro ((⟨i,hi,hj,hp,he⟩ | ⟨i,hi,hj,hp,he⟩) | (⟨i,hi,hj,hp,he⟩ | ⟨i,hi,hj,hp,he⟩)) <;>
      exact ⟨i,by omega,by omega,hp,he⟩
  · rintro ⟨i,hi,hj,hp,he⟩
    by_cases ha : i < k.a₁
    · exact Or.inl (Or.inl ⟨i,hi,ha,hp,he⟩)
    · by_cases hb : i < k.a₂
      · exact Or.inr (Or.inl ⟨i,by omega,hb,hp,he⟩)
      · by_cases hd : i < k.a₃
        · exact Or.inl (Or.inr ⟨i,by omega,hd,hp,he⟩)
        · exact Or.inr (Or.inr ⟨i,by omega,hj,hp,he⟩)

end Corners

end IndexedCycle

end

open scoped symmDiff

variable {V E : Type*} [DecidableEq E]

variable {inc : E → V → Prop}

def exchange (M N S : Finset E) : Finset E := (M \ S) ∪ (N ∩ S)

lemma mem_exchange (M N S : Finset E) (e : E) :
    e ∈ exchange M N S ↔ (e ∈ M ∧ e ∉ S) ∨ (e ∈ N ∧ e ∈ S) := by
  simp only [exchange, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]

lemma exchange_union (M N S : Finset E) :
    exchange M N S ∪ exchange N M S = M ∪ N := by
  ext e
  simp only [Finset.mem_union, mem_exchange]
  tauto

lemma exchange_involution (M N S : Finset E) :
    exchange (exchange M N S) (exchange N M S) S = M := by
  ext e
  simp only [mem_exchange]
  tauto

lemma exchange_composition (M N S T : Finset E) :
    exchange (exchange M N S) (exchange N M S) T = exchange M N (S ∆ T) := by
  ext e
  simp only [mem_exchange, Finset.mem_symmDiff]
  tauto

lemma exchange_multiset (M N S : Finset E) :
    (exchange M N S).val + (exchange N M S).val = M.val + N.val := by
  apply Multiset.ext.mpr
  intro e
  have hc (s : Finset E) : Multiset.count e s.val = if e ∈ s then 1 else 0 :=
    Multiset.count_eq_of_nodup s.nodup
  simp only [Multiset.count_add, hc]
  by_cases hs : e ∈ S <;> by_cases hm : e ∈ M <;> by_cases hn : e ∈ N <;>
    simp [mem_exchange, hs, hm, hn]

lemma exchange_weight {R : Type*} [CommMonoid R] (w : E → R) (M N S : Finset E) :
    (∏ e ∈ exchange M N S, w e) * (∏ e ∈ exchange N M S, w e) =
      (∏ e ∈ M, w e) * (∏ e ∈ N, w e) := by
  have h := congrArg (fun U : Multiset E => (U.map w).prod) (exchange_multiset M N S)
  simpa only [Multiset.map_add, Multiset.prod_add, Finset.prod_eq_multiset_prod] using h

def ExchangeCompatible (M N S : Finset E) : Prop :=
  ∀ e ∈ M, ∀ f ∈ N, ∀ v, inc e v → inc f v → (e ∈ S ↔ f ∈ S)

omit [DecidableEq E] in
lemma ExchangeCompatible.symm {M N S : Finset E} (h : ExchangeCompatible (inc := inc) M N S) :
    ExchangeCompatible (inc := inc) N M S := by
  intro f hf e he v hfv hev
  exact (h e he f hf v hev hfv).symm

lemma exchange_matching [Fintype V] {M N S : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (h : ExchangeCompatible (inc := inc) M N S) :
    MatchingOn inc (exchange M N S) Finset.univ := by
  refine ⟨fun _ _ v _ => Finset.mem_univ v, ?_⟩
  intro v _
  obtain ⟨e,⟨he,hev⟩,hu⟩ := hM.2 v (Finset.mem_univ v)
  obtain ⟨f,⟨hf,hfv⟩,hv⟩ := hN.2 v (Finset.mem_univ v)
  have hs := h e he f hf v hev hfv
  by_cases hse : e ∈ S
  · have hsf := hs.mp hse
    refine ⟨f, ⟨(mem_exchange M N S f).mpr (Or.inr ⟨hf,hsf⟩),hfv⟩, ?_⟩
    rintro g ⟨hg,hgv⟩
    rcases (mem_exchange M N S g).mp hg with ⟨hgm,hgs⟩ | ⟨hgn,_⟩
    · have heq := hu g ⟨hgm,hgv⟩
      exact (hgs (heq ▸ hse)).elim
    · exact hv g ⟨hgn,hgv⟩
  · refine ⟨e, ⟨(mem_exchange M N S e).mpr (Or.inl ⟨he,hse⟩),hev⟩, ?_⟩
    rintro g ⟨hg,hgv⟩
    rcases (mem_exchange M N S g).mp hg with ⟨hgm,_⟩ | ⟨hgn,hgs⟩
    · exact hu g ⟨hgm,hgv⟩
    · have heq := hv g ⟨hgn,hgv⟩
      exact (hse (hs.mpr (heq ▸ hgs))).elim

noncomputable def componentEdges (U : Finset E) (anchor : E) : Finset E := by
  classical
  exact U.filter ((overlayLineGraph inc U).Reachable anchor)

omit [DecidableEq E] in
lemma mem_componentEdges (U : Finset E) (a e : E) :
    e ∈ componentEdges (inc := inc) U a ↔ e ∈ U ∧ (overlayLineGraph inc U).Reachable a e := by
  classical
  simp only [componentEdges, Finset.mem_filter]

lemma shares_reachable {U : Finset E} {e f : E} (he : e ∈ U) (hf : f ∈ U)
    {v : V} (hev : inc e v) (hfv : inc f v) :
    (overlayLineGraph inc U).Reachable e f := by
  by_cases h : e = f
  · subst f; exact SimpleGraph.Reachable.refl e
  · exact (show (overlayLineGraph inc U).Adj e f from ⟨h,he,hf,v,hev,hfv⟩).reachable

lemma component_compatible (M N : Finset E) (anchor : E) :
    ExchangeCompatible (inc := inc) M N (componentEdges (inc := inc) (M ∪ N) anchor) := by
  intro e he f hf v hev hfv
  have heu := Finset.mem_union_left N he
  have hfu := Finset.mem_union_right M hf
  have hr := shares_reachable heu hfu hev hfv
  simp only [mem_componentEdges, heu, hfu, true_and]
  exact ⟨fun h => h.trans hr, fun h => h.trans hr.symm⟩

lemma component_exchange_matching [Fintype V] {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ) (anchor : E) :
    MatchingOn inc (exchange M N (componentEdges (inc := inc) (M ∪ N) anchor)) Finset.univ :=
  exchange_matching hM hN (component_compatible M N anchor)

lemma component_exchange_involution (M N : Finset E) (anchor : E) :
    let S := componentEdges (inc := inc) (M ∪ N) anchor
    exchange (exchange M N S) (exchange N M S)
      (componentEdges (inc := inc) (exchange M N S ∪ exchange N M S) anchor) = M := by
  dsimp only
  rw [exchange_union, exchange_involution]

end MatchingFPRAS.Transport

end OAI
