import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.IntervalPattern

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*} [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable def components (U : Finset E) : Finset (Finset E) := by
  classical
  exact U.image (componentEdges (inc := inc) U)

lemma mem_components {U S : Finset E} :
    S ∈ components (inc := inc) U ↔ ∃ a ∈ U, componentEdges (inc := inc) U a = S := by
  classical
  simp only [components, Finset.mem_image]

omit [DecidableEq E] in
lemma componentEdges_subset (U : Finset E) (a : E) : componentEdges (inc := inc) U a ⊆ U := by
  intro e he
  exact ((mem_componentEdges U a e).mp he).1

omit [DecidableEq E] in
lemma componentEdges_self {U : Finset E} {a : E} (ha : a ∈ U) :
    a ∈ componentEdges (inc := inc) U a :=
  (mem_componentEdges U a a).mpr ⟨ha,SimpleGraph.Reachable.refl a⟩

omit [DecidableEq E] in
lemma componentEdges_eq {U : Finset E} {a b : E}
    (hab : (overlayLineGraph inc U).Reachable a b) :
    componentEdges (inc := inc) U a = componentEdges (inc := inc) U b := by
  ext e
  simp only [mem_componentEdges]
  exact and_congr_right (fun _ => ⟨fun h => hab.symm.trans h, fun h => hab.trans h⟩)

lemma component_nonempty {U S : Finset E} (hS : S ∈ components (inc := inc) U) : S.Nonempty := by
  obtain ⟨a,ha,rfl⟩ := mem_components.mp hS
  exact ⟨a,componentEdges_self ha⟩

lemma component_subset {U S : Finset E} (hS : S ∈ components (inc := inc) U) : S ⊆ U := by
  obtain ⟨a,ha,rfl⟩ := mem_components.mp hS
  exact componentEdges_subset U a

lemma component_eq_of_shares {U S T : Finset E}
    (hS : S ∈ components (inc := inc) U) (hT : T ∈ components (inc := inc) U)
    {e f : E} (he : e ∈ S) (hf : f ∈ T) {v : V} (hev : inc e v) (hfv : inc f v) : S=T := by
  obtain ⟨a,ha,rfl⟩ := mem_components.mp hS
  obtain ⟨b,hb,rfl⟩ := mem_components.mp hT
  obtain ⟨heu,hra⟩ := (mem_componentEdges U a e).mp he
  obtain ⟨hfu,hrb⟩ := (mem_componentEdges U b f).mp hf
  exact componentEdges_eq ((hra.trans (shares_reachable heu hfu hev hfv)).trans hrb.symm)

lemma components_pairwise_disjoint (U : Finset E) :
    (components (inc := inc) U : Set (Finset E)).PairwiseDisjoint id := by
  intro S hS T hT hne
  apply Finset.disjoint_left.mpr
  intro e he hf
  apply hne
  obtain ⟨a,ha,rfl⟩ := mem_components.mp hS
  obtain ⟨b,hb,rfl⟩ := mem_components.mp hT
  obtain ⟨_,hra⟩ := (mem_componentEdges U a e).mp he
  obtain ⟨_,hrb⟩ := (mem_componentEdges U b e).mp hf
  exact componentEdges_eq (hra.trans hrb.symm)

lemma components_cover (U : Finset E) : (components (inc := inc) U).biUnion id = U := by
  classical
  ext e
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨S,hS,he⟩
    exact component_subset hS he
  · intro he
    exact ⟨componentEdges (inc := inc) U e, mem_components.mpr ⟨e,he,rfl⟩,
      componentEdges_self he⟩

lemma component_exists_vertex (hinc : ∀ e, ∃ v, inc e v)
    {U S : Finset E} (hS : S ∈ components (inc := inc) U) :
    ∃ v, ∃ e ∈ S, inc e v := by
  obtain ⟨e,he⟩ := component_nonempty hS
  obtain ⟨v,hv⟩ := hinc e
  exact ⟨v,e,he,hv⟩

noncomputable def componentVertex (hinc : ∀ e, ∃ v, inc e v)
    {U : Finset E} (S : ↥(components (inc := inc) U)) : V :=
  (component_exists_vertex hinc S.property).choose

lemma componentVertex_injective (hinc : ∀ e, ∃ v, inc e v) (U : Finset E) :
    Function.Injective (componentVertex hinc (U := U)) := by
  intro S T h
  obtain ⟨e,he,hev⟩ := (component_exists_vertex hinc S.property).choose_spec
  obtain ⟨f,hf,hfv⟩ := (component_exists_vertex hinc T.property).choose_spec
  apply Subtype.ext
  apply component_eq_of_shares S.property T.property he hf hev
  change inc f (componentVertex hinc T) at hfv
  change inc f (componentVertex hinc S)
  rwa [h]

lemma components_card_le [Fintype V] (hinc : ∀ e, ∃ v, inc e v) (U : Finset E) :
    (components (inc := inc) U).card ≤ Fintype.card V := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective (componentVertex hinc (U := U)) (componentVertex_injective hinc U)

lemma component_exchange_compatible {M N S : Finset E}
    (hS : S ∈ components (inc := inc) (M ∪ N)) : ExchangeCompatible (inc := inc) M N S := by
  obtain ⟨a,_,rfl⟩ := mem_components.mp hS
  exact component_compatible M N a



namespace IndexedCycle

variable (c : IndexedCycle inc)

noncomputable def edgeSet : Finset E := Finset.univ.image c.edge

lemma mem_edgeSet (e : E) : e ∈ c.edgeSet ↔ ∃ i, i < c.size ∧ c.edgeAt i = e := by
  simp only [edgeSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.val,i.isLt,by simp [edgeAt,index,Nat.mod_eq_of_lt i.isLt]⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨c.index i,rfl⟩

lemma edgeAt_mem_edgeSet (i : ℕ) : c.edgeAt i ∈ c.edgeSet := by
  apply (c.mem_edgeSet _).mpr
  exact ⟨i % c.size,Nat.mod_lt _ (by have := c.four_le; omega), c.edgeAt_mod i⟩

lemma edgeSet_subset {U : Finset E} (hU : ∀ i, c.edgeAt i ∈ U) : c.edgeSet ⊆ U := by
  intro e he
  obtain ⟨i,_,rfl⟩ := (c.mem_edgeSet e).mp he
  exact hU i

omit [DecidableEq E] in
lemma previous_indices (i : ℕ) (hi : i < c.size) :
    let j := (i+c.size-1) % c.size
    c.index (j+1) = c.index i := by
  dsimp only
  apply Fin.ext
  dsimp only [index]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have he : i + c.size - 1 + 1 = i + c.size := by have := c.four_le; omega
  rw [he, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]

variable [Fintype V]

lemma edge_incident_cycle_mem {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) {e : E} (he : e ∈ M ∪ N)
    (i : ℕ) (hi : i < c.size) (hev : inc e (c.vertexAt i)) : e ∈ c.edgeSet := by
  let j := (i+c.size-1) % c.size
  have hj : j < c.size := Nat.mod_lt _ (by have := c.four_le; omega)
  have heq : c.edgeAt (j+1) = c.edgeAt i := congrArg c.edge (c.previous_indices i hi)
  have hvq : c.vertexAt (j+1) = c.vertexAt i := congrArg c.vertex (c.previous_indices i hi)
  have hji : c.edgeAt j ≠ c.edgeAt i := by rw [← heq]; exact c.consecutive_ne j hj
  have hiinc := (c.edgeAt_incidence i (c.vertexAt i)).mpr (Or.inl rfl)
  have hjinc : inc (c.edgeAt j) (c.vertexAt i) :=
    (c.edgeAt_incidence j _).mpr (Or.inr hvq.symm)
  have hcomp : c.edgeAt i ∈ M ↔ c.edgeAt j ∉ M := by
    rw [← heq]; exact c.adjacent_mem_complement hM hN hU j hj
  by_cases hjM : c.edgeAt j ∈ M
  · have hiN : c.edgeAt i ∈ N :=
      (Finset.mem_union.mp (hU i)).resolve_left (fun hiM => (hcomp.mp hiM) hjM)
    rcases Finset.mem_union.mp he with heM | heN
    · rw [hM.unique (Finset.mem_univ _) heM hev hjM hjinc]
      exact c.edgeAt_mem_edgeSet j
    · rw [hN.unique (Finset.mem_univ _) heN hev hiN hiinc]
      exact c.edgeAt_mem_edgeSet i
  · have hjN := (Finset.mem_union.mp (hU j)).resolve_left hjM
    have hiM := hcomp.mpr hjM
    rcases Finset.mem_union.mp he with heM | heN
    · rw [hM.unique (Finset.mem_univ _) heM hev hiM hiinc]
      exact c.edgeAt_mem_edgeSet i
    · rw [hN.unique (Finset.mem_univ _) heN hev hjN hjinc]
      exact c.edgeAt_mem_edgeSet j

lemma edgeSet_closed {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) {e f : E} (he : e ∈ c.edgeSet)
    (hef : (overlayLineGraph inc (M ∪ N)).Adj e f) : f ∈ c.edgeSet := by
  obtain ⟨i,hi,rfl⟩ := (c.mem_edgeSet e).mp he
  obtain ⟨_,_,hf,v,hev,hfv⟩ := hef
  rcases (c.edgeAt_incidence i v).mp hev with rfl | rfl
  · exact c.edge_incident_cycle_mem hM hN hU hf i hi hfv
  · have hi' : (i+1) % c.size < c.size := Nat.mod_lt _ (by have := c.four_le; omega)
    apply c.edge_incident_cycle_mem hM hN hU hf ((i+1)%c.size) hi'
    simpa only [c.vertexAt_mod] using hfv

lemma edgeSet_eq_component {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) :
    c.edgeSet = componentEdges (inc := inc) (M ∪ N) (c.edgeAt 0) := by
  ext e
  constructor
  · intro he
    obtain ⟨i,hi,rfl⟩ := (c.mem_edgeSet e).mp he
    exact (mem_componentEdges _ _ _).mpr ⟨hU i,c.edges_reachable _ hU i⟩
  · intro he
    obtain ⟨heu,hr⟩ := (mem_componentEdges _ _ _).mp he
    have hrel := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hr
    clear he heu hr
    induction hrel with
    | refl => exact c.edgeAt_mem_edgeSet 0
    | tail hpath hadj ih => exact c.edgeSet_closed hM hN hU ih hadj

lemma edgeSet_mem_components {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) : c.edgeSet ∈ components (inc := inc) (M ∪ N) := by
  rw [c.edgeSet_eq_component hM hN hU]
  exact mem_components.mpr ⟨c.edgeAt 0,hU 0,rfl⟩

lemma inter_edgeSet_parity {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) :
    M ∩ c.edgeSet = c.parityPattern (if c.edgeAt 0 ∈ M then 0 else 1) := by
  classical
  ext e
  simp only [Finset.mem_inter, c.mem_edgeSet, parityPattern, mem_intervalPattern]
  constructor
  · rintro ⟨heM,i,hi,rfl⟩
    refine ⟨i, Nat.zero_le _,hi,?_,rfl⟩
    have hp := (c.cycle_edge_mem_parity hM hN hU i).mp heM
    split_ifs at hp ⊢ <;> first | omega | tauto
  · rintro ⟨i,_,hi,hpar,rfl⟩
    refine ⟨?_, i,hi,rfl⟩
    apply (c.cycle_edge_mem_parity hM hN hU i).mpr
    split_ifs at hpar ⊢ <;> omega

end IndexedCycle

end

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

namespace CellPaths

variable (c : CellPaths inc)

lemma mem_assemble_iff (M : Fin 4 → Finset E) (e : E) :
    e ∈ assemble M ↔ ∃ i, e ∈ M i := by
  simp only [assemble, Finset.mem_union]
  constructor
  · rintro ((h | h) | (h | h))
    · exact ⟨0,h⟩
    · exact ⟨2,h⟩
    · exact ⟨1,h⟩
    · exact ⟨3,h⟩
  · rintro ⟨i,hi⟩
    fin_cases i <;> tauto

lemma assemble_update (M : Fin 4 → Finset E)
    (hd : Pairwise fun i j => Disjoint (M i) (M j)) (i : Fin 4) (Q : Finset E) :
    assemble (Function.update M i Q) = (assemble M \ M i) ∪ Q := by
  ext e
  simp only [mem_assemble_iff, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨j,hj⟩
    by_cases hji : j = i
    · subst j
      exact Or.inr (by simpa using hj)
    · have hj' : e ∈ M j := by simpa [Function.update_of_ne hji] using hj
      exact Or.inl ⟨⟨j,hj'⟩, fun hi => Finset.disjoint_left.mp (hd hji) hj' hi⟩
  · rintro (⟨⟨j,hj⟩,hi⟩ | hq)
    · have hji : j ≠ i := by rintro rfl; exact hi hj
      exact ⟨j, by simpa [Function.update_of_ne hji] using hj⟩
    · exact ⟨i, by simpa using hq⟩

def conversionPieces (b : Bool) (S : Finset (Fin 4)) (i : Fin 4) : Finset E :=
  if i ∈ S then (c.side i).closed (c.chord i) else c.orientationPieces b i

def converted (b : Bool) (S : Finset (Fin 4)) : Finset E :=
  assemble (c.conversionPieces b S)

lemma conversion_pieces_matching (b : Bool) (S : Finset (Fin 4))
    (hS : ∀ i ∈ S, sideBit i = b) (i : Fin 4) :
    MatchingOn inc (c.conversionPieces b S i) (c.blocks b i) := by
  by_cases hi : i ∈ S
  · simp only [conversionPieces, ite_eq_left hi, blocks, ite_eq_left (hS i hi)]
    exact (c.side i).closed_matching _ (c.chord_incidence i)
  · simp only [conversionPieces, ite_eq_right hi]
    exact c.orientation_pieces_matching b i

lemma converted_matching (b : Bool) (S : Finset (Fin 4))
    (hS : ∀ i ∈ S, sideBit i = b) :
    MatchingOn inc (c.converted b S) c.vertices :=
  c.assembled_matching b _ (c.conversion_pieces_matching b S hS)

lemma converted_empty (b : Bool) : c.converted b ∅ = c.orientation b := by
  unfold converted orientation
  congr 1

lemma conversion_pieces_insert (b : Bool) (S : Finset (Fin 4)) (i : Fin 4) :
    c.conversionPieces b (insert i S) =
      Function.update (c.conversionPieces b S) i ((c.side i).closed (c.chord i)) := by
  funext j
  by_cases hji : j = i
  · subst j; simp [conversionPieces]
  · simp [conversionPieces, hji]

lemma converted_insert (b : Bool) (S : Finset (Fin 4))
    (hS : ∀ j ∈ S, sideBit j = b) (i : Fin 4) (hi : sideBit i = b)
    (hni : i ∉ S) (hinc : ∀ e, ∃ v, inc e v) :
    c.converted b (insert i S) =
      (c.converted b S \ (c.side i).through) ∪ (c.side i).closed (c.chord i) := by
  rw [converted, c.conversion_pieces_insert]
  rw [assemble_update]
  · simp only [conversionPieces, ite_eq_right hni, orientationPieces, pieces, ite_eq_left hi, converted]
  · intro j k hjk
    exact (c.conversion_pieces_matching b S hS j).disjoint_edges
      (c.conversion_pieces_matching b S hS k) hinc (c.blocks_disjoint b hjk)

lemma converted_singleton (b : Bool) (i : Fin 4) (hi : sideBit i = b)
    (hinc : ∀ e, ∃ v, inc e v) :
    c.converted b {i} = c.contextOne b i := by
  have h := c.converted_insert b ∅ (by simp) i hi (by simp) hinc
  simpa only [converted_empty, Finset.insert_empty, contextOne] using h

lemma converted_pair (b : Bool) (X Y : Fin 4)
    (hX : sideBit X = b) (hY : sideBit Y = b) (hne : X ≠ Y) :
    c.converted b {X,Y} = c.switched b := by
  unfold converted switched
  congr 1
  funext i
  have hh : i ∈ ({X,Y} : Finset (Fin 4)) ↔ sideBit i = b := by
    fin_cases X <;> fin_cases Y <;> fin_cases i <;> cases b <;>
      simp_all [sideBit]
  simp only [conversionPieces, hh, switchPieces, pieces, orientationPieces]
  split_ifs <;> rfl

lemma double_conversion (b : Bool) (X Y : Fin 4)
    (hX : sideBit X = b) (hY : sideBit Y = b) (hne : X ≠ Y)
    (hinc : ∀ e, ∃ v, inc e v) :
    (c.contextOne b Y \ (c.side X).through) ∪ (c.side X).closed (c.chord X) =
      c.switched b := by
  rw [← c.converted_singleton b Y hY hinc, ← c.converted_insert b {Y}
    (by intro i hi; have hi := Finset.mem_singleton.mp hi; subst i; exact hY) X hX
    (by simpa only [Finset.mem_singleton] using hne) hinc]
  exact c.converted_pair b X Y hX hY hne

def canonicalGain (R : Finset E) (f : Finset E → ℝ) (b : Bool) (i : Fin 4) : ℝ :=
  f (R ∪ c.orientation b) - f (R ∪ c.contextOne b i)

def contextError (R : Finset E) (f : Finset E → ℝ) (b : Bool) (X Y : Fin 4) : ℝ :=
  (f (R ∪ c.contextOne b Y) -
    f (R ∪ ((c.contextOne b Y \ (c.side X).through) ∪ (c.side X).closed (c.chord X)))) -
  (f (R ∪ c.orientation b) - f (R ∪ c.contextOne b X))

lemma opposite_pair_identity (R : Finset E) (f : Finset E → ℝ) (b : Bool)
    (X Y : Fin 4) (hX : sideBit X = b) (hY : sideBit Y = b) (hne : X ≠ Y)
    (hinc : ∀ e, ∃ v, inc e v) :
    f (R ∪ c.orientation b) - f (R ∪ c.switched b) =
      c.canonicalGain R f b Y + c.canonicalGain R f b X + c.contextError R f b X Y := by
  rw [contextError, c.double_conversion b X Y hX hY hne hinc]
  unfold canonicalGain
  ring

theorem single_cell_identity (R : Finset E) (f : Finset E → ℝ)
    (hinc : ∀ e, ∃ v, inc e v) :
    f (R ∪ c.orientation true) - f (R ∪ c.orientation false) =
      (f (R ∪ c.switched true) - f (R ∪ c.switched false)) +
      (c.canonicalGain R f true 0 + c.canonicalGain R f true 2) -
      (c.canonicalGain R f false 1 + c.canonicalGain R f false 3) +
      c.contextError R f true 2 0 - c.contextError R f false 3 1 := by
  have h₀ := c.opposite_pair_identity R f true 2 0 (by decide) (by decide) (by decide) hinc
  have h₁ := c.opposite_pair_identity R f false 3 1 (by decide) (by decide) (by decide) hinc
  linarith

end CellPaths

end MatchingFPRAS.Transport

end OAI
