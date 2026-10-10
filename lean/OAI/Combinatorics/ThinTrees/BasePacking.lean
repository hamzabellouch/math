import OAI.Combinatorics.ThinTrees.HierarchyBounds

namespace OAI

universe uE uI uV uI2

section

noncomputable section
open Finset Submodule
namespace StrongThinTree.Packing

variable {E : Type uE} {I : Type uI} {V : Type uV} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

abbrev span (v : E → V) (s : Finset E) : Submodule ℝ V :=
  Submodule.span ℝ (v '' (s : Set E))

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_mono (v : E → V) {s t : Finset E} (h : s ⊆ t) : span v s ≤ span v t :=
  Submodule.span_mono (Set.image_mono h)

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma span_insert (v : E → V) (s : Finset E) (e : E) :
    span v (insert e s) = Submodule.span ℝ (insert (v e) (v '' (s : Set E))) := by
  simp only [span, coe_insert, Set.image_insert_eq]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma mem_span_self (v : E → V) {s : Finset E} {e : E} (he : e ∈ s) :
    v e ∈ span v s := Submodule.subset_span ⟨e, he, rfl⟩

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_le_iff (v : E → V) {s : Finset E} {W : Submodule ℝ V} :
    span v s ≤ W ↔ ∀ e ∈ s, v e ∈ W := by
  rw [Submodule.span_le]
  constructor
  · intro h e he; exact h ⟨e, he, rfl⟩
  · rintro h x ⟨e, he, rfl⟩; exact h e he

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma indep_rank (v : E → V) {s : Finset E} (hs : LinearIndepOn ℝ v s) :
    Module.finrank ℝ (span v s) = s.card := by
  have heq : Set.range (fun e : (s : Set E) => v e) = v '' (s : Set E) := by
    ext x; simp
  have h := finrank_span_eq_card hs.linearIndependent
  change Module.finrank ℝ (Submodule.span ℝ (Set.range (fun e : (s : Set E) => v e))) = _ at h
  rw [heq] at h
  simpa using h

omit [Fintype E] [FiniteDimensional ℝ V] in

lemma support_exchange (v : E → V) {s : Finset E}
    (hs : LinearIndepOn ℝ v s) {x : V} {l : E →₀ ℝ}
    (hl : l ∈ Finsupp.supported ℝ ℝ (s : Set E))
    (hx : Finsupp.linearCombination ℝ v l = x) {f : E} (hf : f ∈ l.support) :
    x ∉ span v (s.erase f) := by
  intro h
  obtain ⟨l', hl', hx'⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp h
  have hl's : l' ∈ Finsupp.supported ℝ ℝ (s : Set E) := by
    rw [Finsupp.mem_supported] at hl' ⊢
    exact hl'.trans (Finset.erase_subset _ _)
  have heq : l = l' := (linearIndepOn_iffₛ.mp hs) l hl l' hl's (hx.trans hx'.symm)
  have hz : l' f = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have := ((Finsupp.mem_supported ℝ l').mp hl') hmem
    simp at this
  exact (Finsupp.mem_support_iff.mp hf) (heq ▸ hz)

def Valid (v : E → V) (F : I → Finset E) : Prop :=
  (∀ i, LinearIndepOn ℝ v (F i : Set E)) ∧ Pairwise (fun i j => Disjoint (F i) (F j))

abbrev State (v : E → V) (I : Type uI2) [Fintype I] := {F : I → Finset E // Valid v F}

def cost {v : E → V} (F : State v I) : ℕ := ∑ i, (F.1 i).card

def unused {v : E → V} (F : State v I) (e : E) : Prop := ∀ i, e ∉ F.1 i

omit [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma valid_empty (v : E → V) : Valid v (fun _ : I => ∅) := by
  constructor
  · intro i; simp
  · intro i j h; simp

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma valid_update {v : E → V} (F : State v I) (i : I) (s : Finset E)
    (hs : LinearIndepOn ℝ v (s : Set E))
    (hd : ∀ j, j ≠ i → Disjoint s (F.1 j)) : Valid v (Function.update F.1 i s) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j; simpa using hs
    · simpa [Function.update_of_ne h] using F.2.1 j
  · intro j k hjk
    by_cases hj : j = i
    · subst j
      simpa [Function.update_of_ne (Ne.symm hjk)] using hd k (Ne.symm hjk)
    · by_cases hk : k = i
      · subst k
        simpa [Function.update_of_ne hj] using (hd j hj).symm
      · simpa [Function.update_of_ne hj, Function.update_of_ne hk] using F.2.2 hjk

omit [Fintype E] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma disjoint_insert_unused {v : E → V} (F : State v I) {i : I} {s : Finset E}
    (hs : s ⊆ F.1 i) {e : E} (he : unused F e) :
    ∀ j, j ≠ i → Disjoint (insert e s) (F.1 j) := by
  intro j hj
  rw [Finset.disjoint_insert_left]
  exact ⟨he j, (F.2.2 (Ne.symm hj)).mono_left hs⟩

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma cost_update {v : E → V} (F : State v I) {i : I} {s : Finset E}
    (h : Valid v (Function.update F.1 i s)) :
    cost (⟨Function.update F.1 i s, h⟩ : State v I) + (F.1 i).card = cost F + s.card := by
  unfold cost
  have hsum := Finset.sum_update_of_mem (Finset.mem_univ i) (fun j => (F.1 j).card) s.card
  have heq : (fun j => ((Function.update F.1 i s) j).card) =
      Function.update (fun j => (F.1 j).card) i s.card := by
    ext j; by_cases hj : j = i <;> simp [hj, Function.update_of_ne]
  rw [heq]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ : Finset I) _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have he : ∑ j ∈ Finset.univ.erase i,
      Function.update (fun j => (F.1 j).card) i s.card j =
      ∑ j ∈ Finset.univ.erase i, (F.1 j).card := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  rw [he]
  omega

omit [DecidableEq E] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma exists_maximal_state (v : E → V) :
    ∃ F : State v I, ∀ F' : State v I, cost F' ≤ cost F := by
  classical
  let : Fintype (State v I) := Fintype.ofFinite _
  have hne : (Finset.univ : Finset (State v I)).Nonempty :=
    ⟨⟨fun _ => ∅, valid_empty v⟩, Finset.mem_univ _⟩
  obtain ⟨F, _, hF⟩ := Finset.exists_max_image (Finset.univ : Finset (State v I)) cost hne
  exact ⟨F, fun F' => hF F' (Finset.mem_univ _)⟩

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma maximal_unused_mem_span {v : E → V} {F : State v I}
    (hF : ∀ F' : State v I, cost F' ≤ cost F) {e : E} (he : unused F e) (i : I) :
    v e ∈ span v (F.1 i) := by
  by_contra h
  have hs : LinearIndepOn ℝ v (insert e (F.1 i) : Finset E) := by
    simpa only [Finset.coe_insert] using (F.2.1 i).insert h
  have hv := valid_update F i _ hs (disjoint_insert_unused F (Subset.refl _) he)
  have hc := cost_update F hv
  have hu := hF ⟨_, hv⟩
  rw [Finset.card_insert_of_notMem (he i)] at hc
  omega

def Move {v : E → V} (F F' : State v I) : Prop :=
  ∃ i e f, unused F e ∧ f ∈ F.1 i ∧
    F'.1 = Function.update F.1 i (insert e ((F.1 i).erase f))

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma unused_after_exchange {v : E → V} {F F' : State v I} {i : I} {e f : E}
    (he : unused F e) (hf : f ∈ F.1 i)
    (h : F'.1 = Function.update F.1 i (insert e ((F.1 i).erase f))) : unused F' f := by
  intro j
  rw [h]
  by_cases hj : j = i
  · subst j
    have hfe : f ≠ e := by rintro rfl; exact he i hf
    simp [hfe]
  · rw [Function.update_of_ne hj]
    exact fun hfj => Finset.disjoint_left.mp (F.2.2 (Ne.symm hj)) hf hfj

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma Move.cost_eq {v : E → V} {F F' : State v I} (h : Move F F') : cost F' = cost F := by
  obtain ⟨i, e, f, he, hf, heq⟩ := h
  have hv : Valid v (Function.update F.1 i (insert e ((F.1 i).erase f))) := heq ▸ F'.2
  have hc := cost_update F hv
  have hsame : (⟨_, hv⟩ : State v I) = F' := Subtype.ext heq.symm
  rw [hsame, Finset.card_insert_of_notMem (fun hh => he i (Finset.mem_erase.mp hh).2),
    Finset.card_erase_of_mem hf] at hc
  have hfpos := Finset.card_pos.mpr ⟨f, hf⟩
  omega

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma reachable_cost_eq {v : E → V} {F F' : State v I}
    (h : Relation.ReflTransGen Move F F') : cost F' = cost F := by
  induction h with
  | refl => rfl
  | @tail F' F'' hr hm ih => exact hm.cost_eq.trans ih

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma reachable_maximal {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (h : Relation.ReflTransGen Move F F') : ∀ G : State v I, cost G ≤ cost F' := by
  intro G
  rw [reachable_cost_eq h]
  exact hF G

def recycled {v : E → V} (F : State v I) : Finset E := by
  classical
  exact Finset.univ.filter fun e => ∃ F', Relation.ReflTransGen Move F F' ∧ unused F' e

omit [FiniteDimensional ℝ V] in
lemma mem_recycled {v : E → V} {F : State v I} {e : E} :
    e ∈ recycled F ↔ ∃ F', Relation.ReflTransGen Move F F' ∧ unused F' e := by
  classical
  simp [recycled]

omit [FiniteDimensional ℝ V] in
lemma unused_span_recycled {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') {e : E} (he : unused F' e) (i : I) :
    v e ∈ span v (F'.1 i ∩ recycled F) := by
  have hsp := maximal_unused_mem_span (reachable_maximal hF hr) he i
  obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp hsp
  apply (Finsupp.mem_span_image_iff_linearCombination ℝ).mpr
  refine ⟨l, ?_, hle⟩
  rw [Finsupp.mem_supported]
  intro f hf
  have hfi : f ∈ F'.1 i := (Finsupp.mem_supported ℝ l).mp hl hf
  refine Finset.mem_inter.mpr ⟨hfi, mem_recycled.mpr ?_⟩
  have hex := support_exchange v (F'.2.1 i) hl hle hf
  have hs : LinearIndepOn ℝ v (insert e ((F'.1 i).erase f) : Finset E) := by
    simpa only [Finset.coe_insert] using
      ((F'.2.1 i).mono (Finset.erase_subset _ _)).insert hex
  have hv := valid_update F' i _ hs
    (disjoint_insert_unused F' (Finset.erase_subset _ _) he)
  let F'' : State v I := ⟨_, hv⟩
  have hm : Move F' F'' := ⟨i, e, f, he, hfi, rfl⟩
  exact ⟨F'', hr.tail hm, unused_after_exchange he hfi rfl⟩

omit [FiniteDimensional ℝ V] in
lemma move_span_recycled_eq {v : E → V} {F F' F'' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') (hm : Move F' F'') (j : I) :
    span v (F''.1 j ∩ recycled F) = span v (F'.1 j ∩ recycled F) := by
  obtain ⟨i, e, f, he, hf, hup⟩ := hm
  by_cases hji : j = i
  · subst j
    have heU : v e ∈ span v (F'.1 i ∩ recycled F) := unused_span_recycled hF hr he i
    have hfU : v f ∈ span v (F''.1 i ∩ recycled F) :=
      unused_span_recycled hF (hr.tail ⟨i, e, f, he, hf, hup⟩)
        (unused_after_exchange he hf hup) i
    apply le_antisymm
    · apply (span_le_iff v).mpr
      intro g hg
      have hgU := (Finset.mem_inter.mp hg).2
      have hg' := (Finset.mem_inter.mp hg).1
      rw [hup, Function.update_self] at hg'
      rcases Finset.mem_insert.mp hg' with rfl | hg'
      · exact heU
      · exact mem_span_self v (Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hg').2, hgU⟩)
    · apply (span_le_iff v).mpr
      intro g hg
      by_cases hgf : g = f
      · subst g; exact hfU
      · apply mem_span_self v
        apply Finset.mem_inter.mpr
        refine ⟨?_, (Finset.mem_inter.mp hg).2⟩
        rw [hup, Function.update_self]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hgf, (Finset.mem_inter.mp hg).1⟩)
  · rw [hup, Function.update_of_ne hji]

omit [FiniteDimensional ℝ V] in
lemma reachable_span_recycled_eq {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') (i : I) :
    span v (F'.1 i ∩ recycled F) = span v (F.1 i ∩ recycled F) := by
  induction hr with
  | refl => rfl
  | @tail F' F'' hr hm ih => exact (move_span_recycled_eq hF hr hm i).trans ih

omit [FiniteDimensional ℝ V] in

lemma span_recycled_eq {v : E → V} {F : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F) (i : I) :
    span v (recycled F) = span v (F.1 i ∩ recycled F) := by
  apply le_antisymm
  · apply (span_le_iff v).mpr
    intro e he
    obtain ⟨F', hr, he'⟩ := mem_recycled.mp he
    rw [← reachable_span_recycled_eq hF hr i]
    exact unused_span_recycled hF hr he' i
  · exact span_mono v Finset.inter_subset_right

omit [FiniteDimensional ℝ V] in
lemma cost_decomposition {v : E → V} {F : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F) :
    cost F = (Finset.univ \ recycled F).card +
      Fintype.card I * Module.finrank ℝ (span v (recycled F)) := by
  classical
  have hcover : Finset.univ \ recycled F =
      Finset.univ.biUnion (fun i => F.1 i \ recycled F) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro he
      have hused : ∃ i, e ∈ F.1 i := by
        by_contra h
        have hu : unused F e := by simpa only [unused, not_exists] using h
        exact he (mem_recycled.mpr ⟨F, Relation.ReflTransGen.refl, hu⟩)
      obtain ⟨i, hi⟩ := hused
      exact ⟨i, hi, he⟩
    · rintro ⟨i, hi, he⟩; exact he
  have hdisj : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => F.1 i \ recycled F) := by
    intro i _ j _ hij
    exact (F.2.2 hij).mono Finset.sdiff_subset Finset.sdiff_subset
  have hrank (i : I) : (F.1 i ∩ recycled F).card =
      Module.finrank ℝ (span v (recycled F)) := by
    rw [span_recycled_eq hF i]
    exact (indep_rank v ((F.2.1 i).mono Finset.inter_subset_left)).symm
  rw [hcover, Finset.card_biUnion hdisj]
  calc
    cost F = ∑ i, ((F.1 i \ recycled F).card + (F.1 i ∩ recycled F).card) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.card_sdiff_add_card_inter _ _).symm
    _ = (∑ i, (F.1 i \ recycled F).card) +
        Fintype.card I * Module.finrank ℝ (span v (recycled F)) := by
      simp_rw [hrank, Finset.sum_add_distrib]
      simp

theorem vector_base_packing (v : E → V)
    (hcut : ∀ U : Finset E,
      Fintype.card I * Module.finrank ℝ (span v Finset.univ) ≤
        (Finset.univ \ U).card + Fintype.card I * Module.finrank ℝ (span v U)) :
    ∃ F : State v I, ∀ i, span v (F.1 i) = span v Finset.univ := by
  obtain ⟨F, hF⟩ := exists_maximal_state (I := I) v
  have hle (i : I) : (F.1 i).card ≤ Module.finrank ℝ (span v Finset.univ) := by
    rw [← indep_rank v (F.2.1 i)]
    exact Submodule.finrank_mono (span_mono v (Finset.subset_univ _))
  have htotal : cost F = Fintype.card I * Module.finrank ℝ (span v Finset.univ) := by
    apply le_antisymm
    · calc
        cost F ≤ ∑ _i : I, Module.finrank ℝ (span v Finset.univ) :=
          Finset.sum_le_sum fun i _ => hle i
        _ = _ := by simp
    · rw [cost_decomposition hF]
      exact hcut (recycled F)
  have hcards (i : I) : (F.1 i).card = Module.finrank ℝ (span v Finset.univ) := by
    apply (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset I)) => hle i)).mp ?_ i
      (Finset.mem_univ i)
    simpa [cost] using htotal
  refine ⟨F, fun i => ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq (span_mono v (Finset.subset_univ _))
  rw [indep_rank v (F.2.1 i), hcards]

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma masked_span (v : E → V) (T U : Finset E) :
    span (fun e => if e ∈ T then v e else 0) U = span v (U ∩ T) := by
  classical
  apply le_antisymm
  · apply (span_le_iff _).mpr
    intro e he
    by_cases heT : e ∈ T
    · simp only [ite_eq_left heT]
      exact mem_span_self v (Finset.mem_inter.mpr ⟨he, heT⟩)
    · simp [heT]
  · apply (span_le_iff _).mpr
    intro e he
    have hm := mem_span_self (fun e => if e ∈ T then v e else 0) (Finset.mem_inter.mp he).1
    simpa only [ite_eq_left (Finset.mem_inter.mp he).2] using hm

theorem vector_base_packing_on (v : E → V) (T : Finset E)
    (hcut : ∀ U : Finset E, U ⊆ T →
      Fintype.card I * Module.finrank ℝ (span v T) ≤
        (T \ U).card + Fintype.card I * Module.finrank ℝ (span v U)) :
    ∃ F : I → Finset E, Valid v F ∧ ∀ i, F i ⊆ T ∧ span v (F i) = span v T := by
  classical
  let w : E → V := fun e => if e ∈ T then v e else 0
  have hcrit : ∀ U : Finset E, Fintype.card I * Module.finrank ℝ (span w Finset.univ) ≤
      (Finset.univ \ U).card + Fintype.card I * Module.finrank ℝ (span w U) := by
    intro U
    have hw (A : Finset E) : span w A = span v (A ∩ T) := masked_span v T A
    rw [hw, hw, Finset.univ_inter]
    have h := hcut (U ∩ T) Finset.inter_subset_right
    apply h.trans
    apply Nat.add_le_add_right
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and] at he ⊢
    tauto
  obtain ⟨F, hF⟩ := vector_base_packing (I := I) w hcrit
  have hsub (i : I) : F.1 i ⊆ T := by
    intro e he
    have hz := (F.2.1 i).ne_zero he
    by_contra h
    exact hz (by simp [w, h])
  refine ⟨F.1, ⟨?_, F.2.2⟩, fun i => ⟨hsub i, ?_⟩⟩
  · intro i
    apply (F.2.1 i).congr
    intro e he
    simp [w, hsub i he]
  · have heq := hF i
    simpa only [w, masked_span, Finset.inter_eq_left.mpr (hsub i), Finset.univ_inter] using heq

end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

abbrev edgeSpan (T : Finset (Fin m)) := Packing.span G.incidence T

def Same (T : Finset (Fin m)) (u v : Fin n) : Prop :=
  point u - point v ∈ G.edgeSpan T

lemma same_refl (T : Finset (Fin m)) (u : Fin n) : G.Same T u u := by
  simp [Same]

lemma same_symm {T : Finset (Fin m)} {u v : Fin n} (h : G.Same T u v) : G.Same T v u := by
  change point v - point u ∈ G.edgeSpan T
  simpa only [neg_sub] using (G.edgeSpan T).neg_mem h

lemma same_trans {T : Finset (Fin m)} {u v w : Fin n}
    (huv : G.Same T u v) (hvw : G.Same T v w) : G.Same T u w := by
  change point u - point w ∈ G.edgeSpan T
  simpa only [sub_add_sub_cancel] using (G.edgeSpan T).add_mem huv hvw

def components (T : Finset (Fin m)) : Setoid (Fin n) where
  r := G.Same T
  iseqv := ⟨G.same_refl T, G.same_symm, G.same_trans⟩

def rep (T : Finset (Fin m)) (u : Fin n) : Fin n := (Quotient.mk (G.components T) u).out

lemma rep_same (T : Finset (Fin m)) (u : Fin n) : G.Same T (G.rep T u) u :=
  Quotient.mk_out (s := G.components T) u

lemma rep_eq_iff (T : Finset (Fin m)) (u v : Fin n) : G.rep T u = G.rep T v ↔ G.Same T u v := by
  constructor
  · intro h
    exact G.same_trans (G.same_symm (G.rep_same T u)) (h ▸ G.rep_same T v)
  · intro h
    exact congrArg Quotient.out (Quotient.sound h)

lemma rep_idempotent (T : Finset (Fin m)) (u : Fin n) : G.rep T (G.rep T u) = G.rep T u :=
  (G.rep_eq_iff T _ _).mpr (G.rep_same T u)

lemma same_endpoints {T : Finset (Fin m)} {e : Fin m} (he : e ∈ T) :
    G.Same T (G.left e) (G.right e) := Packing.mem_span_self G.incidence he

lemma rep_endpoints {T : Finset (Fin m)} {e : Fin m} (he : e ∈ T) :
    G.rep T (G.left e) = G.rep T (G.right e) :=
  (G.rep_eq_iff T _ _).mpr (G.same_endpoints he)

abbrev repDifference (T : Finset (Fin m)) (u : Fin n) : Fin n → ℝ :=
  point u - point (G.rep T u)

lemma repDifference_mem (T : Finset (Fin m)) (u : Fin n) : G.repDifference T u ∈ G.edgeSpan T :=
  G.same_symm (G.rep_same T u)

lemma repDifference_independent (T : Finset (Fin m)) :
    LinearIndependent ℝ (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun u => LinearMap.proj u.1)
  · intro u v huv
    have huv' : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    have hru : u.1 ≠ G.rep T v.1 := by
      intro h
      have := G.rep_idempotent T v.1
      rw [← h] at this
      exact u.2 this
    simp [repDifference, point, huv', hru]
  · intro u
    simp [repDifference, point, (Ne.symm u.2)]

lemma edgeSpan_eq_repSpan (T : Finset (Fin m)) :
    G.edgeSpan T = Submodule.span ℝ
      (Set.range (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u)) := by
  classical
  apply le_antisymm
  · apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have hdiff (u : Fin n) : G.repDifference T u ∈ Submodule.span ℝ
        (Set.range (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u)) := by
      by_cases hu : G.rep T u = u
      · simp [repDifference, hu]
      · exact Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩
    have h := (Submodule.span ℝ _).sub_mem (hdiff (G.left e)) (hdiff (G.right e))
    have heq : G.repDifference T (G.left e) - G.repDifference T (G.right e) = G.incidence e := by
      dsimp [repDifference, incidence]
      rw [G.rep_endpoints he]
      abel
    rwa [heq] at h
  · apply Submodule.span_le.mpr
    rintro x ⟨u, rfl⟩
    exact G.repDifference_mem T u

def componentCount (T : Finset (Fin m)) : ℕ := (Finset.univ.image (G.rep T)).card

theorem incidence_rank (T : Finset (Fin m)) :
    Module.finrank ℝ (G.edgeSpan T) = n - G.componentCount T := by
  classical
  rw [G.edgeSpan_eq_repSpan, finrank_span_eq_card (G.repDifference_independent T),
    Fintype.card_subtype_compl]
  have heq : Finset.univ.image (G.rep T) = Finset.univ.filter (fun u => G.rep T u = u) := by
    ext u
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨v, rfl⟩
      exact G.rep_idempotent T v
    · intro hu
      exact ⟨u, hu⟩
  simp only [componentCount, heq, Fintype.card_fin, Fintype.card_subtype]

lemma sumOn_point (S : Finset (Fin n)) (v : Fin n) :
    (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v) =
      if v ∈ S then 1 else 0 := by
  simp [LinearMap.sum_apply, point, Pi.single_apply, Finset.sum_ite_eq']

theorem connected_iff_same (T : Finset (Fin m)) :
    G.Connected T ↔ ∀ u v, G.Same T u v := by
  classical
  constructor
  · intro hconn u v
    by_contra huv
    let S := Finset.univ.filter (fun w => G.Same T w v)
    have hS : S.Nonempty := ⟨v, by simp [S, G.same_refl]⟩
    have hSne : S ≠ Finset.univ := by
      intro heq
      have hu : u ∈ S := heq ▸ Finset.mem_univ u
      exact huv (by simpa [S] using hu)
    obtain ⟨e, he⟩ := hconn S hS hSne
    obtain ⟨heT, hecut⟩ := Finset.mem_filter.mp he
    rcases hecut with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · have hl' : G.Same T (G.left e) v := by simpa [S] using hl
      have hr' := G.same_trans (G.same_symm (G.same_endpoints heT)) hl'
      exact hr (by simpa [S] using hr')
    · have hr' : G.Same T (G.right e) v := by simpa [S] using hr
      have hl' := G.same_trans (G.same_endpoints heT) hr'
      exact hl (by simpa [S] using hl')
  · intro hsame S hS hSne
    by_contra hcut
    have hempty : G.cut T S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcut
    let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ u ∈ S, LinearMap.proj u
    have hker : G.edgeSpan T ≤ LinearMap.ker f := by
      apply (Packing.span_le_iff G.incidence).mpr
      intro e he
      have hiff : G.left e ∈ S ↔ G.right e ∈ S := by
        have h : ¬ ((G.left e ∈ S ∧ G.right e ∉ S) ∨
            (G.right e ∈ S ∧ G.left e ∉ S)) := by
          intro hc
          have : e ∈ G.cut T S := Finset.mem_filter.mpr ⟨he, hc⟩
          simp [hempty] at this
        tauto
      change f (G.incidence e) = 0
      rw [incidence, map_sub]
      change (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.left e)) -
        (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.right e)) = 0
      simp only [sumOn_point]
      simp only [hiff, sub_self]
    obtain ⟨u, hu⟩ := hS
    have hv : ∃ v, v ∉ S := by
      by_contra h
      push Not at h
      exact hSne (Finset.eq_univ_of_forall h)
    obtain ⟨v, hv⟩ := hv
    have hz := hker (hsame u v)
    change f (point u - point v) = 0 at hz
    rw [map_sub] at hz
    change (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point u) -
      (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v) = 0 at hz
    simp [sumOn_point, hu, hv] at hz

lemma connected_of_span_eq {T U : Finset (Fin m)}
    (h : G.edgeSpan T = G.edgeSpan U) (hT : G.Connected T) : G.Connected U := by
  rw [G.connected_iff_same] at hT ⊢
  intro u v
  change point u - point v ∈ G.edgeSpan U
  rw [← h]
  exact hT u v

theorem spanningTree_iff_independent (T : Finset (Fin m)) :
    G.SpanningTree T ↔ G.Connected T ∧ LinearIndepOn ℝ G.incidence (T : Set (Fin m)) := by
  constructor
  · rintro ⟨hconn, hmin⟩
    refine ⟨hconn, linearIndepOn_iff_notMem_span.mpr ?_⟩
    intro e he hdep
    have hd : G.incidence e ∈ G.edgeSpan (T.erase e) := by
      simpa only [edgeSpan, Packing.span, Finset.coe_erase] using hdep
    have heq : G.edgeSpan T = G.edgeSpan (T.erase e) := by
      calc
        G.edgeSpan T = G.edgeSpan (insert e (T.erase e)) := by rw [Finset.insert_erase he]
        _ = G.edgeSpan (T.erase e) := by
          change Packing.span G.incidence (insert e (T.erase e)) = _
          rw [Packing.span_insert, Submodule.span_insert_eq_span hd]
    exact hmin e he (G.connected_of_span_eq heq hconn)
  · rintro ⟨hconn, hind⟩
    refine ⟨hconn, fun e he hdel => ?_⟩
    have hnot := linearIndepOn_iff_notMem_span.mp hind e he
    apply hnot
    have hsame := (G.connected_iff_same (T.erase e)).mp hdel (G.left e) (G.right e)
    simpa only [Same, incidence, edgeSpan, Packing.span, Finset.coe_erase] using hsame

lemma componentCount_pos (hn : 0 < n) (T : Finset (Fin m)) : 0 < G.componentCount T := by
  apply Finset.card_pos.mpr
  exact ⟨G.rep T ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩

lemma componentCount_le (T : Finset (Fin m)) : G.componentCount T ≤ n := by
  exact (Finset.card_image_le).trans_eq (Finset.card_univ.trans (Fintype.card_fin n))

lemma connected_componentCount {T : Finset (Fin m)} (hn : 0 < n) (hc : G.Connected T) :
    G.componentCount T = 1 := by
  apply Finset.card_eq_one.mpr
  let u : Fin n := ⟨0, hn⟩
  refine ⟨G.rep T u, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_singleton.mpr ((G.rep_eq_iff T w u).mpr ((G.connected_iff_same T).mp hc w u))
  · intro hv
    have hv' := Finset.mem_singleton.mp hv
    subst v
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

lemma connected_rank {T : Finset (Fin m)} (hn : 0 < n) (hc : G.Connected T) :
    Module.finrank ℝ (G.edgeSpan T) = n - 1 := by
  rw [G.incidence_rank, G.connected_componentCount hn hc]

lemma spanningTree_card {T : Finset (Fin m)} (hn : 0 < n) (hT : G.SpanningTree T) : T.card = n - 1 := by
  rw [← Packing.indep_rank G.incidence ((G.spanningTree_iff_independent T).mp hT).2]
  exact G.connected_rank hn hT.1

def crossing (T : Finset (Fin m)) (p : Fin n → Fin n) : Finset (Fin m) :=
  T.filter fun e => p (G.left e) ≠ p (G.right e)

def partitionSize (p : Fin n → Fin n) : ℕ := (Finset.univ.image p).card

def TreePackable (T : Finset (Fin m)) (r : ℕ) : Prop :=
  ∃ F : Fin r → Finset (Fin m),
    (∀ i, F i ⊆ T ∧ G.SpanningTree (F i)) ∧ Pairwise (fun i j => Disjoint (F i) (F j))

lemma connected_of_componentCount_eq_one {T : Finset (Fin m)}
    (hc : G.componentCount T = 1) : G.Connected T := by
  rw [G.connected_iff_same]
  have ⟨v, hv⟩ := Finset.card_eq_one.mp hc
  intro a b
  have ha : G.rep T a ∈ Finset.univ.image (G.rep T) :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hb : G.rep T b ∈ Finset.univ.image (G.rep T) :=
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  rw [hv, Finset.mem_singleton] at ha hb
  exact (G.rep_eq_iff T a b).mp (ha.trans hb.symm)

lemma crossing_components_subset (T U : Finset (Fin m)) :
    G.crossing T (G.rep U) ⊆ T \ U := by
  intro e he
  obtain ⟨heT, hec⟩ := Finset.mem_filter.mp he
  exact Finset.mem_sdiff.mpr ⟨heT, fun heU => hec (G.rep_endpoints heU)⟩

lemma crossing_components_self (T : Finset (Fin m)) : G.crossing T (G.rep T) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  have := G.crossing_components_subset T T he
  simp at this

theorem partition_criterion_sufficient (T : Finset (Fin m)) {r : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hp : ∀ p : Fin n → Fin n, r * (partitionSize p - 1) ≤ (G.crossing T p).card) :
    G.TreePackable T r := by
  have hc : G.Connected T := by
    have h := hp (G.rep T)
    rw [G.crossing_components_self, Finset.card_empty] at h
    change r * (G.componentCount T - 1) ≤ 0 at h
    have hpos := G.componentCount_pos hn T
    have hz : G.componentCount T - 1 = 0 := by nlinarith
    exact G.connected_of_componentCount_eq_one (by omega)
  have hcrit : ∀ U : Finset (Fin m), U ⊆ T →
      Fintype.card (Fin r) * Module.finrank ℝ (Packing.span G.incidence T) ≤
        (T \ U).card + Fintype.card (Fin r) * Module.finrank ℝ (Packing.span G.incidence U) := by
    intro U hUT
    change Fintype.card (Fin r) * Module.finrank ℝ (G.edgeSpan T) ≤
      (T \ U).card + Fintype.card (Fin r) * Module.finrank ℝ (G.edgeSpan U)
    rw [Fintype.card_fin, G.connected_rank hn hc, G.incidence_rank]
    have hpart := hp (G.rep U)
    have hcross := Finset.card_le_card (G.crossing_components_subset T U)
    have hcp := G.componentCount_pos hn U
    have hcle := G.componentCount_le U
    change r * (G.componentCount U - 1) ≤ (G.crossing T (G.rep U)).card at hpart
    have hnid : n - 1 = (G.componentCount U - 1) + (n - G.componentCount U) := by omega
    rw [hnid, Nat.mul_add]
    exact Nat.add_le_add_right (hpart.trans hcross) _
  obtain ⟨F, hv, hF⟩ := Packing.vector_base_packing_on G.incidence T hcrit
  refine ⟨F, fun i => ?_, hv.2⟩
  refine ⟨(hF i).1, (G.spanningTree_iff_independent (F i)).mpr ⟨?_, hv.1 i⟩⟩
  exact G.connected_of_span_eq (hF i).2.symm hc

lemma sum_partition_cuts (T : Finset (Fin m)) (p : Fin n → Fin n) :
    (∑ c ∈ Finset.univ.image p, (G.cut T (Finset.univ.filter (p · = c))).card) =
      2 * (G.crossing T p).card := by
  classical
  simp only [cut, crossing, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_comm]
  calc
    _ = ∑ e ∈ T, if p (G.left e) ≠ p (G.right e) then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : p (G.left e) = p (G.right e)
      · simp [h]
      · rw [ite_eq_left h]
        have hl : p (G.left e) ∈ Finset.univ.image p := Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
        have hr : p (G.right e) ∈ Finset.univ.image p := Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
        rw [Finset.sum_eq_add (p (G.left e)) (p (G.right e)) h]
        · simp [h, Ne.symm h]
        · intro c hc hh
          simp [Ne.symm hh.1, Ne.symm hh.2]
        · exact fun hh => (hh hl).elim
        · exact fun hh => (hh hr).elim
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; split_ifs <;> omega

lemma partition_fiber_proper (p : Fin n → Fin n) (hp : 1 < partitionSize p) (c : Fin n) :
    Finset.univ.filter (p · = c) ≠ Finset.univ := by
  intro h
  have him : Finset.univ.image p ⊆ {c} := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hd
    have hv' : v ∈ Finset.univ.filter (p · = c) := by rw [h]; exact Finset.mem_univ v
    simpa using hv'
  have : partitionSize p ≤ 1 := by simpa [partitionSize] using Finset.card_le_card him
  omega

theorem edgeConnected_treePackable {r : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hc : G.EdgeConnected (2 * r)) : G.TreePackable Finset.univ r := by
  apply G.partition_criterion_sufficient _ hr hn
  intro p
  by_cases hp : partitionSize p ≤ 1
  · have : partitionSize p - 1 = 0 := by omega
    simp [this]
  have hp' : 1 < partitionSize p := by omega
  have hsum : (∑ c ∈ Finset.univ.image p, 2 * r) ≤
      ∑ c ∈ Finset.univ.image p, (G.cut Finset.univ (Finset.univ.filter (p · = c))).card := by
    apply Finset.sum_le_sum
    intro c hc'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc'
    exact hc _ ⟨v, by simp⟩ (partition_fiber_proper p hp' _)
  rw [G.sum_partition_cuts] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  change partitionSize p * (2 * r) ≤ _ at hsum
  have : r * partitionSize p ≤ (G.crossing Finset.univ p).card := by nlinarith
  exact (Nat.mul_le_mul_left r (Nat.sub_le _ _)).trans this

lemma same_preserves_label {U : Finset (Fin m)} {p : Fin n → Fin n}
    (hp : ∀ e ∈ U, p (G.left e) = p (G.right e)) {u v : Fin n}
    (huv : G.Same U u v) : p u = p v := by
  classical
  by_contra h
  let S := Finset.univ.filter (fun w => p w = p u)
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ w ∈ S, LinearMap.proj w
  have hker : G.edgeSpan U ≤ LinearMap.ker f := by
    apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    change f (G.incidence e) = 0
    rw [incidence, map_sub]
    change (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.left e)) -
      (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.right e)) = 0
    simp [sumOn_point, S, hp e he]
  have hz := hker huv
  change f (point u - point v) = 0 at hz
  rw [map_sub] at hz
  change (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point u) -
    (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v) = 0 at hz
  simp [sumOn_point, S, Ne.symm h] at hz

lemma partitionSize_le_components {U : Finset (Fin m)} {p : Fin n → Fin n}
    (hp : ∀ e ∈ U, p (G.left e) = p (G.right e)) :
    partitionSize p ≤ G.componentCount U := by
  apply Finset.card_le_card_of_surjOn p
  intro c hc
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
  exact ⟨G.rep U v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩,
    G.same_preserves_label hp (G.rep_same U v)⟩

lemma spanningTree_crossing {T : Finset (Fin m)} (hn : 0 < n)
    (hT : G.SpanningTree T) (p : Fin n → Fin n) :
    partitionSize p - 1 ≤ (G.crossing T p).card := by
  classical
  let U := T \ G.crossing T p
  have hUT : U ⊆ T := Finset.sdiff_subset
  have hUi := ((G.spanningTree_iff_independent T).mp hT).2.mono hUT
  have hrank := Packing.indep_rank G.incidence hUi
  change Module.finrank ℝ (G.edgeSpan U) = U.card at hrank
  rw [G.incidence_rank] at hrank
  have hc := G.partitionSize_le_components (U := U) (p := p) (by
    intro e he
    obtain ⟨heT, hec⟩ := Finset.mem_sdiff.mp he
    by_contra h
    exact hec (Finset.mem_filter.mpr ⟨heT, h⟩))
  have hcard : U.card + (G.crossing T p).card = T.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  rw [G.spanningTree_card hn hT] at hcard
  have hle := G.componentCount_le U
  omega

theorem partition_criterion_necessary {T : Finset (Fin m)} {r : ℕ} (hn : 0 < n)
    (hpack : G.TreePackable T r) (p : Fin n → Fin n) :
    r * (partitionSize p - 1) ≤ (G.crossing T p).card := by
  classical
  obtain ⟨F, hF, hd⟩ := hpack
  have hdis : (↑(Finset.univ : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint
      (fun i => G.crossing (F i) p) := by
    intro i hi j hj hij
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hd hij))
  have hsub : Finset.univ.biUnion (fun i => G.crossing (F i) p) ⊆ G.crossing T p := by
    apply Finset.biUnion_subset.mpr
    intro i hi
    exact Finset.filter_subset_filter _ (hF i).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdis] at hc
  have ht : (∑ i : Fin r, (partitionSize p - 1)) ≤
      ∑ i : Fin r, (G.crossing (F i) p).card :=
    Finset.sum_le_sum (fun i hi => G.spanningTree_crossing hn (hF i).2 p)
  simpa using ht.trans hc

end StrongThinTree.MultiGraph

end
end

end OAI
