import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.SafeSwitch
import OAI.Combinatorics.MatchingCount.Sampling.Underlying

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable def componentOrder (U : Finset E) :
    Fin (components (inc := inc) U).card ≃ ↥(components (inc := inc) U) :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm

noncomputable def componentPrefix (U : Finset E) (i : ℕ) : Finset E := by
  classical
  exact (Finset.univ.filter (fun j : Fin (components (inc := inc) U).card => j.val < i)).biUnion
    (fun j => (componentOrder (inc := inc) U j).val)

omit [Fintype V] [DecidableEq V] in
lemma mem_componentPrefix (U : Finset E) (i : ℕ) (e : E) :
    e ∈ componentPrefix (inc := inc) U i ↔
      ∃ j : Fin (components (inc := inc) U).card, j.val < i ∧ e ∈ (componentOrder (inc := inc) U j).val := by
  classical
  simp only [componentPrefix, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and]

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_zero (U : Finset E) : componentPrefix (inc := inc) U 0 = ∅ := by
  ext e
  simp [mem_componentPrefix]

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_succ (U : Finset E) (i : ℕ) (hi : i < (components (inc := inc) U).card) :
    componentPrefix (inc := inc) U (i+1) =
      componentPrefix (inc := inc) U i ∪ (componentOrder (inc := inc) U ⟨i,hi⟩).val := by
  ext e
  simp only [mem_componentPrefix, Finset.mem_union]
  constructor
  · rintro ⟨j,hj,he⟩
    by_cases hji : j.val < i
    · exact Or.inl ⟨j,hji,he⟩
    · have hje : j = ⟨i,hi⟩ := Fin.ext (by change j.val = i; omega)
      exact Or.inr (hje ▸ he)
  · rintro (⟨j,hj,he⟩ | he)
    · exact ⟨j,by omega,he⟩
    · exact ⟨⟨i,hi⟩,by change i < i+1; omega,he⟩

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_full (U : Finset E) :
    componentPrefix (inc := inc) U (components (inc := inc) U).card = U := by
  rw [← components_cover (inc := inc) U]
  conv_lhs => rw [components_cover]
  ext e
  simp only [mem_componentPrefix, Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨j,_,he⟩
    exact ⟨(componentOrder U j).val, (componentOrder U j).property, he⟩
  · rintro ⟨S,hS,he⟩
    obtain ⟨j,hj⟩ := (componentOrder (inc := inc) U).surjective ⟨S,hS⟩
    exact ⟨j,j.isLt,by simpa only [hj] using he⟩

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_disjoint (U : Finset E) (i : ℕ)
    (hi : i < (components (inc := inc) U).card) :
    Disjoint (componentPrefix (inc := inc) U i) (componentOrder (inc := inc) U ⟨i,hi⟩).val := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨j,hj,he⟩ := (mem_componentPrefix U i e).mp he
  have hne : (componentOrder (inc := inc) U j).val ≠
      (componentOrder (inc := inc) U ⟨i,hi⟩).val := by
    intro heq
    have hh := (componentOrder (inc := inc) U).injective (Subtype.ext heq)
    have hv : j.val = i := congrArg Fin.val hh
    omega
  exact Finset.disjoint_left.mp
    (components_pairwise_disjoint U (componentOrder U j).property
      (componentOrder U ⟨i,hi⟩).property hne) he hf

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_compatible (M N : Finset E) (i : ℕ) :
    ExchangeCompatible (inc := inc) M N (componentPrefix (inc := inc) (M ∪ N) i) := by
  intro e he f hf v hev hfv
  simp only [mem_componentPrefix]
  constructor
  · rintro ⟨j,hj,he'⟩
    exact ⟨j,hj,(component_exchange_compatible (componentOrder (M ∪ N) j).property
      e he f hf v hev hfv).mp he'⟩
  · rintro ⟨j,hj,hf'⟩
    exact ⟨j,hj,(component_exchange_compatible (componentOrder (M ∪ N) j).property
      e he f hf v hev hfv).mpr hf'⟩

lemma exchange_empty (M N : Finset E) : exchange M N ∅ = M := by
  simp [exchange]

lemma exchange_all (M N : Finset E) : exchange M N (M ∪ N) = N := by
  ext e
  simp only [mem_exchange, Finset.mem_union]
  tauto

lemma exchange_disjoint_composition (M N S T : Finset E) (h : Disjoint S T) :
    exchange (exchange M N S) (exchange N M S) T = exchange M N (S ∪ T) := by
  rw [exchange_composition]
  congr 1
  ext e
  have hh : e ∈ S → e ∉ T := fun he => Finset.disjoint_left.mp h he
  simp only [Finset.mem_symmDiff, Finset.mem_union]
  tauto

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_step (M N : Finset E) (i : ℕ)
    (hi : i < (components (inc := inc) (M ∪ N)).card) :
    exchange M N (componentPrefix (inc := inc) (M ∪ N) (i+1)) =
      exchange (exchange M N (componentPrefix (inc := inc) (M ∪ N) i))
        (exchange N M (componentPrefix (inc := inc) (M ∪ N) i))
        (componentOrder (inc := inc) (M ∪ N) ⟨i,hi⟩).val := by
  rw [componentPrefix_succ _ _ hi,
    exchange_disjoint_composition M N _ _ (componentPrefix_disjoint _ _ hi)]

end

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable def prefixPair (p : PM inc × PM inc) (i : ℕ) : PM inc × PM inc :=
  (⟨exchange p.1.val p.2.val (componentPrefix (inc := inc) (p.1.val ∪ p.2.val) i),
    exchange_matching p.1.property p.2.property (componentPrefix_compatible _ _ _)⟩,
   ⟨exchange p.2.val p.1.val (componentPrefix (inc := inc) (p.1.val ∪ p.2.val) i),
    exchange_matching p.2.property p.1.property (componentPrefix_compatible _ _ _).symm⟩)

omit [DecidableEq V] [Fintype E] in
lemma prefixPair_union (p : PM inc × PM inc) (i : ℕ) :
    (prefixPair p i).1.val ∪ (prefixPair p i).2.val = p.1.val ∪ p.2.val :=
  exchange_union _ _ _

omit [DecidableEq V] [Fintype E] in
lemma prefixPair_involutive (i : ℕ) : Function.Involutive (fun p : PM inc × PM inc => prefixPair p i) := by
  intro p
  have hu := prefixPair_union p i
  apply Prod.ext <;> apply Subtype.ext
  · change exchange (prefixPair p i).1.val (prefixPair p i).2.val
      (componentPrefix (inc := inc) ((prefixPair p i).1.val ∪ (prefixPair p i).2.val) i) = _
    rw [hu]
    exact exchange_involution _ _ _
  · change exchange (prefixPair p i).2.val (prefixPair p i).1.val
      (componentPrefix (inc := inc) ((prefixPair p i).1.val ∪ (prefixPair p i).2.val) i) = _
    rw [hu]
    exact exchange_involution _ _ _

omit [DecidableEq V] [Fintype E] in
lemma prefixPair_zero (p : PM inc × PM inc) : prefixPair p 0 = p := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [prefixPair, componentPrefix_zero, exchange_empty]

omit [Fintype V] [DecidableEq V] [Fintype E] in
lemma componentPrefix_eq_full (U : Finset E) (i : ℕ)
    (hi : (components (inc := inc) U).card ≤ i) : componentPrefix (inc := inc) U i = U := by
  calc
    _ = componentPrefix (inc := inc) U (components (inc := inc) U).card := by
      apply Finset.ext
      intro e
      simp only [mem_componentPrefix]
      constructor
      · rintro ⟨j,_,he⟩
        exact ⟨j,j.isLt,he⟩
      · rintro ⟨j,_,he⟩
        exact ⟨j,Nat.lt_of_lt_of_le j.isLt hi,he⟩
    _ = U := componentPrefix_full U

omit [DecidableEq V] [Fintype E] in
lemma prefixPair_full (p : PM inc × PM inc) (i : ℕ)
    (hi : (components (inc := inc) (p.1.val ∪ p.2.val)).card ≤ i) :
    prefixPair p i = (p.2,p.1) := by
  apply Prod.ext <;> apply Subtype.ext
  · dsimp only [prefixPair]
    rw [componentPrefix_eq_full _ _ hi, exchange_all]
  · dsimp only [prefixPair]
    rw [componentPrefix_eq_full _ _ hi, Finset.union_comm p.1.val p.2.val, exchange_all]

noncomputable def componentAt (U : Finset E) (i : ℕ) : Finset E :=
  if h : i < (components (inc := inc) U).card then (componentOrder (inc := inc) U ⟨i,h⟩).val else ∅

omit [Fintype V] [DecidableEq V] [Fintype E] in
lemma componentAt_compatible (M N : Finset E) (i : ℕ) :
    ExchangeCompatible (inc := inc) M N (componentAt (inc := inc) (M ∪ N) i) := by
  classical
  unfold componentAt
  split_ifs with h
  · exact component_exchange_compatible (componentOrder (M ∪ N) ⟨i,h⟩).property
  · intro e he f hf v hev hfv
    simp

noncomputable def componentPair (p : PM inc × PM inc) (i : ℕ) : PM inc × PM inc :=
  (⟨exchange p.1.val p.2.val (componentAt (inc := inc) (p.1.val ∪ p.2.val) i),
    exchange_matching p.1.property p.2.property (componentAt_compatible _ _ _)⟩,
   ⟨exchange p.2.val p.1.val (componentAt (inc := inc) (p.1.val ∪ p.2.val) i),
    exchange_matching p.2.property p.1.property (componentAt_compatible _ _ _).symm⟩)

omit [DecidableEq V] [Fintype E] in
lemma prefixPair_step (p : PM inc × PM inc) (i : ℕ) :
    prefixPair p (i+1) = componentPair (prefixPair p i) i := by
  classical
  by_cases h : i < (components (inc := inc) (p.1.val ∪ p.2.val)).card
  · apply Prod.ext <;> apply Subtype.ext
    · change exchange p.1.val p.2.val (componentPrefix (inc := inc) (p.1.val ∪ p.2.val) (i+1)) =
        exchange (prefixPair p i).1.val (prefixPair p i).2.val
          (componentAt (inc := inc) ((prefixPair p i).1.val ∪ (prefixPair p i).2.val) i)
      rw [prefixPair_union, componentAt, dite_eq_left h]
      exact componentPrefix_step _ _ _ h
    · change exchange p.2.val p.1.val (componentPrefix (inc := inc) (p.1.val ∪ p.2.val) (i+1)) =
        exchange (prefixPair p i).2.val (prefixPair p i).1.val
          (componentAt (inc := inc) ((prefixPair p i).1.val ∪ (prefixPair p i).2.val) i)
      rw [prefixPair_union, componentAt, dite_eq_left h, componentPrefix_succ _ _ h]
      exact (exchange_disjoint_composition _ _ _ _ (componentPrefix_disjoint _ _ h)).symm
  · have hle := Nat.le_of_not_gt h
    rw [prefixPair_full p (i+1) (by omega), prefixPair_full p i hle]
    apply Prod.ext <;> apply Subtype.ext <;>
      simp only [componentPair, componentAt, Finset.union_comm p.2.val p.1.val, dite_eq_right h,
        exchange_empty]

omit [DecidableEq V] in
lemma prefixPair_gibbs (w : E → ℝ) (p : PM inc × PM inc) (i : ℕ) :
    gibbs w (prefixPair p i).1 * gibbs w (prefixPair p i).2 = gibbs w p.1 * gibbs w p.2 := by
  simp only [gibbs, div_mul_div_comm]
  congr 1
  exact exchange_weight w _ _ _

noncomputable def componentDifference (f : PM inc → ℝ) (p : PM inc × PM inc) (i : ℕ) : ℝ :=
  f p.1 - f (componentPair p i).1

omit [DecidableEq V] [Fintype E] in
lemma prefix_difference_sum (f : PM inc → ℝ) (p : PM inc × PM inc) (n : ℕ) :
    (∑ i ∈ Finset.range n, componentDifference f (prefixPair p i) i) =
      f p.1 - f (prefixPair p n).1 := by
  induction n with
  | zero => simp [prefixPair_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [componentDifference, ← prefixPair_step]
    ring

omit [DecidableEq V] [Fintype E] in
lemma canonical_path_square (hinc : ∀ e, ∃ v, inc e v)
    (f : PM inc → ℝ) (p : PM inc × PM inc) :
    (f p.1 - f p.2)^2 ≤ (Fintype.card V : ℝ) *
      ∑ i ∈ Finset.range (Fintype.card V), (componentDifference f (prefixPair p i) i)^2 := by
  classical
  have hfull := prefixPair_full p (Fintype.card V) (components_card_le hinc _)
  have hs := prefix_difference_sum f p (Fintype.card V)
  rw [hfull] at hs
  rw [← hs]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (Fintype.card V))
    (fun i => componentDifference f (prefixPair p i) i) (fun _ => (1:ℝ))
  simpa only [mul_one, one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using hh

omit [DecidableEq V] in
lemma sum_prefixPair (w : E → ℝ) (g : PM inc × PM inc → ℝ) (i : ℕ) :
    letI : Fintype (PM inc) := Fintype.ofFinite _
    (∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 * g (prefixPair p i)) =
      ∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 * g p := by
  classical
  let : Fintype (PM inc) := Fintype.ofFinite _
  let e := (prefixPair_involutive i).toPerm (fun p : PM inc × PM inc => prefixPair p i)
  have hh := Equiv.sum_comp e (fun p => gibbs w p.1 * gibbs w p.2 * g p)
  change (∑ p : PM inc × PM inc, gibbs w (prefixPair p i).1 * gibbs w (prefixPair p i).2 *
    g (prefixPair p i)) = _ at hh
  simpa only [prefixPair_gibbs] using hh

omit [DecidableEq V] in
theorem cycle_demand_variance (hinc : ∀ e, ∃ v, inc e v)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (f : PM inc → ℝ) :
    letI : Fintype (PM inc) := Fintype.ofFinite _
    (∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 * (f p.1 - f p.2)^2) / 2 ≤
      (Fintype.card V : ℝ) * ∑ p : PM inc × PM inc,
        gibbs w p.1 * gibbs w p.2 *
          ∑ i ∈ Finset.range (Fintype.card V), (componentDifference f p i)^2 := by
  classical
  let : Fintype (PM inc) := Fintype.ofFinite _
  have he : (∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 *
        ∑ i ∈ Finset.range (Fintype.card V), (componentDifference f (prefixPair p i) i)^2) =
      ∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 *
        ∑ i ∈ Finset.range (Fintype.card V), (componentDifference f p i)^2 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.range _)]
    apply Finset.sum_congr rfl
    intro i _
    exact sum_prefixPair w (fun p => (componentDifference f p i)^2) i
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (PM inc × PM inc)))
    (fun p _ => mul_le_mul_of_nonneg_left (canonical_path_square hinc f p)
      (mul_nonneg (le_of_lt (gibbs_pos w hw p.1)) (le_of_lt (gibbs_pos w hw p.2))))
  have hr : 0 ≤ (∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 * (f p.1 - f p.2)^2) :=
    Finset.sum_nonneg (fun p _ => mul_nonneg
      (mul_nonneg (le_of_lt (gibbs_pos w hw p.1)) (le_of_lt (gibbs_pos w hw p.2))) (sq_nonneg _))
  have hrew : (∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 *
        ((Fintype.card V : ℝ) * ∑ i ∈ Finset.range (Fintype.card V),
          (componentDifference f (prefixPair p i) i)^2)) =
      (Fintype.card V : ℝ) * ∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 *
        ∑ i ∈ Finset.range (Fintype.card V), (componentDifference f p i)^2 := by
    rw [← he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hrew] at hb
  linarith

end

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

def ColorChange (A B : PM (fun e v => v ∈ ends e)) : Prop :=
  ∃ e f : E, ∃ R : Finset E, ends e = ends f ∧ A.val = R ∪ {e} ∧ B.val = R ∪ {f}

noncomputable def colorDestinations (A : PM (fun e v => v ∈ ends e)) :
    Finset (PM (fun e v => v ∈ ends e)) := by
  classical
  exact Finset.univ.filter (ColorChange ends A)

omit [DecidableEq V] [Fintype E] in
lemma matching_inter_parallel {M : Finset E}
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    {e f : E} (he : e ∈ M) (hef : ends e = ends f) : M ∩ {e,f} = {e} := by
  classical
  obtain ⟨v,hv⟩ : ∃ v, v ∈ ends e := by
    induction ends e using Sym2.inductionOn with | hf a b => exact ⟨a,by simp⟩
  ext a
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨ha, rfl | haf⟩
    · rfl
    · subst a
      exact hM.unique (Finset.mem_univ v) ha (hef ▸ hv) he hv
  · rintro rfl
    exact ⟨he,Or.inl rfl⟩

omit [DecidableEq V] [Fintype E] in
lemma parallel_exchange_color (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e))
    {S : Finset E} (hS : S ∈ components (inc := fun e v => v ∈ ends e) (p.1.val ∪ p.2.val))
    {e f : E} (he : e ∈ p.1.val) (hf : f ∈ p.2.val) (hef : ends e = ends f) (hset : S = {e,f}) :
    ColorChange ends p.1
      ⟨exchange p.1.val p.2.val S,exchange_matching p.1.property p.2.property (component_exchange_compatible hS)⟩ := by
  classical
  refine ⟨e,f,p.1.val \ S,hef,?_,?_⟩
  · have h := matching_inter_parallel ends p.1.property he hef
    rw [← hset] at h
    rw [← h]
    ext a
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  · change exchange p.1.val p.2.val S = _
    have h := matching_inter_parallel ends p.2.property hf hef.symm
    rw [Finset.pair_comm,← hset] at h
    exact congrArg ((p.1.val \ S) ∪ ·) h

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

omit [Fintype L] in
lemma Demand.cellCost_nonneg (d : Demand hbags hG) (f : Finset (BagEdge bags) → ℝ) :
    0 ≤ d.cellCost f := by unfold Demand.cellCost; positivity

omit [Fintype L] in
lemma Demand.cellCost_eq (d : Demand hbags hG) (f : Finset (BagEdge bags) → ℝ) :
    d.cellCost f = d.cycle.diagramEnergy hbags d.outside f
      d.2.2.val.x d.2.2.val.p d.2.2.val.q d.2.2.val.y := by
  classical
  rw [IndexedCycle.diagramEnergy, dite_eq_left ⟨d.cell,d.last_lt⟩]
  rfl

noncomputable def longCellCost (p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) : ℝ :=
  ∑ S : LongComponent p, ∑ a : ↥(S.cycle.subdivision hbags hG).cellSet,
    (show Demand hbags hG from ⟨p,S,a⟩).cellCost f

lemma longCellCost_nonneg (p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) : 0 ≤ longCellCost (hbags := hbags) (hG := hG) p f :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Demand.cellCost_nonneg _ _))

noncomputable def colorCost (A : PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) : ℝ :=
  ∑ B ∈ colorDestinations (fun e : BagEdge bags => e.val.val.1) A, (f A.val-f B.val)^2

lemma colorCost_nonneg (A : PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) : 0 ≤ colorCost A f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem component_cell_bound
    (p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) {S : Finset (BagEdge bags)}
    (hS : S ∈ components (inc := BagEdge.Incident) (p.1.val ∪ p.2.val)) :
    (f p.1.val - f (exchange p.1.val p.2.val S))^2 ≤
      3 * (Fintype.card V : ℝ) * longCellCost (hbags := hbags) (hG := hG) p f + colorCost p.1 f := by
  classical
  rcases Overlay.component_classification (fun e : BagEdge bags => e.val.val.1)
    (fun e => e.val.property) p.1.property p.2.property hS with h | ⟨c,hc,rfl⟩
  · obtain ⟨e,he,d,hd,hed,hset⟩ := h
    have hcol := parallel_exchange_color (fun e : BagEdge bags => e.val.val.1) p hS he hd hed hset
    have hle : (f p.1.val-f (exchange p.1.val p.2.val S))^2 ≤ colorCost p.1 f := by
      exact Finset.single_le_sum (s := colorDestinations (fun e : BagEdge bags => e.val.val.1) p.1)
        (a := ⟨exchange p.1.val p.2.val S,exchange_matching p.1.property p.2.property (component_exchange_compatible hS)⟩)
        (f := fun B : PM BagEdge.Incident => (f p.1.val-f B.val)^2)
        (fun _ _ => sq_nonneg _) (by
          change _ ∈ Finset.univ.filter (ColorChange (fun e : BagEdge bags => e.val.val.1) p.1)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcol⟩)
    exact hle.trans (le_add_of_nonneg_left (mul_nonneg (by positivity) (longCellCost_nonneg p f)))
  · let T : LongComponent p := ⟨c.edgeSet,c,rfl,hc⟩
    have hcell := T.cycle.exchange_cell_square_bound hbags p.1.property p.2.property T.cycle_union hG f
    have hcost : (∑ a ∈ (T.cycle.subdivision hbags hG).cellSet,
        T.cycle.diagramEnergy hbags (p.1.val \ T.cycle.edgeSet) f a.x a.p a.q a.y) =
        ∑ a : ↥(T.cycle.subdivision hbags hG).cellSet,
          (show Demand hbags hG from ⟨p,T,a⟩).cellCost f := by
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro a _
      exact (Demand.cellCost_eq ⟨p,T,a⟩ f).symm
    rw [hcost,T.cycle_set] at hcell
    have hle : (∑ a : ↥(T.cycle.subdivision hbags hG).cellSet,
          (show Demand hbags hG from ⟨p,T,a⟩).cellCost f) ≤
        longCellCost (hbags := hbags) (hG := hG) p f :=
      Finset.single_le_sum (f := fun S : LongComponent p => ∑ a : ↥(S.cycle.subdivision hbags hG).cellSet,
        (show Demand hbags hG from ⟨p,S,a⟩).cellCost f)
        (fun S _ => Finset.sum_nonneg (fun a _ => Demand.cellCost_nonneg ⟨p,S,a⟩ f)) (Finset.mem_univ T)
    exact (hcell.trans (mul_le_mul_of_nonneg_left hle (by positivity))).trans
      (le_add_of_nonneg_right (colorCost_nonneg p.1 f))

end MatchingFPRAS.Transport.CellDemands

lemma arbitrary_sigma_sum {α : Type*} {β : α → Type*} [Fintype α] [∀ a, Fintype (β a)]
    [i : Fintype (Sigma β)] (f : Sigma β → ℝ) :
    (∑ d : Sigma β, f d) = ∑ a : α, ∑ b : β a, f ⟨a,b⟩ := by
  have hi : i = Sigma.instFintype := Subsingleton.elim _ _
  subst hi
  exact Fintype.sum_sigma f

end OAI
