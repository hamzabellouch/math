import Mathlib.Data.Nat.Nth
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace OAI

/-! # Measurably enumerating nonzero frame indices

The `n`th index of a point-dependent subset of the naturals is measurable
when each membership predicate is measurable. The library's value zero
outside the finite range is retained; dimension strata remove that case.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X : Type*} [MeasurableSpace X]

noncomputable def measurableIndexCount (p : X → ℕ → Prop) (x : X) (n : ℕ) : ℕ := by
  classical
  exact Nat.count (p x) n

theorem measurable_indexCount (p : X → ℕ → Prop)
    (hp : ∀ n, MeasurableSet {x | p x n}) (n : ℕ) :
    Measurable fun x => measurableIndexCount p x n := by
  classical
  induction n with
  | zero => simpa only [measurableIndexCount, Nat.count_zero] using
      (measurable_const : Measurable fun _ : X => (0 : ℕ))
  | succ n ih =>
    simp only [measurableIndexCount, Nat.count_succ] at ih ⊢
    exact ih.add (Measurable.ite (hp n) measurable_const measurable_const)

private theorem nth_eq_nonzero_iff (p : ℕ → Prop) (k m : ℕ) (hm : m ≠ 0) :
    Nat.nth p k = m ↔ p m ∧ measurableIndexCount (fun _ : Unit => p) () m = k := by
  classical
  change Nat.nth p k = m ↔ p m ∧ Nat.count p m = k
  constructor
  · intro h
    have hn : Nat.nth p k ≠ 0 := h.trans_ne hm
    refine ⟨h ▸ Nat.nth_mem_of_ne_zero hn, ?_⟩
    rw [← h]
    exact Nat.count_nth fun hf => Nat.lt_card_toFinset_of_nth_ne_zero hn hf
  · rintro ⟨hpm, hc⟩
    rw [← hc]
    exact Nat.nth_count hpm

theorem measurable_natNth (p : X → ℕ → Prop)
    (hp : ∀ n, MeasurableSet {x | p x n}) (k : ℕ) :
    Measurable fun x => Nat.nth (p x) k := by
  classical
  have hm (m : ℕ) (hm0 : m ≠ 0) : MeasurableSet {x | Nat.nth (p x) k = m} := by
    have he : {x | Nat.nth (p x) k = m} =
        {x | p x m} ∩ {x | measurableIndexCount p x m = k} := by
      ext x
      exact nth_eq_nonzero_iff (p x) k m hm0
    rw [he]
    exact (hp m).inter (measurableSet_eq_fun (measurable_indexCount p hp m) measurable_const)
  apply measurable_to_countable'
  intro m
  by_cases hm0 : m = 0
  · subst m
    have he : {x | Nat.nth (p x) k = 0} =
        (⋃ n : ℕ, {x | Nat.nth (p x) k = n + 1})ᶜ := by
      ext x
      cases h : Nat.nth (p x) k with
      | zero => simp [h]
      | succ n => simp [h]
    change MeasurableSet {x | Nat.nth (p x) k = 0}
    rw [he]
    exact (MeasurableSet.iUnion fun n => hm (n + 1) (by omega)).compl
  · exact hm m hm0

/-- There are at least `k + 1` indices satisfying the predicate. -/
def frameIndexAvailable (p : ℕ → Prop) (k : ℕ) : Prop :=
  ∃ m, k < measurableIndexCount (fun _ : Unit => p) () m

theorem frameIndexAvailable_mono {p : ℕ → Prop} {k l : ℕ}
    (hkl : k ≤ l) (h : frameIndexAvailable p l) : frameIndexAvailable p k := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, lt_of_le_of_lt hkl hm⟩

theorem measurableSet_frameIndexAvailable (p : X → ℕ → Prop)
    (hp : ∀ n, MeasurableSet {x | p x n}) (k : ℕ) :
    MeasurableSet {x | frameIndexAvailable (p x) k} := by
  have he : {x | frameIndexAvailable (p x) k} =
      ⋃ m : ℕ, {x | k < measurableIndexCount p x m} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, frameIndexAvailable, measurableIndexCount]
  rw [he]
  exact MeasurableSet.iUnion fun m =>
    measurableSet_lt measurable_const (measurable_indexCount p hp m)

omit [MeasurableSpace X] in
 theorem frameIndexAvailable_valid {p : ℕ → Prop} {k : ℕ}
    (h : frameIndexAvailable p k) :
    ∀ hf : (Set.ofPred p).Finite, k < hf.toFinset.card := by
  classical
  obtain ⟨m, hm⟩ := h
  intro hf
  exact lt_of_lt_of_le hm (Nat.count_le_card hf m)

omit [MeasurableSpace X] in
 theorem frameIndexAvailable_count {p : ℕ → Prop} {m : ℕ} (hm : p m) :
    frameIndexAvailable p (measurableIndexCount (fun _ : Unit => p) () m) := by
  classical
  refine ⟨m + 1, ?_⟩
  change Nat.count p m < Nat.count p (m + 1)
  exact Nat.count_lt_count_succ_iff.mpr hm

/-- The ascending enumeration, restricted to its genuine indices, is a bijection. -/
def frameIndexEquiv (p : ℕ → Prop) : {k // frameIndexAvailable p k} ≃ {m // p m} := by
  classical
  exact {
    toFun := fun k => ⟨Nat.nth p k, Nat.nth_mem _ (frameIndexAvailable_valid k.property)⟩
    invFun := fun m => ⟨Nat.count p m, frameIndexAvailable_count m.property⟩
    left_inv := fun k => Subtype.ext (Nat.count_nth (frameIndexAvailable_valid k.property))
    right_inv := fun m => Subtype.ext (Nat.nth_count m.property) }

/-- Index zero is the infinite-rank stratum; index `n + 1` is rank `n`. -/
def frameDimensionStratum (p : X → ℕ → Prop) : ℕ → Set X
  | 0 => {x | ∀ k, frameIndexAvailable (p x) k}
  | n + 1 => {x | (∀ k < n, frameIndexAvailable (p x) k) ∧
      ¬frameIndexAvailable (p x) n}

theorem measurableSet_frameDimensionStratum (p : X → ℕ → Prop)
    (hp : ∀ n, MeasurableSet {x | p x n}) (n : ℕ) :
    MeasurableSet (frameDimensionStratum p n) := by
  cases n with
  | zero =>
    simpa only [frameDimensionStratum, Set.ofPred_forall] using
      (MeasurableSet.iInter fun k => measurableSet_frameIndexAvailable p hp k)
  | succ n =>
    convert (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _hk : k < n =>
      measurableSet_frameIndexAvailable p hp k).inter
        (measurableSet_frameIndexAvailable p hp n).compl using 1
    ext x
    simp only [frameDimensionStratum, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff, Set.mem_ofPred_eq]

omit [MeasurableSpace X] in
theorem exists_frameDimensionStratum (p : X → ℕ → Prop) (x : X) :
    ∃ n, x ∈ frameDimensionStratum p n := by
  classical
  by_cases h : ∀ k, frameIndexAvailable (p x) k
  · exact ⟨0, h⟩
  · obtain ⟨k, hk⟩ := not_forall.mp h
    let hn : ∃ k, ¬frameIndexAvailable (p x) k := ⟨k, hk⟩
    exact ⟨Nat.find hn + 1, fun k hk => of_not_not (Nat.find_min hn hk), Nat.find_spec hn⟩

omit [MeasurableSpace X] in
theorem frameDimensionStratum_finite_iff (p : X → ℕ → Prop) {n : ℕ}
    {x : X} (hx : x ∈ frameDimensionStratum p (n + 1)) (k : ℕ) :
    frameIndexAvailable (p x) k ↔ k < n := by
  constructor
  · intro hk
    by_contra hn
    exact hx.2 (frameIndexAvailable_mono (Nat.le_of_not_gt hn) hk)
  · exact hx.1 k

end

end KadisonKastler

end OAI
