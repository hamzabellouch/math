import OAI.Computability.WLIdentification.StackCommands

namespace OAI

namespace WLIdentification

namespace FiniteRefinement

/-- Only equality kernels matter; no full color trees need be stored. -/
theorem map_eq_of_kernel {A B C : Type} (f : A → B) (g : A → C) (L M : Multiset A)
    (h : ∀ a b, f a = f b → g a = g b) (he : L.map f = M.map f) : L.map g = M.map g := by
  apply Multiset.rel_eq.mp
  rw [Multiset.rel_map]
  have hr : Multiset.Rel (fun a b => f a = f b) L M := by
    rw [← Multiset.rel_map, Multiset.rel_eq]
    exact he
  exact hr.mono (fun a _ b _ hab => h a b hab)

theorem map_eq_iff_kernel {A B C : Type} (f : A → B) (g : A → C) (L M : Multiset A)
    (h : ∀ a b, f a = f b ↔ g a = g b) : L.map f = M.map f ↔ L.map g = M.map g :=
  ⟨map_eq_of_kernel f g L M (fun a b => (h a b).mp),
    map_eq_of_kernel g f L M (fun a b => (h a b).mpr)⟩

variable {A : Type} [Fintype A] {C : ℕ → Type} (color : (s : ℕ) → A → C s)

def KernelEq (s t : ℕ) : Prop := ∀ a b, color s a = color s b ↔ color t a = color t b

noncomputable def kernel (s : ℕ) : Finset (A × A) := by
  classical exact Finset.univ.filter (fun ab => color s ab.1 = color s ab.2)

theorem kernel_eq_iff (s t : ℕ) : kernel color s = kernel color t ↔ KernelEq color s t := by
  classical
  constructor
  · intro h a b
    have := Finset.ext_iff.mp h (a, b)
    simpa only [kernel, Finset.mem_filter, Finset.mem_univ, true_and] using this
  · intro h
    ext ab
    simp only [kernel, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h ab.1 ab.2

theorem kernel_step_subset (h : ∀ s a b, color (s+1) a = color (s+1) b → color s a = color s b)
    (s : ℕ) : kernel color (s + 1) ⊆ kernel color s := by
  classical
  intro ab hab
  simp only [kernel, Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
  exact h s ab.1 ab.2 hab

/-- A descending Boolean relation on N objects must settle by N² rounds.
This coarse bound avoids an implicit unit-cost operation on full color names. -/
theorem exists_adjacent (h : ∀ s a b, color (s+1) a = color (s+1) b → color s a = color s b) :
    ∃ s ≤ Fintype.card A ^ 2, KernelEq color s (s+1) := by
  classical
  let N := Fintype.card A ^ 2
  by_contra hn
  have hstrict (s : ℕ) (hs : s ≤ N) : (kernel color (s + 1)).card < (kernel color s).card := by
    apply Finset.card_lt_card
    exact (kernel_step_subset color h s).ssubset_of_ne (by
      intro he
      exact hn ⟨s, hs, (kernel_eq_iff color s (s+1)).mp he.symm⟩)
  have hsum (s : ℕ) (hs : s ≤ N + 1) : (kernel color s).card + s ≤ (kernel color 0).card := by
    induction s with
    | zero => simp
    | succ s ih => have hlt := hstrict s (by omega); have hi := ih (by omega); omega
  have hc : (kernel color 0).card ≤ N := by
    calc
      _ ≤ Fintype.card (A × A) := Finset.card_le_univ _
      _ = N := by simp [N, pow_two]
  have := hsum (N+1) (by omega)
  omega

omit [Fintype A] in
theorem KernelEq.refl (s : ℕ) : KernelEq color s s := fun _ _ => Iff.rfl

omit [Fintype A] in
theorem KernelEq.symm {s t : ℕ} (h : KernelEq color s t) : KernelEq color t s :=
  fun a b => (h a b).symm

omit [Fintype A] in
theorem KernelEq.trans {s t u : ℕ} (h : KernelEq color s t) (h' : KernelEq color t u) :
    KernelEq color s u := fun a b => (h a b).trans (h' a b)

variable (hrefine : ∀ s a b, color (s+1) a = color (s+1) b → color s a = color s b)
    (hstep : ∀ s t, KernelEq color s t → KernelEq color (s+1) (t+1))

omit [Fintype A] in
include hrefine in
theorem earlier {s t : ℕ} (hst : s ≤ t) (a b : A) (h : color t a = color t b) :
    color s a = color s b := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t ht ih => exact ih (hrefine t a b h)

omit [Fintype A] in
include hstep in
theorem stable_tail {s : ℕ} (h : KernelEq color s (s+1)) (u : ℕ) :
    KernelEq color s (s+u) := by
  induction u with
  | zero => exact KernelEq.refl color s
  | succ u ih =>
    have ht : KernelEq color (s+1) (s+u+1) := hstep s (s+u) ih
    exact (h.trans color ht)

include hrefine hstep in
/-- The one stored Boolean relation after the explicit cutoff decides equality
at every refinement depth, including all later rounds. -/
theorem cutoff (a b : A) (s : ℕ) :
    color (Fintype.card A ^ 2) a = color (Fintype.card A ^ 2) b → color s a = color s b := by
  intro he
  let N := Fintype.card A ^ 2
  obtain ⟨t, ht, hstable⟩ := exists_adjacent color hrefine
  by_cases hs : s ≤ N
  · exact earlier color hrefine hs a b he
  · have hte := earlier color hrefine ht a b he
    have hts : t ≤ s := by omega
    have htail := stable_tail color hstep hstable (s-t)
    rw [Nat.add_sub_of_le hts] at htail
    exact (htail a b).mp hte

include hrefine hstep in
theorem histogram_cutoff (L M : Multiset A) :
    (∀ s, L.map (color s) = M.map (color s)) ↔
      L.map (color (Fintype.card A ^ 2)) = M.map (color (Fintype.card A ^ 2)) := by
  constructor
  · exact fun h => h _
  · intro h s
    exact map_eq_of_kernel _ _ L M (fun a b => cutoff color hrefine hstep a b s) h

omit [Fintype A] in
/-- Equality of replacement-vector histograms is determined by the old kernel,
so the same stored relation supports ordinary and joint tuple updates. -/
theorem successor_kernel {I : Type} (N : A → Multiset (I → A))
    (hupdate : ∀ s a b, color (s+1) a = color (s+1) b ↔
      color s a = color s b ∧
        (N a).map (fun v i => color s (v i)) = (N b).map (fun v i => color s (v i))) :
    ∀ s t, KernelEq color s t → KernelEq color (s+1) (t+1) := by
  intro s t h a b
  rw [hupdate, hupdate, h a b]
  apply and_congr Iff.rfl
  apply map_eq_iff_kernel
  intro v w
  simp only [funext_iff]
  exact forall_congr' (fun i => h (v i) (w i))

end FiniteRefinement
namespace FiniteRefinement

theorem successor_kernel_scalar {A : Type} {C : ℕ → Type}
    (color : (s : ℕ) → A → C s) (N : A → Multiset A)
    (hupdate : ∀ s a b, color (s+1) a = color (s+1) b ↔
      color s a = color s b ∧ (N a).map (color s) = (N b).map (color s)) :
    ∀ s t, KernelEq color s t → KernelEq color (s+1) (t+1) := by
  intro s t h a b
  rw [hupdate, hupdate, h a b]
  apply and_congr Iff.rfl
  exact map_eq_iff_kernel _ _ _ _ h

end FiniteRefinement

namespace FiniteWL

def neighbor (G H : Graph) (s : ℕ) : Fin G.order ⊕ Fin H.order → NeighborColor s :=
  Sum.elim (neighborColor G s) (neighborColor H s)

def neighbors (G H : Graph) : Fin G.order ⊕ Fin H.order → Multiset (Fin G.order ⊕ Fin H.order)
  | .inl x => (Finset.univ.filter (fun y => G.edge x y = true)).val.map Sum.inl
  | .inr x => (Finset.univ.filter (fun y => H.edge x y = true)).val.map Sum.inr

theorem neighbor_update (G H : Graph) (s : ℕ) (a b : Fin G.order ⊕ Fin H.order) :
    neighbor G H (s+1) a = neighbor G H (s+1) b ↔
      neighbor G H s a = neighbor G H s b ∧
        (neighbors G H a).map (neighbor G H s) = (neighbors G H b).map (neighbor G H s) := by
  cases a <;> cases b <;>
    dsimp only [neighbor, neighborColor, neighbors, Sum.elim] <;>
    simp only [Multiset.map_map, Function.comp_def, Sum.elim_inl, Sum.elim_inr] <;>
    exact Prod.ext_iff

theorem neighbor_cutoff (G H : Graph) :
    (∀ s, neighborHistogram G s = neighborHistogram H s) ↔
    neighborHistogram G ((G.order + H.order)^2) = neighborHistogram H ((G.order+H.order)^2) := by
  have hr s a b (h : neighbor G H (s+1) a = neighbor G H (s+1) b) :=
    ((neighbor_update G H s a b).mp h).1
  have hs := FiniteRefinement.successor_kernel_scalar (neighbor G H) (neighbors G H)
    (neighbor_update G H)
  have he := FiniteRefinement.histogram_cutoff (neighbor G H) hr hs
    ((Finset.univ : Finset (Fin G.order)).val.map Sum.inl)
    ((Finset.univ : Finset (Fin H.order)).val.map Sum.inr)
  have hc : Fintype.card (Fin G.order ⊕ Fin H.order) = G.order + H.order := by simp
  rw [hc] at he
  simpa only [Multiset.map_map, Function.comp_def, neighbor, Sum.elim_inl,
    Sum.elim_inr, neighborHistogram] using he

def tuple (G H : Graph) (k s : ℕ) :
    (Fin k → Fin G.order) ⊕ (Fin k → Fin H.order) → TupleColor k s :=
  Sum.elim (tupleColor G k s) (tupleColor H k s)

def vectors (G H : Graph) (k : ℕ) :
    (Fin k → Fin G.order) ⊕ (Fin k → Fin H.order) →
      Multiset (Fin k → ((Fin k → Fin G.order) ⊕ (Fin k → Fin H.order)))
  | .inl x => Finset.univ.val.map (fun z i => Sum.inl (Function.update x i z))
  | .inr x => Finset.univ.val.map (fun z i => Sum.inr (Function.update x i z))

theorem tuple_update (G H : Graph) (k s : ℕ)
    (a b : (Fin k → Fin G.order) ⊕ (Fin k → Fin H.order)) :
    tuple G H k (s+1) a = tuple G H k (s+1) b ↔
      tuple G H k s a = tuple G H k s b ∧
        (vectors G H k a).map (fun v i => tuple G H k s (v i)) =
          (vectors G H k b).map (fun v i => tuple G H k s (v i)) := by
  cases a <;> cases b <;>
    dsimp only [tuple, tupleColor, vectors, Sum.elim] <;>
    simp only [Multiset.map_map, Function.comp_def] <;>
    exact Prod.ext_iff

theorem tuple_cutoff (G H : Graph) (k : ℕ) :
    (∀ s, tupleHistogram G k s = tupleHistogram H k s) ↔
    tupleHistogram G k ((G.order^k+H.order^k)^2) = tupleHistogram H k ((G.order^k+H.order^k)^2) := by
  have hr s a b (h : tuple G H k (s+1) a = tuple G H k (s+1) b) :=
    ((tuple_update G H k s a b).mp h).1
  have hs := FiniteRefinement.successor_kernel (tuple G H k) (vectors G H k)
    (tuple_update G H k)
  have he := FiniteRefinement.histogram_cutoff (tuple G H k) hr hs
    ((Finset.univ : Finset (Fin k → Fin G.order)).val.map Sum.inl)
    ((Finset.univ : Finset (Fin k → Fin H.order)).val.map Sum.inr)
  have hc : Fintype.card ((Fin k → Fin G.order) ⊕ (Fin k → Fin H.order)) =
      G.order ^ k + H.order ^ k := by simp
  rw [hc] at he
  simpa only [Multiset.map_map, Function.comp_def, tuple, Sum.elim_inl,
    Sum.elim_inr, tupleHistogram] using he

/-- Explicit finite stopping criteria, retaining neighbor refinement precisely at k=1. -/
theorem equivalent_cutoff (G H : Graph) (k : ℕ) :
    Equivalent k G H ↔
      if k = 1 then
        neighborHistogram G ((G.order+H.order)^2) = neighborHistogram H ((G.order+H.order)^2)
      else tupleHistogram G k ((G.order^k+H.order^k)^2) =
        tupleHistogram H k ((G.order^k+H.order^k)^2) := by
  unfold Equivalent
  split_ifs
  · exact neighbor_cutoff G H
  · exact tuple_cutoff G H k

end FiniteWL
namespace FiniteRefinement

/-- Image multiset equality is checked by finite class counts; there is no
unit-cost comparison of recursively expanded color trees. -/
theorem map_eq_iff_counts {A C : Type} [DecidableEq C] (f : A → C) (L M : Multiset A) :
    L.map f = M.map f ↔ ∀ a, L.countP (fun b => f b = f a) = M.countP (fun b => f b = f a) := by
  constructor
  · intro h a
    have he := congrArg (Multiset.count (f a)) h
    simpa only [Multiset.count_map, ← Multiset.countP_eq_card_filter, eq_comm] using he
  · intro h
    apply Multiset.ext.mpr
    intro c
    by_cases hc : ∃ a, f a = c
    · obtain ⟨a, rfl⟩ := hc
      simpa only [Multiset.count_map, ← Multiset.countP_eq_card_filter, eq_comm] using h a
    · have hL : c ∉ L.map f := by simpa only [Multiset.mem_map, not_exists, not_and] using
        (fun a (_ : a ∈ L) ha => hc ⟨a, ha⟩)
      have hM : c ∉ M.map f := by simpa only [Multiset.mem_map, not_exists, not_and] using
        (fun a (_ : a ∈ M) ha => hc ⟨a, ha⟩)
      rw [Multiset.count_eq_zero_of_notMem hL, Multiset.count_eq_zero_of_notMem hM]

variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

def vectorMatch (R : A → A → Bool) (v w : I → A) : Bool :=
  decide (∀ i, R (v i) (w i) = true)

def tableStep (N : A → Multiset (I → A)) (R : A → A → Bool) (a b : A) : Bool :=
  R a b && decide (∀ v : I → A,
    (N a).countP (fun w => vectorMatch R w v = true) =
    (N b).countP (fun w => vectorMatch R w v = true))

omit [DecidableEq A] in
/-- Reusable correctness of a table update, including the joint vector test. -/
theorem tableStep_correct {C D : Type} [DecidableEq C] (old : A → C) (next : A → D)
    (N : A → Multiset (I → A)) (R : A → A → Bool)
    (hR : ∀ a b, R a b = true ↔ old a = old b)
    (hnext : ∀ a b, next a = next b ↔ old a = old b ∧
      (N a).map (fun v i => old (v i)) = (N b).map (fun v i => old (v i))) (a b : A) :
    tableStep N R a b = true ↔ next a = next b := by
  rw [hnext]
  simp only [tableStep, Bool.and_eq_true, decide_eq_true_eq, hR]
  apply and_congr Iff.rfl
  rw [map_eq_iff_counts]
  have hm (w v : I → A) : vectorMatch R w v = true ↔
      (fun i => old (w i)) = (fun i => old (v i)) := by
    simp only [vectorMatch, decide_eq_true_eq, funext_iff]
    exact forall_congr' (fun i => hR (w i) (v i))
  simp only [hm]

/-- Literal finite Boolean relation iteration. -/
def table (N : A → Multiset (I → A)) (initial : A → A → Bool) (rounds : ℕ) : A → A → Bool :=
  (tableStep N)^[rounds] initial

omit [DecidableEq A] in
theorem table_correct {C : ℕ → Type} [∀ s, DecidableEq (C s)]
    (color : (s : ℕ) → A → C s) (N : A → Multiset (I → A))
    (hnext : ∀ s a b, color (s+1) a = color (s+1) b ↔ color s a = color s b ∧
      (N a).map (fun v i => color s (v i)) = (N b).map (fun v i => color s (v i)))
    (initial : A → A → Bool) (hinit : ∀ a b, initial a b = true ↔ color 0 a = color 0 b)
    (s : ℕ) (a b : A) : table N initial s a b = true ↔ color s a = color s b := by
  induction s generalizing a b with
  | zero => exact hinit a b
  | succ s ih =>
    simp only [table, Function.iterate_succ_apply']
    exact tableStep_correct (color s) (color (s+1)) N _ (fun a b => ih (a:=a) (b:=b)) (hnext s) a b

end FiniteRefinement

end WLIdentification

end OAI
