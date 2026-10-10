import OAI.Analysis.MetricEntropy.DirectionTuples
import OAI.Analysis.MetricEntropy.FiniteProductCounting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

universe uU uE uJ uZ

/-!
# Counting and avoiding all disjoint zero-tuple witnesses

All ordered tuples are retained, including tuples with repeated indices.
The probability product estimate is applied only to lists whose distinct
tuple supports are pairwise disjoint. Their number is bounded by the exact
number of all ordered lists, `u ^ (h * w)`.
-/

noncomputable section

open scoped BigOperators

namespace MetricEntropyDuality.DirectionSampling

open FiniteProductCounting

section FiniteUnion

variable {U : Type uU} {E : Type uE} {J : Type uJ} [Fintype U] [DecidableEq U]
  [Fintype E] [DecidableEq E] [Nonempty E]

omit [Nonempty E] in
/-- The union bound for the actual normalized finite sample counts. -/
theorem prob_biUnion_le (s : Finset J) (events : J → Finset (U → E)) :
    prob (s.biUnion events) ≤ ∑ j ∈ s, prob (events j) := by
  classical
  unfold prob
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hcard : (s.biUnion events).card ≤ ∑ j ∈ s, (events j).card :=
    Finset.card_biUnion_le
  exact_mod_cast hcard

/-- Strictly fewer than all samples in an event leaves an actual sample
outside it. Nonempty `E` also covers an empty coordinate index type. -/
theorem exists_not_mem_of_prob_lt_one (event : Finset (U → E))
    (hevent : prob event < 1) : ∃ t : U → E, t ∉ event := by
  classical
  by_contra hnone
  have hall : ∀ t : U → E, t ∈ event := by simpa only [not_exists, not_not] using hnone
  have heq : event = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  rw [heq, prob_univ] at hevent
  exact (lt_irrefl (1 : ℝ)) hevent

end FiniteUnion

section Tuples

variable {U : Type uU} {E : Type uE} [Fintype U] [DecidableEq U]
  [Fintype E] [DecidableEq E] [Nonempty E] {h w : ℕ}

omit [DecidableEq U] [DecidableEq E] [Nonempty E] in
/-- A repeated-index tuple event depends only on the distinct indices in
its literal support. -/
theorem tupleEvent_dependsOn (bad : (Fin h → E) → Prop) (a : Fin h → U) :
    DependsOn (tupleSupport a) (tupleEvent bad a) := by
  intro t s hts
  have heq : (fun j => t (a j)) = (fun j => s (a j)) := by
    funext j
    exact hts (a j) (mem_tupleSupport.mpr ⟨j, rfl⟩)
  simp only [mem_tupleEvent, heq]

/-- The event that every tuple in this particular list is bad. -/
def badListEvent (bad : (Fin h → E) → Prop) (L : Fin w → Fin h → U) :
    Finset (U → E) :=
  allEvents Finset.univ (fun j => tupleEvent bad (L j))

omit [Nonempty E] in
@[simp] theorem mem_badListEvent {bad : (Fin h → E) → Prop}
    {L : Fin w → Fin h → U} {t : U → E} :
    t ∈ badListEvent bad L ↔ ∀ j, bad (fun i => t (L j i)) := by
  classical
  simp [badListEvent, allEvents]

/-- Product estimate proved from disjoint coordinate supports; no
independence hypothesis is assumed. -/
theorem prob_badListEvent_le (bad : (Fin h → E) → Prop)
    (L : Fin w → Fin h → U) (hL : DisjointSupports L) (b : ℝ)
    (hbound : ∀ a : Fin h → U, prob (tupleEvent bad a) ≤ b) :
    prob (badListEvent bad L) ≤ b ^ w :=
  prob_all_univ_le_pow (fun j => tupleSupport (L j))
    (fun j => tupleEvent bad (L j)) (fun j => tupleEvent_dependsOn bad (L j))
    hL b (fun j => hbound (L j))

end Tuples

/-- All ordered witness lists, before imposing disjointness, are counted
exactly. Repetition within any tuple remains allowed. -/
theorem card_witnessLists (u h w : ℕ) :
    Fintype.card (Fin w → Fin h → Fin u) = u ^ (h * w) := by
  simp only [Fintype.card_fun, Fintype.card_fin, ← pow_mul]

/-- Only disjoint lists are used as bad-event witnesses. -/
def disjointLists (u h w : ℕ) : Finset (Fin w → Fin h → Fin u) := by
  classical
  exact Finset.univ.filter DisjointSupports

@[simp] theorem mem_disjointLists {u h w : ℕ} {L : Fin w → Fin h → Fin u} :
    L ∈ disjointLists u h w ↔ DisjointSupports L := by
  classical
  simp [disjointLists]

theorem card_disjointLists_le (u h w : ℕ) :
    (disjointLists u h w).card ≤ u ^ (h * w) := by
  classical
  calc
    (disjointLists u h w).card ≤ Fintype.card (Fin w → Fin h → Fin u) :=
      Finset.card_le_univ _
    _ = u ^ (h * w) := card_witnessLists u h w

section Sampling

variable {Z : Type uZ} {E : Type uE} [Fintype E] [DecidableEq E] [Nonempty E]
  {u h w : ℕ}

/-- The actual union over forms and disjoint witness lists. -/
def badSamples (forms : Finset Z) (bad : Z → (Fin h → E) → Prop) :
    Finset (Fin u → E) := by
  classical
  exact forms.biUnion fun z =>
    (disjointLists u h w).biUnion fun L => badListEvent (bad z) L

omit [Nonempty E] in
@[simp] theorem mem_badSamples {forms : Finset Z} {bad : Z → (Fin h → E) → Prop}
    {t : Fin u → E} :
    t ∈ badSamples (u := u) (w := w) forms bad ↔
      ∃ z ∈ forms, ∃ L : Fin w → Fin h → Fin u,
        DisjointSupports L ∧ ∀ j, bad z (fun i => t (L j i)) := by
  classical
  simp [badSamples]

/-- The counted union bound over the literal form set and every possible
disjoint witness list. -/
theorem prob_badSamples_le (forms : Finset Z) (bad : Z → (Fin h → E) → Prop)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ z ∈ forms, ∀ a : Fin h → Fin u, prob (tupleEvent (bad z) a) ≤ b) :
    prob (badSamples (u := u) (w := w) forms bad) ≤
      (forms.card : ℝ) * (u : ℝ) ^ (h * w) * b ^ w := by
  classical
  have hlistcard : ((disjointLists u h w).card : ℝ) ≤ (u : ℝ) ^ (h * w) := by
    exact_mod_cast card_disjointLists_le u h w
  have hinner (z : Z) (hz : z ∈ forms) :
      prob ((disjointLists u h w).biUnion fun L => badListEvent (bad z) L) ≤
        (u : ℝ) ^ (h * w) * b ^ w := by
    calc
      _ ≤ ∑ L ∈ disjointLists u h w, prob (badListEvent (bad z) L) :=
        prob_biUnion_le _ _
      _ ≤ ∑ _L ∈ disjointLists u h w, b ^ w := by
        apply Finset.sum_le_sum
        intro L hL
        exact prob_badListEvent_le (bad z) L (mem_disjointLists.mp hL) b (hbound z hz)
      _ = ((disjointLists u h w).card : ℝ) * b ^ w := by simp
      _ ≤ (u : ℝ) ^ (h * w) * b ^ w :=
        mul_le_mul_of_nonneg_right hlistcard (pow_nonneg hb w)
  calc
    _ ≤ ∑ z ∈ forms,
        prob ((disjointLists u h w).biUnion fun L => badListEvent (bad z) L) :=
      prob_biUnion_le _ _
    _ ≤ ∑ _z ∈ forms, (u : ℝ) ^ (h * w) * b ^ w :=
      Finset.sum_le_sum hinner
    _ = _ := by simp [mul_assoc]

/-- A strict union budget produces one sample excluding every disjoint
all-bad witness, simultaneously for every form in the actual finite set. -/
theorem exists_sample_avoiding (forms : Finset Z) (bad : Z → (Fin h → E) → Prop)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ z ∈ forms, ∀ a : Fin h → Fin u, prob (tupleEvent (bad z) a) ≤ b)
    (hbudget : (forms.card : ℝ) * (u : ℝ) ^ (h * w) * b ^ w < 1) :
    ∃ t : Fin u → E, ∀ z ∈ forms, ∀ L : Fin w → Fin h → Fin u,
      DisjointSupports L → ¬ ∀ j, bad z (fun i => t (L j i)) := by
  classical
  obtain ⟨t, ht⟩ := exists_not_mem_of_prob_lt_one (badSamples (u := u) (w := w) forms bad)
    ((prob_badSamples_le forms bad b hb hbound).trans_lt hbudget)
  refine ⟨t, ?_⟩
  intro z hz L hL hall
  exact ht (mem_badSamples.mpr ⟨z, hz, L, hL, hall⟩)

/-- The numerical bound used for degree-`h` forms over a field of `p`
elements. Form counts and each repeated-tuple zero bound are explicit
inputs, supplied by the actual form and polynomial constructions. -/
theorem prob_badSamples_le_field_budget (forms : Finset Z)
    (bad : Z → (Fin h → E) → Prop) (p D : ℕ) (hcard : forms.card ≤ p ^ D)
    (hbound : ∀ z ∈ forms, ∀ a : Fin h → Fin u,
      prob (tupleEvent (bad z) a) ≤ (h : ℝ) / p) :
    prob (badSamples (u := u) (w := w) forms bad) ≤
      (p : ℝ) ^ D * (u : ℝ) ^ (h * w) * ((h : ℝ) / p) ^ w := by
  have hb : 0 ≤ (h : ℝ) / p := div_nonneg (Nat.cast_nonneg h) (Nat.cast_nonneg p)
  have hc : (forms.card : ℝ) ≤ (p : ℝ) ^ D := by exact_mod_cast hcard
  exact (prob_badSamples_le forms bad ((h : ℝ) / p) hb hbound).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (pow_nonneg (Nat.cast_nonneg u) _))
      (pow_nonneg hb _))

theorem exists_sample_avoiding_of_field_budget (forms : Finset Z)
    (bad : Z → (Fin h → E) → Prop) (p D : ℕ) (hcard : forms.card ≤ p ^ D)
    (hbound : ∀ z ∈ forms, ∀ a : Fin h → Fin u,
      prob (tupleEvent (bad z) a) ≤ (h : ℝ) / p)
    (hbudget : (p : ℝ) ^ D * (u : ℝ) ^ (h * w) * ((h : ℝ) / p) ^ w < 1) :
    ∃ t : Fin u → E, ∀ z ∈ forms, ∀ L : Fin w → Fin h → Fin u,
      DisjointSupports L → ¬ ∀ j, bad z (fun i => t (L j i)) := by
  classical
  obtain ⟨t, ht⟩ := exists_not_mem_of_prob_lt_one (badSamples (u := u) (w := w) forms bad)
    ((prob_badSamples_le_field_budget forms bad p D hcard hbound).trans_lt hbudget)
  refine ⟨t, ?_⟩
  intro z hz L hL hall
  exact ht (mem_badSamples.mpr ⟨z, hz, L, hL, hall⟩)

end Sampling

end MetricEntropyDuality.DirectionSampling

end

end OAI
