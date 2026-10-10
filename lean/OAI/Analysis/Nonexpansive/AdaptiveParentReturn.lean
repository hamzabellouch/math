import OAI.Analysis.Nonexpansive.AdaptiveSelection

namespace OAI

/-!
# Finite parent returns with their full adaptive history

The finite return is obtained from `adaptive_finite_selection`.  Its full
candidate list and all successive states remain available, including the
candidates of coefficient zero.  A separate order embedding identifies
exactly the positive coefficients used as retained children.
-/

noncomputable section

open Set
open scoped Topology BigOperators

namespace ReflexiveFixedPoints

universe u v w

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Ordered positive-support extraction, including its exact range. -/
theorem positive_support_reindex_exact {N : ℕ}
    (u : Fin N → X) (β : Fin N → ℝ)
    (hβ : ∀ i, 0 ≤ β i) (hβ1 : ∑ i, β i = 1) :
    ∃ (q : ℕ), 0 < q ∧ ∃ (e : Fin q ↪o Fin N),
      (∀ j, 0 < β (e j)) ∧ (∑ j, β (e j) = 1) ∧
      ((∑ j, β (e j) • u (e j)) = ∑ i, β i • u i) ∧
      ∀ i, (∃ j, e j = i) ↔ 0 < β i := by
  classical
  let s := Finset.univ.filter (fun i => 0 < β i)
  have hz (i : Fin N) (hi : i ∉ s) : β i = 0 := by
    have hn : ¬ 0 < β i := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact le_antisymm (le_of_not_gt hn) (hβ i)
  have hm : (∑ i ∈ s, β i) = 1 := by
    calc
      (∑ i ∈ s, β i) = ∑ i, β i :=
        Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hz i hi)
      _ = 1 := hβ1
  have hq : 0 < s.card := by
    apply Finset.card_pos.mpr
    by_contra h
    have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have : (0 : ℝ) = 1 := by
      simpa only [hs, Finset.sum_empty] using hm
    exact zero_ne_one this
  refine ⟨s.card, hq, s.orderEmbOfFin rfl, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (Finset.mem_filter.mp (s.orderEmbOfFin_mem rfl j)).2
  · exact (sum_ordered_finset s β).trans hm
  · exact (sum_ordered_finset s (fun i => β i • u i)).trans
      (Finset.sum_subset (Finset.subset_univ s)
        (fun i _ hi => by rw [hz i hi, zero_smul]))
  · intro i
    change i ∈ Set.range (s.orderEmbOfFin rfl) ↔ 0 < β i
    rw [Finset.range_orderEmbOfFin]
    change i ∈ s ↔ 0 < β i
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A finite return to one parent.  `state` and `selected` describe the
entire legal sequence.  `retain` extracts exactly its positive coefficients in
the original order, without discarding any of the stored transitions. -/
structure AdaptiveParentReturn {K : Set X} {M : Type v} {S : Type w}
    (eval : M → K) (family : ℕ → Set M) (x : K)
    (threshold : ℕ → S → ℕ)
    (transition : ℕ → S → M → S → Prop) (initial : S) (τ : ℝ) where
  N : ℕ
  N_pos : 0 < N
  state : Fin (N + 1) → S
  selected : Fin N → M
  β : Fin N → ℝ
  start : state ⟨0, Nat.succ_pos N⟩ = initial
  legal : ∀ i : Fin N,
    selected i ∈ family (threshold i (state i.castSucc)) ∧
      transition i (state i.castSucc) (selected i) (state i.succ)
  β_nonneg : ∀ i, 0 ≤ β i
  β_sum : ∑ i, β i = 1
  near : ‖(∑ i, β i • (eval (selected i) : X)) - (x : X)‖ < τ
  q : ℕ
  q_pos : 0 < q
  retain : Fin q ↪o Fin N
  retained_pos : ∀ j, 0 < β (retain j)
  retained_sum : ∑ j, β (retain j) = 1
  retained_average :
    (∑ j, β (retain j) • (eval (selected (retain j)) : X)) =
      ∑ i, β i • (eval (selected i) : X)
  retain_range : ∀ i, (∃ j, retain j = i) ↔ 0 < β i

/-- The retained children have the same return estimate as the full sequence. -/
theorem AdaptiveParentReturn.retained_near
    {K : Set X} {M : Type v} {S : Type w}
    {eval : M → K} {family : ℕ → Set M} {x : K}
    {threshold : ℕ → S → ℕ}
    {transition : ℕ → S → M → S → Prop} {initial : S} {τ : ℝ}
    (r : AdaptiveParentReturn eval family x threshold transition initial τ) :
    ‖(∑ j, r.β (r.retain j) • (eval (r.selected (r.retain j)) : X)) -
      (x : X)‖ < τ := by
  rw [r.retained_average]
  exact r.near

/-- Actual finite parent returns exist by adaptive finite selection and
ordered support extraction; no finite-return law is assumed. -/
theorem adaptive_parent_return_nonempty
    {K : Set X} [TopologicalSpace.MetrizableSpace (WeakCarrier K)]
    {M : Type v} {S : Type w}
    (eval : M → K) (family : ℕ → Set M) (x : K) (D : Set X)
    (hDK : D ⊆ K)
    (hx : (x : X) ∈ closure (convexHull ℝ D))
    (hD : ∀ m, 1 ≤ m → ∀ d : D,
      normToWeak K ⟨d, hDK d.property⟩ ∈
        closure ((fun a => normToWeak K (eval a)) '' family m))
    (threshold : ℕ → S → ℕ)
    (hthreshold : ∀ i s, 1 ≤ threshold i s)
    (transition : ℕ → S → M → S → Prop) (initial : S)
    (htransition : ∀ i s a,
      a ∈ family (threshold i s) → ∃ s', transition i s a s')
    {τ : ℝ} (hτ : 0 < τ) :
    Nonempty (AdaptiveParentReturn eval family x threshold transition initial τ) := by
  obtain ⟨N, hN, state, selected, β, hstart, hlegal, hβ, hβ1, hnear⟩ :=
    adaptive_finite_selection eval family x D hDK hx hD threshold hthreshold
      transition initial htransition hτ
  obtain ⟨q, hq, retain, hpos, hsum, havg, hrange⟩ :=
    positive_support_reindex_exact (fun i => (eval (selected i) : X)) β hβ hβ1
  exact ⟨{
    N := N
    N_pos := hN
    state := state
    selected := selected
    β := β
    start := hstart
    legal := hlegal
    β_nonneg := hβ
    β_sum := hβ1
    near := hnear
    q := q
    q_pos := hq
    retain := retain
    retained_pos := hpos
    retained_sum := hsum
    retained_average := havg
    retain_range := hrange
  }⟩

/-- Choose the proved finite parent return, retaining all its witnesses. -/
def adaptive_parent_return
    {K : Set X} [TopologicalSpace.MetrizableSpace (WeakCarrier K)]
    {M : Type v} {S : Type w}
    (eval : M → K) (family : ℕ → Set M) (x : K) (D : Set X)
    (hDK : D ⊆ K)
    (hx : (x : X) ∈ closure (convexHull ℝ D))
    (hD : ∀ m, 1 ≤ m → ∀ d : D,
      normToWeak K ⟨d, hDK d.property⟩ ∈
        closure ((fun a => normToWeak K (eval a)) '' family m))
    (threshold : ℕ → S → ℕ)
    (hthreshold : ∀ i s, 1 ≤ threshold i s)
    (transition : ℕ → S → M → S → Prop) (initial : S)
    (htransition : ∀ i s a,
      a ∈ family (threshold i s) → ∃ s', transition i s a s')
    {τ : ℝ} (hτ : 0 < τ) :
    AdaptiveParentReturn eval family x threshold transition initial τ :=
  Classical.choice (adaptive_parent_return_nonempty eval family x D hDK hx hD
    threshold hthreshold transition initial htransition hτ)

end ReflexiveFixedPoints

end

end OAI
