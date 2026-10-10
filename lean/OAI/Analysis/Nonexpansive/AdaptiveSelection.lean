import OAI.Analysis.Nonexpansive.Basic
import OAI.Analysis.Nonexpansive.AdaptiveRun
import OAI.Analysis.Nonexpansive.AdaptiveConvexPrefix

namespace OAI

/-!
# Finite adaptive return to an anchor

The tail closures and the anchor's closed-convex-hull membership are the
actual analytic input to this helper.  The anchor construction proves
those inputs for the actual resolvent tails.  The arbitrary state below
can retain every earlier candidate and its auxiliary detector, including
the candidates which eventually receive coefficient zero.
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace ReflexiveFixedPoints

universe u v w

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Every weak limit of points from a sequence lies in the norm-closed
convex hull of that sequence.  This uses weak closedness of a convex norm
closure, not weak continuity of any nonlinear map. -/
theorem mem_closedConvexHull_of_weak_subsequence
    (u : ℕ → X) (j : ℕ → ℕ) {d : X}
    (h : Tendsto (fun n => toWeakSpace ℝ X (u (j n))) atTop
      (𝓝 (toWeakSpace ℝ X d))) :
    d ∈ closure (convexHull ℝ (range u)) := by
  let C := closure (convexHull ℝ (range u))
  have hconv : Convex ℝ (convexHull ℝ (range u)) := convex_convexHull _ _
  have hclosed : IsClosed ((toWeakSpace ℝ X) '' C) := by
    dsimp only [C]
    rw [hconv.toWeakSpace_closure ℝ]
    exact isClosed_closure
  have hd : toWeakSpace ℝ X d ∈ (toWeakSpace ℝ X) '' C :=
    hclosed.mem_of_tendsto h (Filter.Eventually.of_forall fun n =>
      ⟨u (j n), subset_closure (subset_convexHull ℝ (range u)
        (mem_range_self (j n))), rfl⟩)
  obtain ⟨a, ha, heq⟩ := hd
  have : a = d := (toWeakSpace ℝ X).injective heq
  simpa only [this] using ha

/-- Fully state-dependent finite selection.  Every threshold is read from
the preceding state, and the legal next state is chosen after the map.
Only after a finite prefix has been obtained are its coefficients chosen.

The returned selected list includes every candidate, including those of
zero weight.  `positive_support_reindex` separately extracts the retained
children in their original order without changing this full history. -/
theorem adaptive_finite_selection
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
    ∃ (N : ℕ), 0 < N ∧
      ∃ (state : Fin (N + 1) → S) (selected : Fin N → M)
        (β : Fin N → ℝ),
        state ⟨0, Nat.succ_pos N⟩ = initial ∧
        (∀ i : Fin N,
          selected i ∈ family (threshold i (state i.castSucc)) ∧
          transition i (state i.castSucc) (selected i) (state i.succ)) ∧
        (∀ i, 0 ≤ β i) ∧ (∑ i, β i = 1) ∧
        ‖(∑ i, β i • (eval (selected i) : X)) - (x : X)‖ < τ := by
  classical
  let : MetricSpace (WeakCarrier K) :=
    TopologicalSpace.metrizableSpaceMetric (WeakCarrier K)
  have hhalf : 0 < τ / 2 := half_pos hτ
  obtain ⟨q, hq, d, lam, hdD, hlam, hlam1, havg⟩ :=
    closure_convexHull_exists_fin hx hhalf
  let target : Fin q → WeakCarrier K :=
    fun r => normToWeak K ⟨d r, hDK (hdD r)⟩
  let weval : M → WeakCarrier K := fun a => normToWeak K (eval a)
  have hclosure (i : ℕ) (s : S) (r : Fin q) :
      target r ∈ closure (weval '' family (threshold i s)) :=
    hD (threshold i s) (hthreshold i s) ⟨d r, hdD r⟩
  obtain ⟨states, selected, hstart, hrun⟩ :=
    exists_adaptive_metric_run hq target weval family threshold transition initial
      hclosure htransition
  let u : ℕ → X := fun i => eval (selected i)
  have htarget (r : Fin q) : d r ∈ closure (convexHull ℝ (range u)) := by
    have ht : Tendsto (fun n : ℕ => weval (selected (q * n + r.val)))
        atTop (𝓝 (target r)) :=
      tendsto_cyclic_target hq target (fun i => weval (selected i))
        (fun i => (hrun i).2.1) r
    have hw := (continuous_subtype_val.tendsto (target r)).comp ht
    apply mem_closedConvexHull_of_weak_subsequence u (fun n => q * n + r.val)
    simpa only [u, target, weval, Function.comp_def, normToWeak_val] using hw
  have havgmem : (∑ r, lam r • d r) ∈ closure (convexHull ℝ (range u)) := by
    have hmem : (∑ r, lam r • d r) ∈ convexHull ℝ (range d) :=
      mem_convexHull_of_exists_fintype lam d hlam hlam1 (fun i => mem_range_self i) rfl
    apply convexHull_min (t := closure (convexHull ℝ (range u))) ?_
      (convex_convexHull ℝ (range u)).closure hmem
    rintro a ⟨r, rfl⟩
    exact htarget r
  obtain ⟨N, hN, β, hβ, hβ1, hnear⟩ :=
    closure_convexHull_range_exists_prefix u havgmem hhalf
  refine ⟨N, hN, (fun i => states i), (fun i => selected i), β,
    hstart, ?_, hβ, hβ1, ?_⟩
  · intro i
    exact ⟨(hrun i).1, (hrun i).2.2⟩
  · change ‖(∑ i : Fin N, β i • u i) - (x : X)‖ < τ
    calc
      ‖(∑ i : Fin N, β i • u i) - (x : X)‖ ≤
          ‖(∑ i : Fin N, β i • u i) - (∑ r, lam r • d r)‖ +
          ‖(∑ r, lam r • d r) - (x : X)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < τ / 2 + τ / 2 := add_lt_add hnear havg
      _ = τ := add_halves τ

end ReflexiveFixedPoints

end

end OAI
