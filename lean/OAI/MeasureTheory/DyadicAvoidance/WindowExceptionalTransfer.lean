import OAI.MeasureTheory.DyadicAvoidance.WindowLocalFactor
import OAI.MeasureTheory.DyadicAvoidance.WindowLocalHit
import OAI.MeasureTheory.DyadicAvoidance.FiniteLocalHit
import OAI.MeasureTheory.DyadicAvoidance.CenterRouteExposure
import OAI.MeasureTheory.DyadicAvoidance.ExceptionalCenters

namespace OAI

noncomputable section
namespace Problem310.WindowExceptionalTransfer

open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate CenterRouteExposure

variable {M d g r₀ : ℕ}

lemma local_depth (U : Node M d) (i : Fin M) :
    (U.val ++ [i.castSucc]).length + (d - (U.val.length + 1)) = d := by
  have h := U.property
  simp only [List.length_append, List.length_singleton]
  omega

/-- The actual local Boolean test, using the canonical tables and subtree router. -/
def localQ (W : WindowData (M + 1) d g r₀) (U : Node M d)
    (ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W))
    (i : Fin M) (y : ℝ) : Bool :=
  ω.1 (selectorAddress (selectorEndpoints W) U i y) &&
    ω.2 (terminalAddress (terminalEndpoints W)
      (localLeaf (selectorChoice (selectorEndpoints W) ω.1)
        (d - (U.val.length + 1)) (U.val ++ [i.castSucc]) (local_depth U i) y) y)

/-- Stability in precisely the selector-value form supplied by the canonical
window stability construction. -/
def StableAt (W : WindowData (M + 1) d g r₀) (x : ℝ) : Prop :=
  ∀ (P : Node M d) (i : Fin M) (n : ℕ),
    W.b (P.val ++ [i.castSucc]) + g < n →
    ∀ t ∈ Set.Icc (1 : ℝ) 2, ∀ ω : SelectorTable (selectorEndpoints W),
      selectorValue (selectorEndpoints W) ω P.val i x =
        selectorValue (selectorEndpoints W) ω P.val i (x + t * (2 : ℝ)⁻¹ ^ n)

lemma localQ_mem_routedSet (W : WindowData (M + 1) d g r₀)
    (U : Node M d) (k : ℕ) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W))
    (hU : routeFrom (selectorChoice (selectorEndpoints W) ω.1) k [] x = U.val)
    (hdefault : selectorChoice (selectorEndpoints W) ω.1 U.val x = Fin.last M)
    (hprior : ∀ l < k, selectorChoice (selectorEndpoints W) ω.1
      (routeFrom (selectorChoice (selectorEndpoints W) ω.1) l [] x) x ≠ Fin.last M)
    (hstable : StableAt W x) (i : Fin M) (n : ℕ)
    (hn : W.a (U.val ++ [i.castSucc]) ≤ n)
    (hq : localQ W U ω i (x + t * (2 : ℝ)⁻¹ ^ n) = true) :
    x + t * (2 : ℝ)⁻¹ ^ n ∈ routedSet (selectorEndpoints W) (terminalEndpoints W) ω := by
  have hlen : k = U.val.length := by
    have h := congrArg List.length hU
    simpa using h
  have hk : k < d := by rw [hlen]; exact U.property
  apply FiniteLocalHit.local_test_mem_routedSet (selectorEndpoints W) (terminalEndpoints W)
    ω.1 ω.2 k (d - (U.val.length + 1)) U i x (x + t * (2 : ℝ)⁻¹ ^ n)
    (local_depth U i) hU hprior ?_ hdefault ?_ hq
  · intro l hl j hj
    have hP : (routeFrom (selectorChoice (selectorEndpoints W) ω.1) l [] x).length < d := by
      simpa using hl.trans hk
    apply hstable ⟨_, hP⟩ j n ?_ t ht ω.1
    have hgap := WindowLocalHit.ancestor_selector_gap W
      (selectorChoice (selectorEndpoints W) ω.1) x hl hk i.castSucc j.castSucc hj
    rw [hU] at hgap
    exact hgap.trans_le hn
  · intro j hj
    apply hstable U j n ?_ t ht ω.1
    have hgap := W.gap_sibling U.val j.castSucc i.castSucc []
      (by simpa using hj) (selectorEdge_valid U j) (selectorEdge_valid U i)
    exact hgap.trans_le hn

/-- Raw exceptional failure on a fixed good center atom transfers to one finite
representative scale at which every actual local Boolean trial fails. -/
theorem exists_representatives_failure_transfer
    (W : WindowData (M + 1) d g r₀) (U : Node M d) (k : ℕ) (x : ℝ)
    (ξ : Node M d × Fin M → Bool)
    (hfirst : ∀ ω : SelectorTable (selectorEndpoints W),
      centerExposure (selectorEndpoints W) x ω = ξ →
      routeFrom (selectorChoice (selectorEndpoints W) ω) k [] x = U.val ∧
      selectorChoice (selectorEndpoints W) ω U.val x = Fin.last M ∧
      ∀ l < k, selectorChoice (selectorEndpoints W) ω
        (routeFrom (selectorChoice (selectorEndpoints W) ω) l [] x) x ≠ Fin.last M)
    (hstable : StableAt W x) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * W.r (d - U.val.length) * 2 ^ (2 * W.r (d - U.val.length) + 2) ∧
      ∀ ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W),
        centerExposure (selectorEndpoints W) x ω.1 = ξ →
        x ∈ Auxiliary.exceptionalCenters
          (routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
          (Set.Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n) →
        ∃ t ∈ R, ∀ (i : Fin M) (j : Fin (W.r (d - U.val.length))),
          localQ W U ω i
            (x + t * (2 : ℝ)⁻¹ ^ (W.a (U.val ++ [i.castSucc]) + j.val)) = false := by
  obtain ⟨R, hR, hcard, hrep⟩ := WindowLocalFactor.exists_concrete_local_representatives
    W U x (selectorChoice (selectorEndpoints W))
    (fun _ => OrderedRouting.chooseChild) (fun _ _ _ => rfl)
    (d - (U.val.length + 1)) (local_depth U) (localQ W U) (fun _ _ _ => rfl)
  refine ⟨R, hR, hcard, ?_⟩
  intro ω hω hfail
  obtain ⟨t, ht, havoid⟩ := hfail
  obtain ⟨t', ht', heq⟩ := hrep t ht
  refine ⟨t', ht', ?_⟩
  intro i j
  rw [heq ω i j]
  obtain ⟨hU, hdefault, hprior⟩ := hfirst ω.1 hω
  have hn : 1 ≤ W.a (U.val ++ [i.castSucc]) + j.val := by
    have h : 3 ≤ W.a (U.val ++ [i.castSucc]) := W.start_three _ (selectorEdge_valid U i)
    omega
  cases hq : localQ W U ω i
      (x + t * (2 : ℝ)⁻¹ ^ (W.a (U.val ++ [i.castSucc]) + j.val)) with
  | false => rfl
  | true =>
    exact False.elim (havoid _ hn
      (localQ_mem_routedSet W U k x t ht ω hU hdefault hprior hstable i _
        (Nat.le_add_right _ _) hq))

end Problem310.WindowExceptionalTransfer

end

end OAI
