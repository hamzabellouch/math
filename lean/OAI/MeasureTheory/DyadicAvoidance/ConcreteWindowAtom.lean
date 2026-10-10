import OAI.MeasureTheory.DyadicAvoidance.WindowExceptionalTransfer
import OAI.MeasureTheory.DyadicAvoidance.WindowFixedScale
import OAI.MeasureTheory.DyadicAvoidance.RoutedExposure
import OAI.MeasureTheory.DyadicAvoidance.CenterFailureBound

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Problem310.ConcreteWindowAtom

open FiniteTableModel RoutedSetDensity RoutingPath FiniteLocalPredicate
open CenterRouteExposure CenterFailureBound WindowExceptionalTransfer WindowTrialAddresses

variable {M d g r₀ : ℕ}

/-- The concrete center atom together with all child-window trial misses. -/
def localMiss (W : WindowData (M + 1) d g r₀) (U : Node M d)
    (x t : ℝ) (ξ : Node M d × Fin M → Bool) :
    Set (SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W)) :=
  {ω | centerExposure (selectorEndpoints W) x ω.1 = ξ ∧
    ∀ z : LocalTrial W U, localQ W U ω z.1
      (x + t * (2 : ℝ)⁻¹ ^ localIndex W U z) = false}

lemma centerAtom_mass (W : WindowData (M + 1) d g r₀)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ)
    (ξ : Node M d × Fin M → Bool) :
    ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp0 hp1
      (centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) =
    ConcreteLabels.selectorLaw (SelectorAddress (selectorEndpoints W))
      {a | ∀ c : Node M d × Fin M,
        a (selectorAddress (selectorEndpoints W) c.1 c.2 x) = ξ c} := by
  have heq : centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ =
      ({a : SelectorTable (selectorEndpoints W) | ∀ c : Node M d × Fin M,
        a (selectorAddress (selectorEndpoints W) c.1 c.2 x) = ξ c} ×ˢ
        (Set.univ : Set (TerminalTable (terminalEndpoints W)))) := by
    ext ω
    simp only [centerAtom, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
    exact funext_iff
  rw [heq, ConcreteLabels.outcomeLaw, Measure.prod_prod]
  simp

/-- Exact mass of the actual local Boolean failure event, with no remaining
address-injectivity or leaf-prefix obligations. -/
theorem localMiss_mass (W : WindowData (M + 1) d g r₀) (U : Node M d)
    (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ξ : Node M d × Fin M → Bool) :
    ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp0 hp1 (localMiss W U x t ξ) =
    (ENNReal.ofReal (1 - p / 2)) ^ (M * W.r (d - U.val.length)) *
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp0 hp1
        (centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) := by
  let leaf : SelectorTable (selectorEndpoints W) → LocalTrial W U → Leaf M d :=
    fun a z => localLeaf (selectorChoice (selectorEndpoints W) a)
      (d - (U.val.length + 1)) (U.val ++ [z.1.castSucc]) (local_depth U z.1)
      (x + t * (2 : ℝ)⁻¹ ^ localIndex W U z)
  have hprefix : ∀ a z, (selectorEdge U z.1).IsPrefix (leaf a z).val := by
    intro a z
    exact prefix_routeFrom _ _ _ _
  have h := window_fixed_scale_on_center_atom W U x t ht p hp0 hp1 ξ leaf hprefix
  have heq : localMiss W U x t ξ =
      {ω : SelectorTable (selectorEndpoints W) × TerminalTable (terminalEndpoints W) |
        (∀ c : Node M d × Fin M,
          ω.1 (selectorAddress (selectorEndpoints W) c.1 c.2 x) = ξ c) ∧
        ∀ z : LocalTrial W U, ω.1 (localSelectorAddress W U x t z) = true →
          ω.2 (terminalAddress (terminalEndpoints W) (leaf ω.1 z)
            (x + t * (2 : ℝ)⁻¹ ^ localIndex W U z)) = false} := by
    ext ω
    simp only [localMiss, Set.mem_ofPred_eq, funext_iff, centerExposure,
      localQ, Bool.and_eq_false_imp, localSelectorAddress, leaf]
  rw [heq, h, centerAtom_mass]
  exact mul_comm _ _

/-- The final good-atom bound for the actual window router. The only numerical
input is precisely the uniform entropy budget returned by RoutingBudget. -/
theorem raw_failure_on_good_atom
    (W : WindowData (M + 1) d g r₀) (hM : 1 ≤ M)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbudget : ∀ r : ℕ, r₀ ≤ r → ∀ N : ℕ,
      N ≤ 1 + M * r * 2 ^ (2 * r + 2) →
      (N : ENNReal) * (ENNReal.ofReal (1 - p / 2)) ^ (M * r) ≤ ENNReal.ofReal p)
    (x : ℝ) (hstable : StableAt W x)
    (ξ : Node M d × Fin M → Bool) (hgood : GoodExposure (selectorEndpoints W) x ξ) :
    ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
      (TerminalAddress (terminalEndpoints W)) p hp0 hp1
      ({ω | x ∈ Auxiliary.exceptionalCenters
        (routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
        (Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)} ∩
        centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) ≤
    ENNReal.ofReal p *
      ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
        (TerminalAddress (terminalEndpoints W)) p hp0 hp1
        (centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ) := by
  classical
  obtain ⟨k, U, hlen, hfirst⟩ :=
    RoutedExposure.actual_firstDefaultNode_on_atom (selectorEndpoints W) x ξ hgood
  obtain ⟨R, hR, hcard, htransfer⟩ :=
    exists_representatives_failure_transfer W U k.val x ξ hfirst hstable
  let μ := ConcreteLabels.outcomeLaw (SelectorAddress (selectorEndpoints W))
    (TerminalAddress (terminalEndpoints W)) p hp0 hp1
  let A := centerAtom (selectorEndpoints W) (terminalEndpoints W) x ξ
  let q := (ENNReal.ofReal (1 - p / 2)) ^ (M * W.r (d - U.val.length))
  have hthreshold : r₀ ≤ W.r (d - U.val.length) := by
    have h := W.length_threshold (selectorEdge U (⟨0, by omega⟩ : Fin M))
      (selectorEdge_valid U _)
    simpa [WindowData.length, selectorEdge] using h
  have hsmall : (R.card : ENNReal) * q ≤ ENNReal.ofReal p :=
    hbudget _ hthreshold _ hcard
  have hsub : ({ω | x ∈ Auxiliary.exceptionalCenters
      (routedSet (selectorEndpoints W) (terminalEndpoints W) ω)
      (Ici 1) (fun n => (2 : ℝ)⁻¹ ^ n)} ∩ A) ⊆
      ⋃ t ∈ R, localMiss W U x t ξ := by
    rintro ω ⟨hfail, hatom⟩
    obtain ⟨t, ht, hmiss⟩ := htransfer ω hatom hfail
    refine mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, hatom, ?_⟩⟩
    intro z
    exact hmiss z.1 z.2
  change μ _ ≤ ENNReal.ofReal p * μ A
  calc
    μ _ ≤ μ (⋃ t ∈ R, localMiss W U x t ξ) := measure_mono hsub
    _ ≤ ∑ t ∈ R, μ (localMiss W U x t ξ) := measure_biUnion_finset_le _ _
    _ = ∑ _t ∈ R, q * μ A := by
      apply Finset.sum_congr rfl
      intro t ht
      exact localMiss_mass W U x t (hR t ht) p hp0 hp1 ξ
    _ = (R.card : ENNReal) * (q * μ A) := by simp [nsmul_eq_mul]
    _ = ((R.card : ENNReal) * q) * μ A := (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal p * μ A := mul_le_mul hsmall le_rfl (by positivity) (by positivity)

end Problem310.ConcreteWindowAtom

end

end OAI
