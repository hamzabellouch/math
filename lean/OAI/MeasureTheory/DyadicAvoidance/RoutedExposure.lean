import OAI.MeasureTheory.DyadicAvoidance.CenterRouteExposure
import OAI.MeasureTheory.DyadicAvoidance.RoutedSetDensity

namespace OAI

noncomputable section

namespace Problem310.RoutedExposure
open FiniteTableModel RoutingPath CenterRouteExposure RoutedSetDensity

@[simp] theorem selectorChoice_eq_centerChoice {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (ω : SelectorTable b)
    (P : List (Child M)) (x : ℝ) :
    selectorChoice b ω P x = centerChoice b x P ω := rfl

/-- Translate from spatial routing with tables fixed to routing the table outcome
with the center fixed. No decision or node representation is changed. -/
theorem routedPath_eq_centerRoute {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (ω : SelectorTable b) (x : ℝ)
    (n : ℕ) (P : List (Child M)) :
    routeFrom (selectorChoice b ω) n P x = routeFrom (centerChoice b x) n P ω :=
  routeFrom_congr_at _ _ x ω (fun _ => rfl) n P

/-- The actual finite terminal leaf at the center is fixed on each exposure atom. -/
theorem routedLeaf_eq_of_centerExposure_eq {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) {ω ω' : SelectorTable b}
    (h : centerExposure b x ω = centerExposure b x ω') :
    routedLeaf b ω x = routedLeaf b ω' x := by
  apply Subtype.ext
  change routeFrom (selectorChoice b ω) d [] x = routeFrom (selectorChoice b ω') d [] x
  rw [routedPath_eq_centerRoute, routedPath_eq_centerRoute]
  exact centerRoute_eq_of_centerExposure_eq b x h d []

/-- Therefore the actual terminal table address at the center is fixed as well. -/
theorem routedAddress_eq_of_centerExposure_eq {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ) (x : ℝ)
    {ω ω' : SelectorTable bS} (h : centerExposure bS x ω = centerExposure bS x ω') :
    routedAddress bS bT ω x = routedAddress bS bT ω' x := by
  simp only [routedAddress, routedLeaf_eq_of_centerExposure_eq bS x h]

/-- The bad-exposure event in the atom average is exactly the actual raw router's
no-default event, in the notation of `RoutedSetDensity`. -/
theorem badExposure_iff_actual_no_default {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ω : SelectorTable b) :
    ¬ GoodExposure b x (centerExposure b x ω) ↔
      ∀ k < d, selectorChoice b ω (routeFrom (selectorChoice b ω) k [] x) x ≠ Fin.last M := by
  rw [badExposure_centerExposure_iff]
  simp only [routedPath_eq_centerRoute, selectorChoice_eq_centerChoice]

/-- A good exposure supplies the actual bounded first-default node, fixed before
any remaining selector or terminal-table coordinates are revealed. -/
theorem actual_firstDefaultNode_on_atom {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool)
    (hgood : GoodExposure b x ξ) :
    ∃ k : Fin d, ∃ U : Node M d, U.val.length = k.val ∧
      ∀ ω : SelectorTable b, centerExposure b x ω = ξ →
        routeFrom (selectorChoice b ω) k.val [] x = U.val ∧
        selectorChoice b ω U.val x = Fin.last M ∧
        ∀ l < k.val,
          selectorChoice b ω (routeFrom (selectorChoice b ω) l [] x) x ≠ Fin.last M := by
  obtain ⟨k, U, hlen, hU⟩ := firstDefaultNode_on_atom b x ξ hgood
  refine ⟨k, U, hlen, ?_⟩
  intro ω hω
  obtain ⟨hroute, _, hdefault, hprior⟩ := hU ω hω
  have hactual : routeFrom (selectorChoice b ω) k.val [] x = U.val := by
    rw [routedPath_eq_centerRoute]
    exact hroute
  refine ⟨hactual, ?_, ?_⟩
  · change centerChoice b x U.val ω = Fin.last M
    rwa [hroute] at hdefault
  · intro l hl
    simpa only [routedPath_eq_centerRoute, selectorChoice_eq_centerChoice] using hprior l hl

end Problem310.RoutedExposure

end

end OAI
