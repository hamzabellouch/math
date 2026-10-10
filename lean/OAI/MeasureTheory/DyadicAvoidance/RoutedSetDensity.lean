import OAI.MeasureTheory.DyadicAvoidance.FiniteTableModel
import OAI.MeasureTheory.DyadicAvoidance.OrderedRouting
import OAI.MeasureTheory.DyadicAvoidance.RoutingPath
import OAI.MeasureTheory.DyadicAvoidance.RandomSetDensity

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem310.RoutedSetDensity

open FiniteTableModel

/-- The actual first-success/default child choice made by the finite selector tables. -/
def selectorChoice {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (x : ℝ) : Child M :=
  OrderedRouting.chooseChild (fun i => selectorValue b ω P i x)

/-- The leaf reached by the root router, as an element of the finite leaf type. -/
def routedLeaf {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (x : ℝ) : Leaf M d :=
  ⟨RoutingPath.routeFrom (selectorChoice b ω) d [] x, by simp⟩

/-- The terminal table coordinate consulted by the complete finite router. -/
def routedAddress {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ω : SelectorTable bS) (x : ℝ) : TerminalAddress bT :=
  terminalAddress bT (routedLeaf bS ω x) x

/-- The raw random periodic set, with both selector and terminal tables explicit. -/
def routedSet {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ω : SelectorTable bS × TerminalTable bT) : Set ℝ :=
  RandomSetDensity.selectedSet (routedAddress bS bT) ω

lemma measurable_selectorChoice {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) : Measurable (selectorChoice b ω P) := by
  classical
  exact (measurable_of_finite (OrderedRouting.chooseChild (M := M))).comp
    (measurable_pi_iff.mpr fun i => measurable_selectorValue b ω P i)

@[simp] lemma selectorChoice_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (x : ℝ) :
    selectorChoice b ω P (x + 1) = selectorChoice b ω P x := by
  apply OrderedRouting.chooseChild_congr
  intro i
  exact selectorValue_add_one b ω P i x

lemma measurable_routedLeaf {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) : Measurable (routedLeaf b ω) := by
  let : MeasurableSpace (List (Child M)) := ⊤
  let : DiscreteMeasurableSpace (List (Child M)) := ⟨fun _ => trivial⟩
  have hchoose : Measurable (Function.uncurry (selectorChoice b ω)) :=
    measurable_from_prod_countable_right (measurable_selectorChoice b ω)
  have hroute := RoutingPath.measurable_routeFrom (selectorChoice b ω) hchoose d []
  apply measurable_to_countable
  intro y
  convert (measurableSet_singleton
    (RoutingPath.routeFrom (selectorChoice b ω) d [] y)).preimage hroute using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, routedLeaf]
  exact List.Vector.toList_injective.eq_iff.symm

@[simp] lemma routedLeaf_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (x : ℝ) : routedLeaf b ω (x + 1) = routedLeaf b ω x := by
  apply Subtype.ext
  exact RoutingPath.routeFrom_periodic (selectorChoice b ω) (selectorChoice_add_one b ω) d [] x

lemma measurable_routedAddress {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (ω : SelectorTable bS) : Measurable (routedAddress bS bT ω) := by
  have hterminal : Measurable (fun z : Leaf M d × ℝ => terminalAddress bT z.1 z.2) :=
    measurable_from_prod_countable_right (measurable_terminalAddress bT)
  exact hterminal.comp ((measurable_routedLeaf bS ω).prodMk measurable_id)

@[simp] lemma routedAddress_add_one {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (ω : SelectorTable bS) (x : ℝ) :
    routedAddress bS bT ω (x + 1) = routedAddress bS bT ω x := by
  simp [routedAddress]

lemma measurableSet_routedSet {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (ω : SelectorTable bS × TerminalTable bT) :
    MeasurableSet (routedSet bS bT ω) :=
  RandomSetDensity.measurableSet_selectedSet _ (measurable_routedAddress bS bT) ω

lemma routedSet_periodic {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (ω : SelectorTable bS × TerminalTable bT) (x : ℝ) :
    x + 1 ∈ routedSet bS bT ω ↔ x ∈ routedSet bS bT ω :=
  RandomSetDensity.periodic_selectedSet _ (routedAddress_add_one bS bT) ω x

/-- Exact density of the concrete raw routed blocker, with no spatial regularity hypotheses. -/
theorem expected_routedSet_density {M d : ℕ} (bS : Node M d → Fin M → ℕ)
    (bT : Leaf M d → ℕ) (P : Measure (SelectorTable bS)) [IsProbabilityMeasure P]
    (ν : Measure Bool) [IsProbabilityMeasure ν] :
    (∫⁻ ω, volume (routedSet bS bT ω ∩ Set.Icc (0 : ℝ) 1)
      ∂(P.prod (Measure.pi (fun _ : TerminalAddress bT => ν)))) = ν {true} := by
  classical
  exact RandomSetDensity.expected_density_selectedSet P ν _ (measurable_routedAddress bS bT)

end Problem310.RoutedSetDensity

end

end OAI
