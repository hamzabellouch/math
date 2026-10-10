import OAI.MeasureTheory.DyadicAvoidance.LocalPredicateFactor
import OAI.MeasureTheory.DyadicAvoidance.FiniteTableModel

namespace OAI

noncomputable section

namespace Problem310.FiniteLocalPredicate

open RoutingPath GridSeparation LocalPredicateFactor FiniteTableModel

variable {M d : ℕ}

/-- The leaf reached from a local child, with its ambient-depth proof retained. -/
def localLeaf (choose : List (Child M) → ℝ → Child M)
    (r : ℕ) (P : List (Child M)) (hdepth : P.length + r = d) (x : ℝ) : Leaf M d :=
  ⟨routeFrom choose r P x, (length_routeFrom choose r P x).trans hdepth⟩

/-- Table lookup at a valid node depends only on a finer common grid. -/
theorem selector_lookup_eq {b : Node M d → Fin M → ℕ} (ω : SelectorTable b)
    (Q : Node M d) (i : Fin M) {B : ℕ} (hb : b Q i ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    ω (selectorAddress b Q i x) = ω (selectorAddress b Q i y) := by
  exact table_eq_of_finest_key hb (fun k => ω ⟨(Q, i), k⟩) hxy

/-- The analogous statement for an actual dependent terminal-table address. -/
theorem terminal_lookup_eq {b : Leaf M d → ℕ} (ω : TerminalTable b)
    (L : Leaf M d) {B : ℕ} (hb : b L ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    ω (terminalAddress b L x) = ω (terminalAddress b L y) := by
  exact table_eq_of_finest_key hb (fun k => ω ⟨L, k⟩) hxy

/-- Concrete local terminal predicates in the finite table model factor through
the largest resolution in the child subtree. `rule` may be the canonical
first-success/default rule; no assumptions on that rule are needed. -/
theorem finite_local_predicate_factors
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ωS : SelectorTable bS) (ωT : TerminalTable bT)
    (choose : List (Child M) → ℝ → Child M)
    (rule : List (Child M) → (Fin M → Bool) → Child M)
    (hchoose : ∀ Q x, choose Q x = rule Q (fun i => selectorValue bS ωS Q i x))
    (r : ℕ) (P : List (Child M)) (hdepth : P.length + r = d)
    (U : Node M d) (i : Fin M) (B : ℕ)
    (hbS : ∀ Q : Node M d, P.IsPrefix Q.val → ∀ j, bS Q j ≤ B)
    (hbT : ∀ L : Leaf M d, P.IsPrefix L.val → bT L ≤ B)
    (hIn : bS U i ≤ B) {x y : ℝ}
    (hxy : ⌊(2 : ℝ) ^ (B + 2) * Int.fract x⌋ =
      ⌊(2 : ℝ) ^ (B + 2) * Int.fract y⌋) :
    (ωS (selectorAddress bS U i x) &&
      ωT (terminalAddress bT (localLeaf choose r P hdepth x) x)) =
    (ωS (selectorAddress bS U i y) &&
      ωT (terminalAddress bT (localLeaf choose r P hdepth y) y)) := by
  have hchoice : ∀ Q : List (Child M), P.IsPrefix Q → Q.length < P.length + r →
      ∀ u v : ℝ, ⌊(2 : ℝ) ^ (B + 2) * Int.fract u⌋ =
        ⌊(2 : ℝ) ^ (B + 2) * Int.fract v⌋ → choose Q u = choose Q v := by
    intro Q hPQ hlen u v huv
    have hQ : Q.length < d := hlen.trans_eq hdepth
    rw [hchoose Q u, hchoose Q v]
    apply congrArg (rule Q)
    funext j
    have hlook := selector_lookup_eq ωS (⟨Q, hQ⟩ : Node M d) j
      (hbS ⟨Q, hQ⟩ hPQ j) huv
    simpa only [selectorValue, dite_eq_left hQ] using hlook
  have hroute := route_eq_of_key_eq choose
    (fun z : ℝ => ⌊(2 : ℝ) ^ (B + 2) * Int.fract z⌋) r P hchoice hxy
  have hleaf : localLeaf choose r P hdepth x = localLeaf choose r P hdepth y :=
    Subtype.ext hroute
  have hprefix : P.IsPrefix (localLeaf choose r P hdepth y).val :=
    prefix_routeFrom choose r P y
  rw [selector_lookup_eq ωS U i hIn hxy, hleaf,
    terminal_lookup_eq ωT (localLeaf choose r P hdepth y) (hbT _ hprefix) hxy]

end Problem310.FiniteLocalPredicate

end

end OAI
