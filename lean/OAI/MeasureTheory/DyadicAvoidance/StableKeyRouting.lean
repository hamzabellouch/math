import OAI.MeasureTheory.DyadicAvoidance.StableRoutingBridge
import OAI.MeasureTheory.DyadicAvoidance.FiniteTableModel

namespace OAI

noncomputable section
namespace Problem310.StableKeyRouting

open FiniteTableModel StableRouting RoutingPath

variable {M d : ℕ}

/-- Agreement of the precise table key is enough to preserve a total selector lookup;
nodes outside the finite routing tree consult no table. -/
theorem selectorValue_eq_of_own_key_eq (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (i : Fin M) (x y : ℝ)
    (hkey : ∀ h : P.length < d,
      GridSeparation.dyadicKey (b ⟨P, h⟩ i) x = GridSeparation.dyadicKey (b ⟨P, h⟩ i) y) :
    selectorValue b ω P i x = selectorValue b ω P i y := by
  by_cases h : P.length < d
  · simp only [selectorValue, dite_eq_left h]
    apply congrArg ω
    unfold selectorAddress
    congr 1
    exact hkey h
  · simp only [selectorValue, dite_eq_right h]

/-- Concrete finite-table version of the local-hit routing lemma. The geometric input
is only equality of the grid keys used in earlier routing decisions. -/
theorem terminal_success_of_stable_keys
    (b : Node M d → Fin M → ℕ) (ω : SelectorTable b)
    (terminal : List (Child M) → ℝ → Prop)
    (k r : ℕ) (P U : List (Child M)) (x y : ℝ) (i : Fin M)
    (hU : routeFrom (select (selectorValue b ω)) k P x = U)
    (hnd : ∀ l < k,
      select (selectorValue b ω) (routeFrom (select (selectorValue b ω)) l P x) x ≠ Fin.last M)
    (hprefix : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ select (selectorValue b ω)
        (routeFrom (select (selectorValue b ω)) l P x) x →
      ∀ h : (routeFrom (select (selectorValue b ω)) l P x).length < d,
      GridSeparation.dyadicKey
        (b ⟨routeFrom (select (selectorValue b ω)) l P x, h⟩ j) x =
      GridSeparation.dyadicKey
        (b ⟨routeFrom (select (selectorValue b ω)) l P x, h⟩ j) y)
    (hdefault : select (selectorValue b ω) U x = Fin.last M)
    (hearlier : ∀ j < i, ∀ h : U.length < d,
      GridSeparation.dyadicKey (b ⟨U, h⟩ j) x =
        GridSeparation.dyadicKey (b ⟨U, h⟩ j) y)
    (hi : selectorValue b ω U i y = true)
    (hlocal : terminal
      (routeFrom (select (selectorValue b ω)) r (U ++ [i.castSucc]) y) y) :
    terminal (routeFrom (select (selectorValue b ω)) (k + 1 + r) P y) y := by
  apply terminal_success_of_stable_local_success (selectorValue b ω) terminal k r P U x y i
    hU hnd ?_ hdefault ?_ hi hlocal
  · intro l hl j hj
    exact selectorValue_eq_of_own_key_eq b ω _ j x y (hprefix l hl j hj)
  · intro j hj
    exact selectorValue_eq_of_own_key_eq b ω U j x y (hearlier j hj)

end Problem310.StableKeyRouting

end

end OAI
