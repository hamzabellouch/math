import OAI.MeasureTheory.DyadicAvoidance.StableRoutingBridge
import OAI.MeasureTheory.DyadicAvoidance.FiniteLocalPredicate
import OAI.MeasureTheory.DyadicAvoidance.RoutedSetDensity

namespace OAI

noncomputable section
namespace Problem310.FiniteLocalHit

open FiniteTableModel StableRouting RoutingPath OrderedRouting FiniteLocalPredicate

variable {M d : ℕ}

/-- A successful concrete child-local test is a successful terminal lookup on the
actual root route. Only the earlier center-path selectors must be stable. -/
theorem local_test_implies_root_hit
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ωS : SelectorTable bS) (ωT : TerminalTable bT)
    (k r : ℕ) (U : Node M d) (i : Fin M) (x y : ℝ)
    (hdepth : (U.val ++ [i.castSucc]).length + r = d)
    (hU : routeFrom (select (selectorValue bS ωS)) k [] x = U.val)
    (hnd : ∀ l < k, select (selectorValue bS ωS)
      (routeFrom (select (selectorValue bS ωS)) l [] x) x ≠ Fin.last M)
    (hprefix : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ select (selectorValue bS ωS)
        (routeFrom (select (selectorValue bS ωS)) l [] x) x →
      selectorValue bS ωS (routeFrom (select (selectorValue bS ωS)) l [] x) j x =
      selectorValue bS ωS (routeFrom (select (selectorValue bS ωS)) l [] x) j y)
    (hdefault : select (selectorValue bS ωS) U.val x = Fin.last M)
    (hearlier : ∀ j < i, selectorValue bS ωS U.val j x = selectorValue bS ωS U.val j y)
    (hlocal : (ωS (selectorAddress bS U i y) &&
      ωT (terminalAddress bT
        (localLeaf (select (selectorValue bS ωS)) r (U.val ++ [i.castSucc]) hdepth y) y)) = true) :
    ωT (terminalAddress bT
      (localLeaf (select (selectorValue bS ωS)) d [] (by simp) y) y) = true := by
  have hklength : k = U.val.length := by
    have h := congrArg List.length hU
    simpa using h
  have htotal : k + 1 + r = d := by
    simpa only [List.length_append, List.length_singleton, ← hklength] using hdepth
  simp only [Bool.and_eq_true] at hlocal
  obtain ⟨hselector, hterminal⟩ := hlocal
  have hi : select (selectorValue bS ωS) U.val y = i.castSucc := by
    apply chooseChild_of_local_success
    · exact rejects_earlier_at_default (selectorValue bS ωS) U.val x y i hdefault hearlier
    · simpa using hselector
  have hroute : routeFrom (select (selectorValue bS ωS)) d [] y =
      routeFrom (select (selectorValue bS ωS)) r (U.val ++ [i.castSucc]) y := by
    apply (congrArg (fun n => routeFrom (select (selectorValue bS ωS)) n [] y) htotal).symm.trans
    apply routeFrom_eq_local_route _ k r [] U.val x y i.castSucc hU ?_ hi
    intro l hl
    exact select_eq_of_earlier_agreement (selectorValue bS ωS) _ x y
      (hnd l hl) (hprefix l hl)
  have hleaf : localLeaf (select (selectorValue bS ωS)) d [] (by simp) y =
      localLeaf (select (selectorValue bS ωS)) r (U.val ++ [i.castSucc]) hdepth y :=
    Subtype.ext hroute
  rw [hleaf]
  exact hterminal

/-- Final canonical-set form of the local-hit implication. This uses precisely the
concrete `selectorChoice`, `localLeaf`, and `routedSet` definitions of the model. -/
theorem local_test_mem_routedSet
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (ωS : SelectorTable bS) (ωT : TerminalTable bT)
    (k r : ℕ) (U : Node M d) (i : Fin M) (x y : ℝ)
    (hdepth : (U.val ++ [i.castSucc]).length + r = d)
    (hU : routeFrom (RoutedSetDensity.selectorChoice bS ωS) k [] x = U.val)
    (hnd : ∀ l < k, RoutedSetDensity.selectorChoice bS ωS
      (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) x ≠ Fin.last M)
    (hprefix : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ RoutedSetDensity.selectorChoice bS ωS
        (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) x →
      selectorValue bS ωS (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) j x =
      selectorValue bS ωS (routeFrom (RoutedSetDensity.selectorChoice bS ωS) l [] x) j y)
    (hdefault : RoutedSetDensity.selectorChoice bS ωS U.val x = Fin.last M)
    (hearlier : ∀ j < i, selectorValue bS ωS U.val j x = selectorValue bS ωS U.val j y)
    (hlocal : (ωS (selectorAddress bS U i y) &&
      ωT (terminalAddress bT
        (localLeaf (RoutedSetDensity.selectorChoice bS ωS) r (U.val ++ [i.castSucc]) hdepth y) y)) = true) :
    y ∈ RoutedSetDensity.routedSet bS bT (ωS, ωT) := by
  exact local_test_implies_root_hit bS bT ωS ωT k r U i x y hdepth hU hnd
    hprefix hdefault hearlier hlocal

end Problem310.FiniteLocalHit

end

end OAI
