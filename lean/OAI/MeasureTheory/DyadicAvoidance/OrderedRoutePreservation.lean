import OAI.MeasureTheory.DyadicAvoidance.OrderedRouting
import OAI.MeasureTheory.DyadicAvoidance.RoutingPath

namespace OAI

universe u_X

noncomputable section

namespace Problem310.OrderedRoutePreservation

open OrderedRouting RoutingPath

variable {M : ℕ} {X : Type u_X}

/-- The node-choice function induced by ordered selector tables. -/
def routingChoice (S : List (Fin (M + 1)) → X → Fin M → Bool) :
    List (Fin (M + 1)) → X → Fin (M + 1) :=
  fun P x => chooseChild (S P x)

/-- Agreement of exactly the selector entries queried along a nondefault
center path preserves its common prefix. Later siblings need not agree. -/
theorem preserved_prefix (S : List (Fin (M + 1)) → X → Fin M → Bool)
    (k : ℕ) (P : List (Fin (M + 1))) (x y : X)
    (hnd : ∀ l < k,
      routingChoice S (routeFrom (routingChoice S) l P x) x ≠ Fin.last M)
    (hstable : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ routingChoice S (routeFrom (routingChoice S) l P x) x →
      S (routeFrom (routingChoice S) l P x) x j =
        S (routeFrom (routingChoice S) l P x) y j) :
    routeFrom (routingChoice S) k P y = routeFrom (routingChoice S) k P x := by
  apply routeFrom_eq_of_choices_eq
  intro l hl
  let Q := routeFrom (routingChoice S) l P x
  let i := (routingChoice S Q x).castPred (hnd l hl)
  have hi : routingChoice S Q x = i.castSucc :=
    (Fin.castSucc_castPred _ (hnd l hl)).symm
  have hy : chooseChild (S Q y) = i.castSucc := by
    apply chooseChild_preserved (S Q x) (S Q y) i hi
    intro j hji
    apply hstable l hl j
    rw [hi]
    simpa using hji
  exact hy.trans hi.symm

/-- At a default center node, stable earlier sibling selectors remain rejected,
so the successful local selector chooses the tested child. -/
theorem child_of_default_local_success
    (S : List (Fin (M + 1)) → X → Fin M → Bool)
    (U : List (Fin (M + 1))) (x y : X) (i : Fin M)
    (hdefault : routingChoice S U x = Fin.last M)
    (hstable : ∀ j < i, S U x j = S U y j)
    (hsuccess : S U y i = true) : routingChoice S U y = i.castSucc := by
  apply chooseChild_of_local_success
  · intro j hji
    rw [← hstable j hji]
    exact (chooseChild_eq_default_iff (S U x)).mp hdefault j
  · exact hsuccess

/-- The full deterministic route-preservation implication of the random routing
construction, independent of the numerical grid and probability implementations. -/
theorem terminal_success_of_stable_local_test
    (S : List (Fin (M + 1)) → X → Fin M → Bool)
    (terminal : List (Fin (M + 1)) → X → Prop)
    (k r : ℕ) (P U : List (Fin (M + 1))) (x y : X) (i : Fin M)
    (hU : routeFrom (routingChoice S) k P x = U)
    (hnd : ∀ l < k,
      routingChoice S (routeFrom (routingChoice S) l P x) x ≠ Fin.last M)
    (hancestors : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ routingChoice S (routeFrom (routingChoice S) l P x) x →
      S (routeFrom (routingChoice S) l P x) x j =
        S (routeFrom (routingChoice S) l P x) y j)
    (hdefault : routingChoice S U x = Fin.last M)
    (hearlier : ∀ j < i, S U x j = S U y j)
    (hsuccess : S U y i = true)
    (hterminal : terminal (routeFrom (routingChoice S) r (U ++ [i.castSucc]) y) y) :
    terminal (routeFrom (routingChoice S) (k + 1 + r) P y) y := by
  have hp := preserved_prefix S k P x y hnd hancestors
  rw [hU] at hp
  have hi := child_of_default_local_success S U x y i hdefault hearlier hsuccess
  rw [routeFrom_add, routeFrom_succ, hp, hi]
  exact hterminal

end Problem310.OrderedRoutePreservation

end

end OAI
