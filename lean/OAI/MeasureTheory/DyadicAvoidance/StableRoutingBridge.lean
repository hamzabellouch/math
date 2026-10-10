import OAI.MeasureTheory.DyadicAvoidance.OrderedRouting
import OAI.MeasureTheory.DyadicAvoidance.RoutingPath

namespace OAI

universe u_X

noncomputable section

namespace Problem310.StableRouting

open OrderedRouting RoutingPath

variable {M : ℕ} {X : Type u_X}

/-- Ordered routing associated to the spatial selector values. -/
def select (S : List (Fin (M + 1)) → Fin M → X → Bool)
    (P : List (Fin (M + 1))) (x : X) : Fin (M + 1) :=
  chooseChild (fun i => S P i x)

/-- A nondefault decision is unchanged if all selectors up to that decision agree. -/
theorem select_eq_of_earlier_agreement
    (S : List (Fin (M + 1)) → Fin M → X → Bool)
    (P : List (Fin (M + 1))) (x y : X)
    (hnd : select S P x ≠ Fin.last M)
    (hagree : ∀ j : Fin M, j.castSucc ≤ select S P x → S P j x = S P j y) :
    select S P y = select S P x := by
  generalize hc : select S P x = c at *
  induction c using Fin.lastCases with
  | last => exact (hnd rfl).elim
  | cast i =>
    exact chooseChild_preserved (fun j => S P j x) (fun j => S P j y) i hc
      (fun j hj => hagree j (Fin.castSucc_le_castSucc_iff.mpr hj))

/-- Stable earlier selector addresses preserve the path before its first default. -/
theorem route_eq_of_earlier_selector_agreement
    (S : List (Fin (M + 1)) → Fin M → X → Bool)
    (k : ℕ) (P : List (Fin (M + 1))) (x y : X)
    (hnd : ∀ l < k, select S (routeFrom (select S) l P x) x ≠ Fin.last M)
    (hagree : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ select S (routeFrom (select S) l P x) x →
      S (routeFrom (select S) l P x) j x = S (routeFrom (select S) l P x) j y) :
    routeFrom (select S) k P y = routeFrom (select S) k P x := by
  apply routeFrom_eq_of_choices_eq
  intro l hl
  exact select_eq_of_earlier_agreement S _ x y (hnd l hl) (hagree l hl)

/-- At a center's default node, preserving the earlier selectors rejects those children. -/
theorem rejects_earlier_at_default
    (S : List (Fin (M + 1)) → Fin M → X → Bool)
    (U : List (Fin (M + 1))) (x y : X) (i : Fin M)
    (hdefault : select S U x = Fin.last M)
    (hagree : ∀ j < i, S U j x = S U j y) :
    ∀ j < i, S U j y = false := by
  intro j hj
  rw [← hagree j hj]
  exact (chooseChild_eq_default_iff (fun j => S U j x)).mp hdefault j

/-- The local-hit implication, with its geometric input isolated as
selector agreement. Later sibling selectors and off-prefix choices are unrestricted. -/
theorem terminal_success_of_stable_local_success
    (S : List (Fin (M + 1)) → Fin M → X → Bool)
    (terminal : List (Fin (M + 1)) → X → Prop)
    (k r : ℕ) (P U : List (Fin (M + 1))) (x y : X) (i : Fin M)
    (hU : routeFrom (select S) k P x = U)
    (hnd : ∀ l < k, select S (routeFrom (select S) l P x) x ≠ Fin.last M)
    (hprefix : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ select S (routeFrom (select S) l P x) x →
      S (routeFrom (select S) l P x) j x = S (routeFrom (select S) l P x) j y)
    (hdefault : select S U x = Fin.last M)
    (hearlier : ∀ j < i, S U j x = S U j y)
    (hi : S U i y = true)
    (hlocal : terminal (routeFrom (select S) r (U ++ [i.castSucc]) y) y) :
    terminal (routeFrom (select S) (k + 1 + r) P y) y := by
  apply terminal_success_of_local_success (select S) terminal k r P U x y i.castSucc hU
  · intro l hl
    exact select_eq_of_earlier_agreement S _ x y (hnd l hl) (hprefix l hl)
  · exact chooseChild_of_local_success (fun j => S U j y) i
      (rejects_earlier_at_default S U x y i hdefault hearlier) hi
  · exact hlocal

end Problem310.StableRouting

end

end OAI
