import OAI.MeasureTheory.DyadicAvoidance.WindowData
import OAI.MeasureTheory.DyadicAvoidance.StableRoutingBridge
import OAI.MeasureTheory.DyadicAvoidance.GridSeparation
import OAI.MeasureTheory.DyadicAvoidance.FiniteTableModel

namespace OAI

universe u_X

noncomputable section

namespace Problem310.WindowLocalHit

open RoutingPath StableRouting GridSeparation

variable {q d g r₀ : ℕ} {X : Type u_X}

/-- Every selector used at an earlier routed node precedes an incoming edge
below that route, provided its child index is no later than the chosen child. -/
theorem ancestor_selector_gap (W : WindowData q d g r₀)
    (choose : List (Fin q) → X → Fin q) (x : X)
    {k l : ℕ} (hkl : k < l) (hld : l < d) (i j : Fin q)
    (hj : j ≤ choose (routeFrom choose k [] x) x) :
    W.b (routeFrom choose k [] x ++ [j]) + g <
      W.a (routeFrom choose l [] x ++ [i]) := by
  have hvalid (n : ℕ) (hn : n < d) (c : Fin q) :
      ValidWindowEdge d (routeFrom choose n [] x ++ [c]) := by
    constructor
    · simp
    · simp only [List.length_append, length_routeFrom, List.length_nil,
        List.length_singleton, zero_add]
      omega
  have hpre : (routeFrom choose (k + 1) [] x).IsPrefix (routeFrom choose l [] x) := by
    have h := prefix_routeFrom choose (l - (k + 1)) (routeFrom choose (k + 1) [] x) x
    rw [← routeFrom_add, Nat.add_sub_of_le (by omega : k + 1 ≤ l)] at h
    exact h
  have hwhole : (routeFrom choose k [] x ++ [choose (routeFrom choose k [] x) x]).IsPrefix
      (routeFrom choose l [] x ++ [i]) :=
    hpre.trans (List.prefix_append _ _)
  rcases lt_or_eq_of_le hj with hj | rfl
  · obtain ⟨tail, htail⟩ := hwhole
    have heq : routeFrom choose k [] x ++ choose (routeFrom choose k [] x) x :: tail =
        routeFrom choose l [] x ++ [i] := by
      simpa only [List.append_assoc, List.singleton_append] using htail
    have hgap := W.gap_sibling (routeFrom choose k [] x) j
      (choose (routeFrom choose k [] x) x) tail hj
      (hvalid k (hkl.trans hld) j) (by rw [heq]; exact hvalid l hld i)
    rwa [heq] at hgap
  · apply W.gap_prefix _ _ (hvalid k (hkl.trans hld) _) (hvalid l hld i) hwhole
    intro heq
    have hlen := congrArg List.length heq
    simp only [List.length_append, length_routeFrom, List.length_nil,
      List.length_singleton, zero_add] at hlen
    omega

variable {M : ℕ}

/-- Canonical finite-table selectors satisfy the key-factor hypothesis of the
window-routing lemma whenever their endpoint map is taken from `W`. -/
theorem selectorValue_factors_window_key (W : WindowData (M + 1) d g r₀)
    (bS : FiniteTableModel.Node M d → Fin M → ℕ)
    (ωS : FiniteTableModel.SelectorTable bS)
    (hbS : ∀ (P : FiniteTableModel.Node M d) (j : Fin M),
      bS P j = W.b (P.val ++ [j.castSucc]))
    (P : List (Fin (M + 1))) (hP : P.length < d) (j : Fin M) (u v : ℝ)
    (hkey : dyadicKey (W.b (P ++ [j.castSucc])) u =
      dyadicKey (W.b (P ++ [j.castSucc])) v) :
    FiniteTableModel.selectorValue bS ωS P j u =
      FiniteTableModel.selectorValue bS ωS P j v := by
  have heq : dyadicKey (bS ⟨P, hP⟩ j) u = dyadicKey (bS ⟨P, hP⟩ j) v := by
    rw [hbS ⟨P, hP⟩ j]
    exact hkey
  simp only [FiniteTableModel.selectorValue, dite_eq_left hP]
  exact congrArg (fun key => ωS ⟨((⟨P, hP⟩ : FiniteTableModel.Node M d), j), key⟩) heq


/-- The actual window geometry turns uniform stable-grid agreement into the
local-route identity at a first-default node. This is the concrete geometric
input to the local-hit implication; no probability assumptions are used. -/
theorem route_eq_local_of_window_stability (W : WindowData (M + 1) d g r₀)
    (S : List (Fin (M + 1)) → Fin M → ℝ → Bool)
    (hS : ∀ (P : List (Fin (M + 1))), P.length < d →
      ∀ (j : Fin M) (u v : ℝ),
        dyadicKey (W.b (P ++ [j.castSucc])) u =
          dyadicKey (W.b (P ++ [j.castSucc])) v → S P j u = S P j v)
    (x t : ℝ) (n k r : ℕ) (i : Fin M)
    (hdepth : k + 1 + r = d) (_ht : t ∈ Set.Icc (1 : ℝ) 2)
    (hn : n ∈ W.window (routeFrom (select S) k [] x ++ [i.castSucc]))
    (hstable : ∀ E : List (Fin (M + 1)), ValidWindowEdge d E →
      W.b E + g < n → dyadicKey (W.b E) x =
        dyadicKey (W.b E) (x + t * ((2 : ℝ)⁻¹ ^ n)))
    (hnd : ∀ l < k, select S (routeFrom (select S) l [] x) x ≠ Fin.last M)
    (hdefault : select S (routeFrom (select S) k [] x) x = Fin.last M)
    (hi : S (routeFrom (select S) k [] x) i (x + t * ((2 : ℝ)⁻¹ ^ n)) = true) :
    routeFrom (select S) d [] (x + t * ((2 : ℝ)⁻¹ ^ n)) =
      routeFrom (select S) r (routeFrom (select S) k [] x ++ [i.castSucc])
        (x + t * ((2 : ℝ)⁻¹ ^ n)) := by
  have hk : k < d := by omega
  have hnlow : W.a (routeFrom (select S) k [] x ++ [i.castSucc]) ≤ n :=
    (Finset.mem_Icc.mp hn).1
  have hvalid (l : ℕ) (hl : l < d) (j : Fin M) :
      ValidWindowEdge d (routeFrom (select S) l [] x ++ [j.castSucc]) := by
    constructor
    · simp
    · simp only [List.length_append, length_routeFrom, List.length_nil,
        List.length_singleton, zero_add]
      omega
  have hprefix : ∀ l < k, ∀ j : Fin M,
      j.castSucc ≤ select S (routeFrom (select S) l [] x) x →
      S (routeFrom (select S) l [] x) j x =
        S (routeFrom (select S) l [] x) j (x + t * ((2 : ℝ)⁻¹ ^ n)) := by
    intro l hl j hj
    apply hS _ (by simpa only [length_routeFrom, List.length_nil, zero_add] using hl.trans hk)
    apply hstable _ (hvalid l (hl.trans hk) j)
    exact (ancestor_selector_gap W (select S) x hl hk i.castSucc j.castSucc hj).trans_le hnlow
  have hearlier : ∀ j < i,
      S (routeFrom (select S) k [] x) j x =
        S (routeFrom (select S) k [] x) j (x + t * ((2 : ℝ)⁻¹ ^ n)) := by
    intro j hj
    apply hS _ (by simpa only [length_routeFrom, List.length_nil, zero_add] using hk)
    apply hstable _ (hvalid k hk j)
    exact (W.gap_sibling (routeFrom (select S) k [] x) j.castSucc i.castSucc []
      (by simpa using hj) (hvalid k hk j) (hvalid k hk i)).trans_le hnlow
  rw [← hdepth]
  apply terminal_success_of_stable_local_success S
    (fun Q _ => Q = routeFrom (select S) r
      (routeFrom (select S) k [] x ++ [i.castSucc]) (x + t * ((2 : ℝ)⁻¹ ^ n)))
    k r [] (routeFrom (select S) k [] x) x (x + t * ((2 : ℝ)⁻¹ ^ n)) i
    rfl hnd hprefix hdefault hearlier hi rfl

end Problem310.WindowLocalHit

end

end OAI
