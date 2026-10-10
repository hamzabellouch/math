import OAI.MeasureTheory.DyadicAvoidance.AddressInjectivity
import OAI.MeasureTheory.DyadicAvoidance.RoutingPath

namespace OAI

universe u_I u_A u_X u_K

noncomputable section

namespace Problem310.AddressInjectivity

/-- The terminal-address bridge specialized to the canonical recursive router.
This applies separately to every selector outcome, with no probabilistic
independence assumption on the selected leaves. -/
theorem routedTerminalAddress_injective {I : Type u_I} {A : Type u_A} {X : Type u_X} {K : Type u_K}
    (choose : List A → X → A) (r : ℕ) (U : List A)
    (child : I → A) (point : I → X)
    (base : A → ℕ) (level : List A → ℕ) (key : ℕ → X → K)
    (hlevel : ∀ i, base (child i) ≤
      level (RoutingPath.routeFrom choose r (U ++ [child i]) (point i)))
    (hrefine : ∀ {b B : ℕ} {x y : X}, b ≤ B →
      key B x = key B y → key b x = key b y)
    (hseparate : ∀ {i j : I}, child i = child j → i ≠ j →
      key (base (child i)) (point i) ≠ key (base (child i)) (point j)) :
    Function.Injective (fun i =>
      (RoutingPath.routeFrom choose r (U ++ [child i]) (point i),
       key (level (RoutingPath.routeFrom choose r (U ++ [child i]) (point i)))
         (point i))) := by
  apply terminalAddress_injective U child point
    (fun i => RoutingPath.routeFrom choose r (U ++ [child i]) (point i))
    base level key
  · intro i
    exact RoutingPath.prefix_routeFrom choose r (U ++ [child i]) (point i)
  · exact hlevel
  · exact hrefine
  · exact hseparate

/-- In particular, routes starting in distinct child subtrees always end at
distinct leaves, even at different spatial points. -/
theorem routed_leaves_ne_of_child_ne {A : Type u_A} {X : Type u_X}
    (choose : List A → X → A) (r s : ℕ) (U : List A)
    {i j : A} (hij : i ≠ j) (x y : X) :
    RoutingPath.routeFrom choose r (U ++ [i]) x ≠
      RoutingPath.routeFrom choose s (U ++ [j]) y := by
  intro h
  exact hij (child_eq_of_common_descendant
    (RoutingPath.prefix_routeFrom choose r (U ++ [i]) x)
    (h.symm ▸ RoutingPath.prefix_routeFrom choose s (U ++ [j]) y))

end Problem310.AddressInjectivity

end

end OAI
