import OAI.MeasureTheory.DyadicAvoidance.AddressInjectivity
import OAI.MeasureTheory.DyadicAvoidance.RoutingPath
import OAI.MeasureTheory.DyadicAvoidance.TrialAddresses

namespace OAI

universe u_I u_A u_L

noncomputable section

namespace Problem310.AddressInjectivity

/-- Terminal addresses of actual local dyadic routes are distinct, including
when terminal leaves are represented by a finite subtype or a fixed-length
vector. `path` forgets that finite representation. This is the concrete bridge
to the injective-address hypothesis of the adaptive-label product law. -/
theorem dyadic_routed_terminalAddress_injective {I : Type u_I} {A : Type u_A} {L : Type u_L}
    (choose : List A → ℝ → A) (r : ℕ) (U : List A)
    (child : I → A) (n : I → ℕ) (leaf : I → L) (path : L → List A)
    (b : A → ℕ) (B : L → ℕ) (x t : ℝ)
    (hpath : ∀ i, path (leaf i) = RoutingPath.routeFrom choose r
      (U ++ [child i]) (x + t * (2 : ℝ)⁻¹ ^ n i))
    (htlo : 1 ≤ t) (hthi : t ≤ 2)
    (hnlo : ∀ i, 3 ≤ n i) (hnhi : ∀ i, n i ≤ b (child i))
    (hrefine : ∀ i, b (child i) ≤ B (leaf i))
    (hpair : Function.Injective (fun i => (child i, n i))) :
    Function.Injective (TrialAddresses.trialAddress B leaf n x t) := by
  apply TrialAddresses.terminalAddress_injective child n leaf b B x t
    htlo hthi hnlo hnhi hrefine
  · intro i j hij
    have hr : RoutingPath.routeFrom choose r (U ++ [child i])
          (x + t * (2 : ℝ)⁻¹ ^ n i) =
        RoutingPath.routeFrom choose r (U ++ [child j])
          (x + t * (2 : ℝ)⁻¹ ^ n j) := by
      rw [← hpath i, ← hpath j, hij]
    exact child_eq_of_common_descendant
      (RoutingPath.prefix_routeFrom choose r (U ++ [child i]) _)
      (hr.symm ▸ RoutingPath.prefix_routeFrom choose r (U ++ [child j]) _)
  · exact hpair

end Problem310.AddressInjectivity

end

end OAI
