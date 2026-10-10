import Mathlib

namespace OAI

universe u_A u_I u_X u_K

noncomputable section

namespace Problem310.AddressInjectivity

/-- Two descendants of different children cannot be the same leaf. -/
theorem child_eq_of_common_descendant {A : Type u_A} {U L : List A} {i j : A}
    (hi : U ++ [i] <+: L) (hj : U ++ [j] <+: L) : i = j := by
  have hi' := List.prefix_iff_eq_take.mp hi
  have hj' := List.prefix_iff_eq_take.mp hj
  have heq : U ++ [i] = U ++ [j] := by
    rw [hi', hj']
    simp
  simpa using List.append_cancel_left heq

/-- A pointwise-selected terminal leaf still gives distinct terminal table addresses.
The selected leaf may depend arbitrarily on the selector outcome: only its child
subtree and the refinement of its terminal grid matter. -/
theorem terminalAddress_injective {I : Type u_I} {A : Type u_A} {X : Type u_X} {K : Type u_K}
    (U : List A) (child : I → A) (point : I → X)
    (leaf : I → List A) (base : A → ℕ) (level : List A → ℕ)
    (key : ℕ → X → K)
    (hprefix : ∀ i, U ++ [child i] <+: leaf i)
    (hlevel : ∀ i, base (child i) ≤ level (leaf i))
    (hrefine : ∀ {b B : ℕ} {x y : X}, b ≤ B →
      key B x = key B y → key b x = key b y)
    (hseparate : ∀ {i j : I}, child i = child j → i ≠ j →
      key (base (child i)) (point i) ≠ key (base (child i)) (point j)) :
    Function.Injective (fun i => (leaf i, key (level (leaf i)) (point i))) := by
  intro i j hij
  have hleaf : leaf i = leaf j := congrArg Prod.fst hij
  have hchild : child i = child j :=
    child_eq_of_common_descendant (hprefix i) (hleaf.symm ▸ hprefix j)
  have hkey : key (level (leaf i)) (point i) = key (level (leaf i)) (point j) := by
    have h := congrArg Prod.snd hij
    simpa only [hleaf] using h
  by_contra hne
  exact hseparate hchild hne (hrefine (hlevel i) hkey)

/-- Selector trials in different child windows use different tables; within a
window coarse-key separation gives different entries. -/
theorem selectorAddress_injective {I : Type u_I} {A : Type u_A} {X : Type u_X} {K : Type u_K}
    (child : I → A) (point : I → X) (key : A → X → K)
    (hseparate : ∀ {i j : I}, child i = child j → i ≠ j →
      key (child i) (point i) ≠ key (child i) (point j)) :
    Function.Injective (fun i => (child i, key (child i) (point i))) := by
  intro i j hij
  have hchild : child i = child j := congrArg Prod.fst hij
  have hkey : key (child i) (point i) = key (child i) (point j) := by
    have h := congrArg Prod.snd hij
    simpa only [hchild] using h
  by_contra hne
  exact hseparate hchild hne hkey

/-- Freshness is against the entire exposed center-address set, not merely the
entries on the center's actual route. -/
theorem selectorAddress_ne_centerAddress {I : Type u_I} {A : Type u_A} {X : Type u_X} {K : Type u_K}
    (child : I → A) (point : I → X) (key : A → X → K) (x : X)
    (hfresh : ∀ i, key (child i) (point i) ≠ key (child i) x)
    (i : I) (a : A) :
    (child i, key (child i) (point i)) ≠ (a, key a x) := by
  intro h
  have hchild : child i = a := congrArg Prod.fst h
  have hkey := congrArg Prod.snd h
  apply hfresh i
  simpa only [hchild] using hkey

/-- Consequently all selected trial addresses are disjoint from the exposed
center addresses, as required by finite-product conditioning. -/
theorem disjoint_selector_center_ranges {I : Type u_I} {A : Type u_A} {X : Type u_X} {K : Type u_K}
    (child : I → A) (point : I → X) (key : A → X → K) (x : X)
    (hfresh : ∀ i, key (child i) (point i) ≠ key (child i) x) :
    Disjoint (Set.range (fun i => (child i, key (child i) (point i))))
      (Set.range (fun a => (a, key a x))) := by
  rw [Set.disjoint_left]
  rintro z ⟨i, rfl⟩ ⟨a, ha⟩
  exact selectorAddress_ne_centerAddress child point key x hfresh i a ha.symm

end Problem310.AddressInjectivity

end

end OAI
