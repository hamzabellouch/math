import Mathlib

namespace OAI

/-!
# Integer shortest-path metrics and Lipschitz descent
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree.NatMetricClosure
open scoped Classical

variable {X : Type*} (w : X → X → ℕ)

def cost (x y : X) : List X → ℕ
  | [] => w x y
  | z :: zs => w x z + cost z y zs

@[simp] theorem cost_nil (x y : X) : cost w x y [] = w x y := rfl
@[simp] theorem cost_cons (x y z : X) (zs : List X) :
    cost w x y (z::zs) = w x z + cost w z y zs := rfl

theorem cost_append (x y z : X) (u v : List X) :
    cost w x z (u ++ y::v) = cost w x y u + cost w y z v := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, cost_cons, ih, Nat.add_assoc]

theorem cost_reverse (hs : ∀ x y, w x y = w y x) (x y : X) (u : List X) :
    cost w x y u = cost w y x u.reverse := by
  induction u generalizing x with
  | nil => exact hs x y
  | cons z u ih =>
    simp only [cost_cons, List.reverse_cons, cost_append, cost_nil]
    rw [ih, hs x z, Nat.add_comm]

def distance (x y : X) : ℕ :=
  Nat.find (show ∃ n : ℕ, ∃ u : List X, cost w x y u = n from ⟨w x y, [], rfl⟩)

theorem distance_le_cost (x y : X) (u : List X) : distance w x y ≤ cost w x y u :=
  Nat.find_min' _ ⟨u, rfl⟩

theorem exists_shortest (x y : X) : ∃ u : List X, cost w x y u = distance w x y :=
  Nat.find_spec (show ∃ n : ℕ, ∃ u : List X, cost w x y u = n from ⟨w x y, [], rfl⟩)

theorem distance_le (x y : X) : distance w x y ≤ w x y := distance_le_cost w x y []

theorem distance_self (hz : ∀ x, w x x = 0) (x : X) : distance w x x = 0 := by
  have h := distance_le w x x
  rw [hz] at h
  exact Nat.eq_zero_of_le_zero h

theorem distance_comm (hs : ∀ x y, w x y = w y x) (x y : X) :
    distance w x y = distance w y x := by
  have h (a b : X) : distance w a b ≤ distance w b a := by
    obtain ⟨u, hu⟩ := exists_shortest w b a
    calc
      distance w a b ≤ cost w a b u.reverse := distance_le_cost _ _ _ _
      _ = cost w b a u := (cost_reverse w hs b a u).symm
      _ = distance w b a := hu
  exact le_antisymm (h x y) (h y x)

theorem distance_triangle (x y z : X) :
    distance w x z ≤ distance w x y + distance w y z := by
  obtain ⟨u, hu⟩ := exists_shortest w x y
  obtain ⟨v, hv⟩ := exists_shortest w y z
  calc
    distance w x z ≤ cost w x z (u ++ y::v) := distance_le_cost _ _ _ _
    _ = distance w x y + distance w y z := by rw [cost_append, hu, hv]

theorem cost_zero (hz : ∀ x y, w x y = 0 → x = y)
    (x y : X) (u : List X) (h : cost w x y u = 0) : x = y := by
  induction u generalizing x with
  | nil => exact hz x y h
  | cons z u ih =>
    have hh := Nat.add_eq_zero_iff.mp h
    exact (hz x z hh.1).trans (ih z hh.2)

theorem distance_zero (hz : ∀ x y, w x y = 0 → x = y)
    (x y : X) (h : distance w x y = 0) : x = y := by
  obtain ⟨u, hu⟩ := exists_shortest w x y
  exact cost_zero w hz x y u (hu.trans h)

abbrev metricSpace (hself : ∀ x, w x x = 0) (hsym : ∀ x y, w x y = w y x)
    (hzero : ∀ x y, w x y = 0 → x = y) : MetricSpace X where
  dist x y := distance w x y
  dist_self x := by simp [distance_self w hself]
  dist_comm x y := by rw [distance_comm w hsym]
  dist_triangle x y z := by exact_mod_cast distance_triangle w x y z
  eq_of_dist_eq_zero {x y} h := distance_zero w hzero x y (by exact_mod_cast h)

theorem separated (hself : ∀ x, w x x = 0) (hsym : ∀ x y, w x y = w y x)
    (hzero : ∀ x y, w x y = 0 → x = y) {x y : X} (hxy : x ≠ y) :
    letI := metricSpace w hself hsym hzero
    1 ≤ dist x y := by
  change (1 : ℝ) ≤ (distance w x y : ℝ)
  have h : 1 ≤ distance w x y := Nat.one_le_iff_ne_zero.mpr (fun h => hxy (distance_zero w hzero x y h))
  exact_mod_cast h

theorem lipschitz_bound {Y : Type*} [PseudoMetricSpace Y] (f : X → Y)
    (hf : ∀ x y, dist (f x) (f y) ≤ (w x y : ℝ)) (x y : X) :
    dist (f x) (f y) ≤ (distance w x y : ℝ) := by
  have hcost (u : List X) (a : X) : dist (f a) (f y) ≤ cost w a y u := by
    induction u generalizing a with
    | nil => exact hf a y
    | cons b u ih =>
      calc
        dist (f a) (f y) ≤ dist (f a) (f b) + dist (f b) (f y) := dist_triangle _ _ _
        _ ≤ (w a b : ℝ) + cost w b y u := add_le_add (hf a b) (ih b)
        _ = (cost w a y (b::u) : ℝ) := by rw [cost_cons, Nat.cast_add]
  obtain ⟨u, hu⟩ := exists_shortest w x y
  simpa [hu] using hcost u x

theorem path_relation (P : ℕ → X → X → Prop)
    (hedge : ∀ x y, P (w x y) x y)
    (htrans : ∀ a b x y z, P a x y → P b y z → P (a+b) x z)
    (x y : X) : P (distance w x y) x y := by
  have hcost (u : List X) (a : X) : P (cost w a y u) a y := by
    induction u generalizing a with
    | nil => exact hedge a y
    | cons b u ih => exact htrans _ _ _ _ _ (hedge a b) (ih b)
  obtain ⟨u, hu⟩ := exists_shortest w x y
  simpa [hu] using hcost u x

end DiscreteFree.NatMetricClosure

end

end

end OAI
