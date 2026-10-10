import Mathlib

namespace OAI

namespace PerfectMatchingPSD

abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def IsPerfectMatching {n : ℕ} (M : Finset (Edge n)) : Prop :=
  ∀ v : Fin n, (M.filter fun e => e.1.1 = v ∨ e.1.2 = v).card = 1

abbrev PerfectMatching (n : ℕ) :=
  {M : Finset (Edge n) // IsPerfectMatching M}

noncomputable def matchingPoint {n : ℕ} (M : PerfectMatching n) : Edge n → ℝ := by
  classical
  exact fun e => if e ∈ M.1 then 1 else 0

noncomputable def matchingPolytope (n : ℕ) : Set (Edge n → ℝ) :=
  convexHull ℝ (Set.range (matchingPoint (n := n)))

def HasAffineLift (n r : ℕ) : Prop :=
  ∃ (L : AffineSubspace ℝ (Matrix (Fin r) (Fin r) ℝ))
    (T : Matrix (Fin r) (Fin r) ℝ →ᵃ[ℝ] (Edge n → ℝ)),
    T '' {X | X ∈ L ∧ X.PosSemidef} = matchingPolytope n

theorem affine_lift_lower_bound :
    ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, 4 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → Even n → ∀ r : ℕ,
        HasAffineLift n r → (n : ℝ) ^ C < (r : ℝ) := by
  sorry

end PerfectMatchingPSD

end OAI
