import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

universe u

noncomputable section

namespace MetricEntropyDuality

open Filter Topology
open scoped BigOperators Pointwise

abbrev RealSpace (ι : Type u) := ι → ℝ

def pairing {ι : Type u} [Fintype ι] (x y : RealSpace ι) : ℝ :=
  ∑ i, x i * y i

def cube (ι : Type u) : Set (RealSpace ι) :=
  {x | ∀ i, |x i| ≤ 1}

def polar {ι : Type u} [Fintype ι] (K : Set (RealSpace ι)) : Set (RealSpace ι) :=
  {y | ∀ x ∈ K, pairing x y ≤ 1}

def Covers {ι : Type u} {M : ℕ} (A B : Set (RealSpace ι))
    (centers : Fin M → RealSpace ι) : Prop :=
  ∀ x ∈ A, ∃ j, x - centers j ∈ B

def Coverable {ι : Type u} (A B : Set (RealSpace ι)) : Prop :=
  ∃ M : ℕ, ∃ centers : Fin M → RealSpace ι, Covers A B centers

def coveringNumber {ι : Type u} (A B : Set (RealSpace ι)) : ℕ :=
  sInf {M : ℕ | ∃ centers : Fin M → RealSpace ι, Covers A B centers}

structure IsSymmetricConvexBody {ι : Type u} [Fintype ι]
    (K : Set (RealSpace ι)) : Prop where
  isCompact : IsCompact K
  convex : Convex ℝ K
  symmetric : ∀ x, x ∈ K ↔ -x ∈ K
  interior_nonempty : (interior K).Nonempty

theorem exists_entropy_duality_counterexample_with_covers
    (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ n : ℕ, 0 < n ∧ ∃ K : Set (RealSpace (Fin n)),
      IsSymmetricConvexBody K ∧
      Coverable K (cube (Fin n)) ∧
      Coverable (polar (cube (Fin n))) (a⁻¹ • polar K) ∧
      b * Real.log (coveringNumber (polar (cube (Fin n))) (a⁻¹ • polar K) : ℝ) <
        Real.log (coveringNumber K (cube (Fin n)) : ℝ) := by
  sorry

end MetricEntropyDuality

end

end OAI
