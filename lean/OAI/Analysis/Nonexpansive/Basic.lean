import OAI.Analysis.Nonexpansive.Model

namespace OAI

/-!
# Actual norm and weak carriers for the fixed point argument

The public reflexivity predicate uses the continuous bidual.  All maps on
convex sets use their norm subtypes.  Weak convergence takes place on a
separate subtype of `WeakSpace`, so it cannot alter the given norm.
The data structures record conclusions of the reduction from actual
fixed-point-free counterexamples.
-/

noncomputable section

open Set TopologicalSpace
open scoped Pointwise

namespace ReflexiveFixedPoints

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {X}

/-- The weak carrier is distinct from the norm subtype `K`. -/
abbrev WeakCarrier (K : Set X) :=
  {x : WeakSpace ℝ X // (toWeakSpace ℝ X).symm x ∈ K}

/-- Change only the carrier; both representatives denote the same point. -/
def normToWeak (K : Set X) : K ≃ WeakCarrier K where
  toFun x := ⟨toWeakSpace ℝ X x, by simp⟩
  invFun x := ⟨(toWeakSpace ℝ X).symm x, x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

@[simp] theorem normToWeak_val (K : Set X) (x : K) :
    ((normToWeak K x : WeakCarrier K) : WeakSpace ℝ X) = toWeakSpace ℝ X x := rfl

@[simp] theorem normToWeak_symm_val (K : Set X) (x : WeakCarrier K) :
    ((normToWeak K).symm x : X) = (toWeakSpace ℝ X).symm x := rfl

/-- Actual weak compactness in the ambient weak topology. -/
def WeaklyCompact (K : Set X) : Prop :=
  IsCompact ((toWeakSpace ℝ X) '' K)

/-- Actual weak closedness in the ambient weak topology. -/
def WeaklyClosed (K : Set X) : Prop :=
  IsClosed ((toWeakSpace ℝ X) '' K)

/-- The norm-closed linear span of the actual differences. -/
def differenceSpan (K : Set X) : Submodule ℝ X :=
  (Submodule.span ℝ (K - K)).topologicalClosure

/-- The entire closed unit ball of the difference span, viewed in `X`. -/
def differenceBall (K : Set X) : Set X :=
  {x | x ∈ differenceSpan K ∧ ‖x‖ ≤ 1}

/-- Invariance for an ambient subset under a map of the norm subtype. -/
def InvariantSubset (K : Set X) (T : K → K) (s : Set X) : Prop :=
  ∀ x : K, (x : X) ∈ s → (T x : X) ∈ s

/-- Minimality concerns genuine norm-closed convex invariant subsets. -/
def MinimalInvariant (K : Set X) (T : K → K) : Prop :=
  ∀ s : Set X, s ⊆ K → s.Nonempty → IsClosed s → Convex ℝ s →
    InvariantSubset K T s → s = K

/-- Structural conclusions obtained from a genuine fixed-point-free map. -/
structure MinimalInvariantData where
  K : Set X
  nonempty : K.Nonempty
  closed : IsClosed K
  bounded : Bornology.IsBounded K
  convex : Convex ℝ K
  separable : IsSeparable K
  weak_compact : WeaklyCompact K
  T : K → K
  nonexpansive : LipschitzWith 1 T
  no_fixed : ∀ x : K, T x ≠ x
  minimal : MinimalInvariant K T

/-- The normalized reduction data, still in the original ambient norm.
The normalization producer uses an actual scalar homothety of the set. -/
structure NormalizedMinimalData extends MinimalInvariantData (X := X) where
  diam_one : Metric.diam K = 1
  z : ℕ → K
  dense_z : DenseRange z
  weak_metrizable : MetrizableSpace (WeakCarrier K)
  weak_ball_compact : WeaklyCompact (differenceBall K)

namespace MinimalInvariantData

instance (D : MinimalInvariantData (X := X)) : Nonempty D.K := D.nonempty.to_subtype

instance (D : MinimalInvariantData (X := X)) [CompleteSpace X] : CompleteSpace D.K :=
  D.closed.completeSpace_coe

end MinimalInvariantData

namespace NormalizedMinimalData

instance (D : NormalizedMinimalData (X := X)) : Nonempty D.K := D.nonempty.to_subtype

instance (D : NormalizedMinimalData (X := X)) [CompleteSpace X] : CompleteSpace D.K :=
  D.closed.completeSpace_coe

/-- Every pair of points is at distance at most the normalized diameter. -/
theorem norm_sub_le_one (D : NormalizedMinimalData (X := X)) (x y : D.K) :
    ‖(x : X) - (y : X)‖ ≤ 1 := by
  rw [← dist_eq_norm, ← D.diam_one]
  exact Metric.dist_le_diam_of_mem D.bounded x.property y.property

end NormalizedMinimalData

end ReflexiveFixedPoints

end

end OAI
