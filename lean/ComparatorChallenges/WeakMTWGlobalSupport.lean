import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

open scoped Manifold ContDiff Topology
open Set Filter Manifold Bundle

namespace WeakMTW

noncomputable section

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev model (n : ℕ) := 𝓘(ℝ, Model n)

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

def CompleteGeodesicWithInitialData (x : M) (v : TangentSpace (model n) x)
    (γ : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) (model n) ∞ γ ∧
  ∃ h : γ 0 = x,
    (h ▸ mfderiv 𝓘(ℝ, ℝ) (model n) γ 0 (1 : ℝ)) = v ∧
    ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
        dist (γ s) (γ r) = ‖v‖ * |s - r|

def ExpEndpoint (x : M) (v : TangentSpace (model n) x) (y : M) : Prop :=
  ∃ γ : ℝ → M, CompleteGeodesicWithInitialData x v γ ∧ γ 1 = y

noncomputable def exp (x : M) (v : TangentSpace (model n) x) : M :=
  by
    classical
    exact if h : ∃ y, ExpEndpoint x v y then Classical.choose h else x

def injectivityDomain (x : M) : Set (TangentSpace (model n) x) :=
  {v | ∃ a : ℝ, 1 < a ∧ dist x (exp x (a • v)) = a * ‖v‖}

def cost (x y : M) : ℝ := dist x y ^ 2 / 2

noncomputable def mtw (x : M) (v ξ η : TangentSpace (model n) x) : ℝ :=
  -(3 / 2 : ℝ) * deriv (fun s : ℝ =>
    deriv (fun s' : ℝ => deriv (fun t : ℝ =>
      deriv (fun t' : ℝ => cost (exp x (t' • ξ)) (exp x (v + s' • η))) t) 0) s) 0

def HasWeakMTW : Prop :=
  ∀ (x : M) (v : TangentSpace (model n) x), v ∈ injectivityDomain x →
    ∀ ξ η : TangentSpace (model n) x, inner ℝ ξ η = 0 → 0 ≤ mtw x v ξ η

def MainConvexity : Prop :=
  ∀ x : M, Convex ℝ (injectivityDomain (n := n) x)

end

end WeakMTW

/-- Weak MTW implies linear convexity of every open tangent injectivity domain. -/
theorem current_main_convexity
    {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M]
    [IsManifold (WeakMTW.model n) ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
      (fun x : M => TangentSpace (WeakMTW.model n) x)]
    [IsRiemannianManifold (WeakMTW.model n) M]
    (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M)) :
    WeakMTW.MainConvexity (n := n) (M := M) :=
  by
    sorry

end WeakMTWGlobalSupport

end OAI
