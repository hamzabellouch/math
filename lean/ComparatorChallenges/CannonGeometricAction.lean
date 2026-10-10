import Mathlib

namespace OAI

noncomputable section
namespace CannonRelease

universe u

structure CayleyData (G : Type u) [Group G] where
  generators : Finset G
  symmetric : ∀ x ∈ generators, x⁻¹ ∈ generators
  connected : (SimpleGraph.mulCayley (generators : Set G)).Connected

def CayleyData.graph {G : Type u} [Group G] (D : CayleyData G) : SimpleGraph G :=
  SimpleGraph.mulCayley (D.generators : Set G)

/-- A uniform thinness constant for geodesic triangles in the Cayley graph. -/
def CayleyData.ThinTriangles {G : Type u} [Group G] (D : CayleyData G) : Prop :=
  ∃ δ : ℕ, ∀ x y z : G,
    ∀ p : D.graph.Walk x y, ∀ q : D.graph.Walk y z, ∀ r : D.graph.Walk z x,
      p.length = D.graph.dist x y → q.length = D.graph.dist y z →
      r.length = D.graph.dist z x →
      ∀ a ∈ p.support, ∃ b ∈ q.support ++ r.support, D.graph.dist a b ≤ δ

/-- Based geodesic rays, parametrized at integer times. -/
def BasedRay {G : Type u} [Group G] (D : CayleyData G) :=
  {r : ℕ → G // r 0 = 1 ∧ ∀ i j, D.graph.dist (r i) (r j) = Nat.dist i j}

instance {G : Type u} [Group G] [TopologicalSpace G] (D : CayleyData G) :
    TopologicalSpace (BasedRay D) := inferInstanceAs (TopologicalSpace {r : ℕ → G //
      r 0 = 1 ∧ ∀ i j, D.graph.dist (r i) (r j) = Nat.dist i j})

/-- Finite synchronous distance, equivalent to asymptoticity for based rays. -/
def raySetoid {G : Type u} [Group G] (D : CayleyData G) : Setoid (BasedRay D) where
  r r s := ∃ C : ℕ, ∀ n, D.graph.dist (r.val n) (s.val n) ≤ C
  iseqv := by
    constructor
    · intro r
      exact ⟨0, fun n => by simp⟩
    · rintro r s ⟨C, hC⟩
      exact ⟨C, fun n => by rw [SimpleGraph.dist_comm]; exact hC n⟩
    · rintro r s t ⟨C, hC⟩ ⟨E, hE⟩
      refine ⟨C + E, fun n => ?_⟩
      exact le_trans ((D.connected (r.val n) (s.val n)).dist_triangle_left (t.val n))
        (Nat.add_le_add (hC n) (hE n))

def Boundary {G : Type u} [Group G] (D : CayleyData G) := Quotient (raySetoid D)

instance {G : Type u} [Group G] [TopologicalSpace G] (D : CayleyData G) :
    TopologicalSpace (Boundary D) :=
  inferInstanceAs (TopologicalSpace (Quotient (raySetoid D)))

abbrev SphereTwo := {x : EuclideanSpace ℝ (Fin 3) // x ∈ Metric.sphere 0 1}

/-- The upper-half-space model of hyperbolic three-space. -/
def HyperbolicThree := {x : Fin 3 → ℝ // 0 < x 2}

instance : TopologicalSpace HyperbolicThree :=
  inferInstanceAs (TopologicalSpace {x : Fin 3 → ℝ // 0 < x 2})

def hyperbolicDist (x y : HyperbolicThree) : ℝ :=
  Real.arcosh (1 + (∑ i : Fin 3, (x.val i - y.val i) ^ 2) / (2 * x.val 2 * y.val 2))

/-- The full isometry group, including orientation-reversing isometries. -/
def hyperbolicIsometries : Subgroup (HyperbolicThree ≃ₜ HyperbolicThree) where
  carrier := {f | ∀ x y, hyperbolicDist (f x) (f y) = hyperbolicDist x y}
  one_mem' := by
    change ∀ x y, hyperbolicDist x y = hyperbolicDist x y
    intros
    rfl
  mul_mem' := by
    intro f g hf hg x y
    exact (hf (g x) (g y)).trans (hg x y)
  inv_mem' := by
    intro f hf x y
    simpa using (hf (f.symm x) (f.symm y)).symm

abbrev H3Isom := ↥hyperbolicIsometries

def ProperAction {G : Type u} [Group G] (ρ : G →* H3Isom) : Prop :=
  ∀ K : Set HyperbolicThree, IsCompact K →
    {g : G | ∃ x ∈ K, (ρ g).val x ∈ K}.Finite

def CocompactAction {G : Type u} [Group G] (ρ : G →* H3Isom) : Prop :=
  ∃ K : Set HyperbolicThree, IsCompact K ∧
    ∀ x : HyperbolicThree, ∃ g : G, ∃ y ∈ K, (ρ g).val y = x

theorem cannon (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (D : CayleyData G) (hthin : D.ThinTriangles)
    (hsphere : Nonempty (Boundary D ≃ₜ SphereTwo)) :
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧
      (ρ.ker : Set G).Finite := by
  sorry

end CannonRelease
end

end OAI
