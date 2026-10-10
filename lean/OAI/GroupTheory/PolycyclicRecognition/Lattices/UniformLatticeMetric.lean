import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricCoarseBridge
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

/-!
# Uniform lattice metric comparison

A discrete subgroup with a compact set of right-coset representatives is a
uniform lattice. Its inclusion has a uniformly close section. This gives
the discrete-group coarse comparison required in the duality endgame from
a metric quasi-isometry to the ambient Lie group. Neither finite generation
nor a recognition conclusion is built into the lattice definition.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric

variable {G : Type*} [Group G]

/-- A uniform lattice, expressed by discreteness and a compact fundamental
cover. Over a locally compact group this is equivalent to compactness of
the coset quotient. -/
def IsUniformLattice [TopologicalSpace G] (Λ : Subgroup G) : Prop :=
  DiscreteTopology Λ ∧ ∃ K : Set G, IsCompact K ∧
    ∀ g : G, ∃ (γ : Λ) (k : G), k ∈ K ∧ (γ : G) * k = g

variable [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]

omit [IsTopologicalGroup G] in
/-- Compactness of a fundamental cover gives a uniform distance to the
lattice. -/
theorem IsUniformLattice.exists_covering_radius {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ g : G, ∃ γ : Λ, dist g (γ : G) ≤ R := by
  obtain ⟨K, hK, hcover⟩ := hΛ.2
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (1 : G)
  refine ⟨max R 0, le_max_right _ _, fun g => ?_⟩
  obtain ⟨γ, k, hk, rfl⟩ := hcover g
  refine ⟨γ, ?_⟩
  have hkR : dist k 1 ≤ R := hR hk
  calc
    dist ((γ : G) * k) (γ : G) = dist k 1 := by
      simpa only [mul_one] using dist_mul_left (γ : G) k 1
    _ ≤ max R 0 := hkR.trans (le_max_left _ _)

omit [IsIsometricSMul G G] in
/-- A discrete subgroup has finite metric balls in a proper ambient group. -/
theorem IsUniformLattice.finite_closedBall [ProperSpace G] {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) (R : ℝ) :
    (closedBall (1 : Λ) R).Finite := by
  let := hΛ.1
  have hclosed : IsClosed (Λ : Set G) := Subgroup.isClosed_of_discreteTopology
  have hcompact := hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_closedBall (1 : G) R)
  exact hcompact.finite_of_discrete

omit [IsTopologicalGroup G] in
/-- A uniformly close lattice section has explicit coarse Lipschitz bounds. -/
theorem IsUniformLattice.exists_metric_section {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) :
    ∃ (r : G → Λ) (R : ℝ), 0 ≤ R ∧
      (∀ g, dist g (r g : G) ≤ R) ∧
      (∀ x y, dist (r x) (r y) ≤ dist x y + (R + R)) := by
  obtain ⟨R, hR, hcover⟩ := hΛ.exists_covering_radius
  choose r hr using hcover
  refine ⟨r, R, hR, hr, fun x y => ?_⟩
  change dist (r x : G) (r y : G) ≤ _
  calc
    dist (r x : G) (r y : G) ≤
        dist (r x : G) x + dist x y + dist y (r y : G) := dist_triangle4 _ _ _ _
    _ ≤ R + dist x y + R := by
      gcongr
      exact (dist_comm (r x : G) x).trans_le (hr x)
      exact hr y
    _ = dist x y + (R + R) := by ring

variable {H : Type*} [Group H] [MetricSpace H] [IsIsometricSMul H H]

/-- A metric quasi-isometry to a group containing a uniform lattice gives
the actual coarse equivalence with that lattice used by the algebraic
duality comparison. All inverse and finite-difference estimates are proved. -/
theorem IsUniformLattice.nonempty_coarseEquivalence [ProperSpace G]
    {Λ : Subgroup G} (hΛ : IsUniformLattice Λ) (f : H → G)
    (hfinite : ∀ R : ℝ, (closedBall (1 : H) R).Finite)
    {K C K' C' E : ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hsurj : ∀ g, ∃ x, dist g (f x) ≤ E) :
    Nonempty (GroupCoarseEquivalence H Λ) := by
  let : IsIsometricSMul Λ Λ := ⟨fun γ => Isometry.of_dist_eq (fun x y => by
    change dist ((γ : G) * (x : G)) ((γ : G) * (y : G)) = dist (x : G) (y : G)
    exact dist_mul_left (γ : G) (x : G) (y : G))⟩
  obtain ⟨r, R, _, hr, hrlip⟩ := hΛ.exists_metric_section
  have hgupper (x y : H) : dist (r (f x)) (r (f y)) ≤ K * dist x y + (C + (R + R)) := by
    exact (hrlip _ _).trans (by linarith [hupper x y])
  have hglower (x y : H) : dist x y ≤
      K' * dist (r (f x)) (r (f y)) + (K' * (R + R) + C') := by
    have hd : dist (f x) (f y) ≤ dist (r (f x)) (r (f y)) + (R + R) := by
      change dist (f x) (f y) ≤ dist (r (f x) : G) (r (f y) : G) + (R + R)
      calc
        dist (f x) (f y) ≤ dist (f x) (r (f x) : G) +
            dist (r (f x) : G) (r (f y) : G) + dist (r (f y) : G) (f y) :=
          dist_triangle4 _ _ _ _
        _ ≤ R + dist (r (f x) : G) (r (f y) : G) + R := by
          gcongr
          exact hr (f x)
          exact (dist_comm (r (f y) : G) (f y)).trans_le (hr (f y))
        _ = dist (r (f x) : G) (r (f y) : G) + (R + R) := by ring
    calc
      dist x y ≤ K' * dist (f x) (f y) + C' := hlower x y
      _ ≤ K' * (dist (r (f x)) (r (f y)) + (R + R)) + C' := by gcongr
      _ = K' * dist (r (f x)) (r (f y)) + (K' * (R + R) + C') := by ring
  have hgsurj (γ : Λ) : ∃ x : H, dist γ (r (f x)) ≤ E + R := by
    obtain ⟨x, hx⟩ := hsurj (γ : G)
    refine ⟨x, (dist_triangle (γ : G) (f x) (r (f x))).trans ?_⟩
    exact add_le_add hx (hr (f x))
  exact ⟨groupCoarseEquivalenceOfQuasiIsometry (r ∘ f) hfinite hΛ.finite_closedBall
    hK hK' hgupper hglower hgsurj⟩

end PolycyclicRecognition

end

end OAI
