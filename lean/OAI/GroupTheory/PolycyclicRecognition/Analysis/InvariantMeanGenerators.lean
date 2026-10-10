import OAI.GroupTheory.PolycyclicRecognition.Analysis.ApproximateInvariantMean
import Mathlib.Algebra.Group.Subgroup.Lattice

namespace OAI

/-! # It suffices to make a mean invariant under a generating set -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Set
open scoped Topology

variable {G : Type*} [Group G]

/-- The left translations preserving a linear averaging functional form a subgroup. -/
def meanStabilizer (M : BoundedReal G →ₗ[ℝ] ℝ) : Subgroup G where
  carrier := {g | ∀ f, M (leftPull g f) = M f}
  one_mem' := by intro f; rw [leftPull_one]
  mul_mem' := by
    intro g h hg hh f
    rw [leftPull_mul, hh, hg]
  inv_mem' := by
    intro g hg f
    have h := hg (leftPull g⁻¹ f)
    simpa only [← leftPull_mul, inv_mul_cancel, leftPull_one] using h.symm

/-- Approximate invariance need only be checked on generators; the limiting
functional is invariant under their whole algebraic closure. -/
theorem exists_invariantMean_of_approximate_generators
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (L : ι → BoundedReal G →ₗ[ℝ] ℝ)
    (hpos : ∀ i f, (∀ g, 0 ≤ f g) → 0 ≤ L i f)
    (hone : ∀ i, L i 1 = 1) (S : Set G) (hS : Subgroup.closure S = ⊤)
    (hdefect : ∀ g ∈ S, ∀ f, Tendsto (fun i => L i (leftPull g f) - L i f) l (𝓝 0)) :
    Nonempty (InvariantMean G) := by
  obtain ⟨M, hM, hMone, hMinv⟩ := exists_partially_invariantMean_of_approximate
    (l := l) L hpos hone S hdefect
  have hc : Subgroup.closure S ≤ meanStabilizer M := by
    rw [Subgroup.closure_le]
    exact hMinv
  rw [hS] at hc
  exact ⟨⟨M, hM, hMone, fun g f => hc (Subgroup.mem_top g) f⟩⟩

end PolycyclicRecognition

end

end OAI
