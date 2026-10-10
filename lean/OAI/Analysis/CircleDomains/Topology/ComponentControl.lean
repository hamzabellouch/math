import OAI.Analysis.CircleDomains.LengthArea
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Recognition of the limiting circle domain

Complementary-component coverage, collapse of unmarked components, and filling
of marked components together identify the limiting image as a circle domain.
-/

namespace CircleDomainRigidity

/-- An actual connected component of the closed complement. -/
def IsComplementaryComponent (G K : Set Sphere) : Prop :=
  ∃ p ∈ Gᶜ, K = connectedComponentIn Gᶜ p

/-- Complementary components are nonempty. -/
theorem IsComplementaryComponent.nonempty {G K : Set Sphere}
    (h : IsComplementaryComponent G K) : K.Nonempty := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p, mem_connectedComponentIn hp⟩

/-- The final component argument requires coverage, unmarked collapse, and
marked filling separately.  In particular, merely finding round disks
*inside* marked components is insufficient. -/
theorem isCircleDomain_of_component_control
    {G : Set Sphere} (hopen : IsOpen G) (hconn : IsConnected G)
    {B : Type*} (component : B → Set Sphere) (marked : Set B)
    (coverage : ∀ K, IsComplementaryComponent G K → ∃ b, K = component b)
    (collapse : ∀ b, b ∉ marked → ∃ p, component b = {p})
    (filling : ∀ b, b ∈ marked → IsRoundClosedDisk (component b)) :
    IsCircleDomain G := by
  refine ⟨hopen, hconn, ?_⟩
  intro p hp
  obtain ⟨b, hb⟩ := coverage _ ⟨p, hp, rfl⟩
  rw [hb]
  by_cases hb : b ∈ marked
  · exact Or.inr (filling b hb)
  · exact Or.inl (collapse b hb)

/-- Vanishing barrier estimates force every nonnegative projected length to vanish.
This is the real-number limit step of the unmarked-collapse argument (§6,
`thm:unmarked-collapse`). -/
theorem eq_zero_of_arbitrarily_small_bound {length C : ℝ}
    (hlength : 0 ≤ length) (hC : 0 ≤ C)
    (hbound : ∀ ε : ℝ, 0 < ε → length ≤ C * ε) : length = 0 := by
  by_contra hne
  have hpos : 0 < length := lt_of_le_of_ne hlength (Ne.symm hne)
  have hden : 0 < C + 1 := by linarith
  have heps : 0 < length / (2 * (C + 1)) :=
    div_pos hpos (mul_pos (by norm_num) hden)
  have hb := hbound _ heps
  have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hden)).mp
    (show length ≤ (C * length) / (2 * (C + 1)) by
      simpa only [mul_div_assoc] using hb)
  nlinarith

/-- A metric version of the collapse step: vanishing pairwise distances give a
singleton, provided the component is nonempty. -/
theorem singleton_of_arbitrarily_small_dist {X : Type*} [MetricSpace X]
    {K : Set X} (hne : K.Nonempty) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ K, ∀ y ∈ K, ∀ ε : ℝ, 0 < ε → dist x y ≤ C * ε) :
    ∃ x, K = {x} := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, Set.Subset.antisymm ?_ ?_⟩
  · intro y hy
    have hdist := eq_zero_of_arbitrarily_small_bound dist_nonneg hC
      (hbound y hy x hx)
    exact Set.mem_singleton_iff.mpr (dist_eq_zero.mp hdist)
  · exact Set.singleton_subset_iff.mpr hx

end CircleDomainRigidity

end OAI
