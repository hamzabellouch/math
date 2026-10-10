import OAI.Analysis.RCDHeat.Foundations
import OAI.Geometry.RCD.Metric.MetricLimit

namespace OAI

/-!
# Openness of the limiting coordinate chart

Euclidean invariance of domain is formulated as an open-image property,
following Hatcher, *Algebraic Topology* (2002), Theorem 2B.3, page 172.
The metric estimates use the ambient subtype distance.
-/

open Set Topology

namespace RegularPointCoordinates

/-- Precisely the Euclidean open-image assertion of Hatcher, Theorem 2B.3. -/
def EuclideanInvarianceOfDomain (n : ℕ) : Prop :=
  ∀ (O : Set (Euclidean n)), IsOpen O →
    ∀ f : O → Euclidean n, Continuous f → Function.Injective f → IsOpen (range f)

/-- Transfer invariance of domain through the original topological coordinates. -/
theorem isOpen_range_of_coordinates {X : Type*} [TopologicalSpace X] {n : ℕ}
    (hIOD : EuclideanInvarianceOfDomain n) {O : Set (Euclidean n)} (hO : IsOpen O)
    (u : X ≃ₜ O) {F : X → Euclidean n} (hF : Continuous F)
    (hinj : Function.Injective F) : IsOpen (range F) := by
  have hopen := hIOD O hO (F ∘ u.symm) (hF.comp u.symm.continuous)
    (hinj.comp u.symm.injective)
  have hrange : range (F ∘ u.symm) = range F := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨u.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨u x, by simp⟩
  rwa [hrange] at hopen

/-- Two-sided ambient-distance bounds and topological coordinates give an open
bi-Lipschitz chart. -/
theorem hasOpenBilipschitzChart_of_coordinates_and_bounds
    {X : Type*} [MetricSpace X] {n : ℕ} {p : X}
    (hIOD : EuclideanInvarianceOfDomain n)
    {U : Set X} (hU : IsOpen U) (hp : p ∈ U)
    {O : Set (Euclidean n)} (hO : IsOpen O) (u : U ≃ₜ O)
    {F : U → Euclidean n} {L : ℝ} (hL : 1 ≤ L)
    (hbound : ∀ x z : U,
      L⁻¹ * dist (x : X) (z : X) ≤ dist (F x) (F z) ∧
      dist (F x) (F z) ≤ L * dist (x : X) (z : X)) :
    HasOpenBilipschitzChart n p := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨hLip, hAnti⟩ := lipschitz_antilipschitz_of_dist_bounds
    (inv_pos.mpr hLpos) hLpos.le hbound
  have hEmb : IsEmbedding F := hAnti.isEmbedding hLip.continuous
  have hRange : IsOpen (range F) :=
    isOpen_range_of_coordinates hIOD hO u hLip.continuous hEmb.injective
  refine ⟨U, range F, hU, hp, hRange, hEmb.toHomeomorph, L, hL, ?_⟩
  intro x z
  simpa using hbound x z

end RegularPointCoordinates

end OAI
