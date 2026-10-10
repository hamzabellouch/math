import OAI.Analysis.BoundedHochschild.WeakCompactFragment
import OAI.Analysis.BoundedHochschild.CompactInvariantSets
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace OAI

/-! Minimal weakly compact isometric orbits are norm compact in a separable space. -/

noncomputable section

open Topology TopologicalSpace

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type v} [Group G]

/-- The weak action associated to a linear isometry. -/
def weakIsometry (T : E ≃ₗᵢ[ℂ] E) : WeakSpace ℂ E → WeakSpace ℂ E :=
  WeakSpace.map T.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma weakIsometry_apply (T : E ≃ₗᵢ[ℂ] E) (x : WeakSpace ℂ E) :
    (toWeakSpace ℂ E).symm (weakIsometry T x) = T ((toWeakSpace ℂ E).symm x) := rfl

/-- Minimality and the Baire small-piece lemma give a finite norm net. -/
theorem minimal_isometric_orbit_finite_net (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (K : Set (WeakSpace ℂ E)) (hK : IsCompact K) (hne : K.Nonempty)
    (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' K))
    (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) K K)
    (hmin : ∀ L : Set (WeakSpace ℂ E), L ⊆ K → L.Nonempty → IsClosed L →
      (∀ g, Set.MapsTo (weakIsometry (T g)) L L) → K ⊆ L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset E, (↑s : Set E) ⊆ (toWeakSpace ℂ E).symm '' K ∧
      ∀ x ∈ K, ∃ y ∈ s, ‖(toWeakSpace ℂ E).symm x - y‖ < ε := by
  classical
  obtain ⟨U, hU, hKU, hdiam⟩ := weakCompact_small_open_piece K hK hne hsep ε hε
  have hcov : K ⊆ ⋃ g, weakIsometry (T g) ⁻¹' U := by
    apply minimal_invariant_open_cover (fun g => weakIsometry (T g))
      (fun g => (WeakSpace.map (T g).toContinuousLinearEquiv.toContinuousLinearMap).continuous)
      _ _ K hK.isClosed hinv hmin U hU hKU
    · intro x
      apply (toWeakSpace ℂ E).symm.injective
      exact hone _
    · intro g h x
      apply (toWeakSpace ℂ E).symm.injective
      exact hmul g h _
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun g => weakIsometry (T g) ⁻¹' U)
    (fun g => hU.preimage (WeakSpace.map (T g).toContinuousLinearEquiv.toContinuousLinearMap).continuous) hcov
  obtain ⟨y, hyK, hyU⟩ := hKU
  let z (g : G) : E := T g⁻¹ ((toWeakSpace ℂ E).symm y)
  refine ⟨s.image z, ?_, ?_⟩
  · intro a ha
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨weakIsometry (T g⁻¹) y, hinv g⁻¹ hyK, rfl⟩
  · intro x hx
    obtain ⟨g, hgs, hxU⟩ := Set.mem_iUnion₂.mp (hs hx)
    refine ⟨z g, Finset.mem_image.mpr ⟨g, hgs, rfl⟩, ?_⟩
    have hgzy : T g (z g) = (toWeakSpace ℂ E).symm y := by
      dsimp [z]
      rw [← hmul, mul_inv_cancel, hone]
    have hd := hdiam (weakIsometry (T g) x) ⟨hinv g hx, hxU⟩ y ⟨hyK, hyU⟩
    change ‖T g ((toWeakSpace ℂ E).symm x) - (toWeakSpace ℂ E).symm y‖ < ε at hd
    rwa [← hgzy, ← map_sub, (T g).norm_map] at hd

/-- A minimal weakly compact orbit inside a norm-separable Banach space is
compact for the norm topology as well. -/
theorem minimal_isometric_orbit_normCompact [CompleteSpace E]
    (T : G → E ≃ₗᵢ[ℂ] E)
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (K : Set (WeakSpace ℂ E)) (hK : IsCompact K) (hne : K.Nonempty)
    (hsep : IsSeparable ((toWeakSpace ℂ E).symm '' K))
    (hinv : ∀ g, Set.MapsTo (weakIsometry (T g)) K K)
    (hmin : ∀ L : Set (WeakSpace ℂ E), L ⊆ K → L.Nonempty → IsClosed L →
      (∀ g, Set.MapsTo (weakIsometry (T g)) L L) → K ⊆ L) :
    IsCompact ((toWeakSpace ℂ E).symm '' K) := by
  have hc : IsClosed ((toWeakSpace ℂ E).symm '' K) := by
    have heq : (toWeakSpace ℂ E).symm '' K = (toWeakSpace ℂ E) ⁻¹' K := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      exact ⟨fun ⟨y, hy, he⟩ => he ▸ by simpa using hy,
        fun hx => ⟨toWeakSpace ℂ E x, hx, rfl⟩⟩
    rw [heq]
    exact hK.isClosed.preimage (toWeakSpaceCLM ℂ E).continuous
  apply TotallyBounded.isCompact_of_isComplete _ hc.isComplete
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨s, _, hs⟩ := minimal_isometric_orbit_finite_net T hone hmul K hK hne hsep hinv hmin ε hε
  refine ⟨s, s.finite_toSet, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hdist⟩ := hs y hy
  apply Set.mem_iUnion₂.mpr
  exact ⟨z, hz, by simpa only [Metric.mem_ball, dist_eq_norm] using hdist⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
