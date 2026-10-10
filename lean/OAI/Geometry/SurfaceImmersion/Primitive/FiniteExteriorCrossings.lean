import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceCrossingExterior

namespace OAI

/-! One tolerance preserves all exterior crossing invariants in a finite
family, for the actual normal supplied by the primitive gluing theorem. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [Fintype ι]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem finite_exterior_crossing_preservation
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (curves : ι → PhaseBoundaryCurve B)
    {D : Set M} (hDr : interior (closure D) = D)
    {E : Set M} (hE : E.Finite)
    (hold : ∀ j k, j ≠ k → ∀ p ∈ E, p ∈ (curves j).carrier → p ∈ (curves k).carrier →
      (0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
       0 < (curves k).second F p ⬝ᵥ spaceCoordinates (n.vector p)) ∧
      0 < (curves j).crossing (curves k) F p ∧ 0 < (curves k).crossing (curves j) F p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ∀ h : SmoothMetric M, IsSmoothIsometricImmersion M h W →
      ∀ b a : ℝ, 0 ≤ b → 0 ≤ a → b+a < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 a (W-V) →
      (∀ p ∉ closure D, V =ᶠ[𝓝 p] G) → ∀ N : PreferredNormal W,
      (∀ p ∈ E, p ∉ D → N.vector p = A.unitProjectedNormalField W n.vector p) →
      ∀ j k, j ≠ k → ∀ p ∈ E, p ∉ D → p ∈ (curves j).carrier → p ∈ (curves k).carrier →
      (0 < (curves j).second W p ⬝ᵥ spaceCoordinates (N.vector p) ∧
       0 < (curves k).second W p ⬝ᵥ spaceCoordinates (N.vector p)) ∧
      0 < (curves j).crossing (curves k) W p ∧ 0 < (curves k).crossing (curves j) W p := by
  classical
  let P := {q : ι × ι // q.1 ≠ q.2}
  let K : P → Set M := fun q => {p | p ∈ E ∧ p ∉ D ∧
    p ∈ (curves q.val.1).carrier ∧ p ∈ (curves q.val.2).carrier}
  have hp (q : P) := (curves q.val.1).exterior_crossing_preservation (curves q.val.2) A
    hF n houter (hE.subset (fun _ h => h.1)).isCompact
    (show K q ⊆ (curves q.val.1).carrier from fun _ h => h.2.2.1)
    (show K q ⊆ (curves q.val.2).carrier from fun _ h => h.2.2.2)
    (closure D)ᶜ (by
      intro p hp
      rw [closure_compl,hDr]
      exact hp.2.1)
    (fun p hp => (hold q.val.1 q.val.2 q.property p hp.1 hp.2.2.1 hp.2.2.2).1)
    (fun p hp => (hold q.val.1 q.val.2 q.property p hp.1 hp.2.2.1 hp.2.2.2).2)
  choose r hr hpres using hp
  obtain ⟨ρ,hρ,_,hle⟩ := finite_positive_threshold r hr
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV h hW b a hb ha hba hGF hWV hext N hN j k hjk p hp hpD hpj hpk
  have hh := hpres ⟨(j,k),hjk⟩ G V W hG hV h hW b a hb ha
    (hba.trans_le (hle ⟨(j,k),hjk⟩)) hGF hWV hext p ⟨hp,hpD,hpj,hpk⟩
  rw [hN p hp hpD]
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
