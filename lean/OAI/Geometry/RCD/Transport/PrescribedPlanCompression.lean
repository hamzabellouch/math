import OAI.Geometry.RCD.Transport.CompressedFiniteUnique

namespace OAI

/-! # Sharpening compression on a prescribed optimal plan

Uniqueness transfers the short-distance compression estimate from the
constructed entropy plan to the same plan used by the energy argument.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem prescribed_plan_compression {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C B : ℝ≥0∞} (hC : C≠⊤) (hB : B≠⊤)
    (h0 : ν₀≤C • hausdorff n X) (h1 : ν₁≤C • hausdorff n X)
    (p : X) {R D : ℝ} (hR : 0≤R) (hD : 0≤D)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p≤R) (hs1 : ∀ᵐ x ∂ν₁, dist x p≤R)
    (hd : OptimalPlanDistanceBound ν₀ ν₁ D)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hc : ∀ t : Time, π.map (fun γ => γ t)≤B • hausdorff n X) :
    ∀ t : Time, π.map (fun γ => γ t)≤compressionBudget K n D C • hausdorff n X := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨ρ,hρ,hgρ,hpρ,hcρ⟩ :=
    hX.exists_compressed_entropy_plan K n hn ν₀ ν₁ hC h0 h1 p hR hs0 hs1 D hD hd
  let : IsProbabilityMeasure ρ := hρ
  have he := hX.compressed_plan_unique_finite hn p hR π ρ hg hgρ hp hpρ hB
    (compressionBudget_ne_top K n D hC) hc (fun t => (hcρ t).1) hs0 hs1
  rw [he]
  exact fun t => (hcρ t).1

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
