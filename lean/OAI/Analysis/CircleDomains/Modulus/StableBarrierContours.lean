import OAI.Analysis.CircleDomains.Transfer.SmallImageDustContours
import OAI.Analysis.CircleDomains.Modulus.SavedBarrierMargins

namespace OAI

/-! Choose the actual inner Jordan contours together with open plateau
neighborhoods and a common strict stability margin for later tests. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem exists_stable_barrier_contours
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (p q : EuclideanPlane → ℝ) (hp : Continuous p) (hq : Continuous q)
    (hps : HasCompactSupport p) (hqs : HasCompactSupport q)
    (Φ : EuclideanPlane → ℝ) {r D : ℝ} (hr : 0 < r)
    (hplateau : ∀ y, ‖y‖ ≤ r → Φ y = 1)
    (hBD : ∀ z : ℂ, (z : Sphere) ∉ G → z ∈ ball 0 D) :
    ∃ (n : ℕ) (J : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ)
      (b : Fin n → Sphere) (V : Fin n → Set ℂ),
      ({z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (J i)) ∧
      (∀ i, b i ∈ Gᶜ) ∧
      (∀ i, closure (jordanInterior (J i)) ⊆ ball 0 D) ∧
      (∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (J i)) = range (γ i) ∧ ∀ z ∈ range (γ i), (z : Sphere) ∈ G) ∧
      (∀ i, IsOpen (V i) ∧ closure (jordanInterior (J i)) ⊆ V i ∧
        ∀ A' : ℂ → EuclideanPlane,
          (∀ z ∈ V i, ‖A' z-planePair (p (complexPlaneCoordinates.symm z))
            (q (complexPlaneCoordinates.symm z))‖ < r/4) →
          ∀ z ∈ V i, Φ (A' z-planePair (sphereFromPlaneFunction p (b i))
            (sphereFromPlaneFunction q (b i))) = 1) := by
  obtain ⟨n,J,γ,b,hcover,hb,hD,hγ,hclose⟩ := exists_small_image_dust_contours
    hsard hsch hG hinf hTD p q hp hq hps hqs hBD (half_pos hr)
  let A := fun z : ℂ => planePair (p (complexPlaneCoordinates.symm z)) (q (complexPlaneCoordinates.symm z))
  have hA : Continuous A := continuous_planePair
    (hp.comp complexPlaneCoordinates.symm.continuous) (hq.comp complexPlaneCoordinates.symm.continuous)
  have hv (i : Fin n) := saved_barrier_one_on_neighborhood A hA
    (planePair (sphereFromPlaneFunction p (b i)) (sphereFromPlaneFunction q (b i)))
    Φ (closure (jordanInterior (J i))) hr hplateau (fun z hz => (hclose i z hz).le)
  choose V hVo hJV hVs using hv
  exact ⟨n,J,γ,b,V,hcover,hb,hD,hγ,fun i => ⟨hVo i,hJV i,hVs i⟩⟩

end CircleDomainRigidity

end

end OAI
