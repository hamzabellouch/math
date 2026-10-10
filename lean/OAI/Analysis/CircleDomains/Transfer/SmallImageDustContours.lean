import OAI.Analysis.CircleDomains.Selection.PointDustContourSelection
import OAI.Analysis.CircleDomains.Topology.PlanarPairCalculus

namespace OAI

/-! Smooth inner contours can be selected where the two actual compact
source coordinates remain uniformly close to a single dust trace. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem exists_small_image_dust_contours
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) {G : Set Sphere} (hG : IsOpen G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (p q : EuclideanPlane → ℝ) (hp : Continuous p) (hq : Continuous q)
    (hps : HasCompactSupport p) (hqs : HasCompactSupport q)
    {D r : ℝ} (hBD : ∀ z : ℂ, (z : Sphere) ∉ G → z ∈ ball 0 D) (hr : 0 < r) :
    ∃ (n : ℕ) (J : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ) (b : Fin n → Sphere),
      ({z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (J i)) ∧
      (∀ i, b i ∈ Gᶜ) ∧
      (∀ i, closure (jordanInterior (J i)) ⊆ ball 0 D) ∧
      (∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (J i)) = range (γ i) ∧ ∀ z ∈ range (γ i), (z : Sphere) ∈ G) ∧
      ∀ i z, z ∈ closure (jordanInterior (J i)) →
        ‖planePair (p (complexPlaneCoordinates.symm z)) (q (complexPlaneCoordinates.symm z))-
          planePair (sphereFromPlaneFunction p (b i)) (sphereFromPlaneFunction q (b i))‖ < r := by
  have hpc := continuous_sphereFromPlaneFunction hp hps
  have hqc := continuous_sphereFromPlaneFunction hq hqs
  let P := fun z => planePair (sphereFromPlaneFunction p z) (sphereFromPlaneFunction q z)
  have hP : Continuous P := continuous_planePair hpc hqc
  let W : Set Sphere := ((↑) : ℂ → Sphere) '' ball 0 D
  have hBW : Gᶜ ⊆ W := by
    intro z hz
    cases z using OnePoint.rec with
    | infty => exact (hz hinf).elim
    | coe z => exact ⟨z,hBD z hz,rfl⟩
  have hW : IsOpen W := OnePoint.isOpen_image_coe.mpr isOpen_ball
  let Q : {z : Sphere // z ∈ Gᶜ} → Set Sphere :=
    fun a => P ⁻¹' ball (P a.val) r
  have hQ (a : {z : Sphere // z ∈ Gᶜ}) : IsOpen (Q a) :=
    isOpen_ball.preimage hP
  have haQ (a : {z : Sphere // z ∈ Gᶜ}) : a.val ∈ Q a := by
    change dist (P a.val) (P a.val) < r
    simpa only [dist_self] using hr
  obtain ⟨n,J,γ,hcover,hdata⟩ := exists_point_dust_subordinate_contours
    (G := G) (W := W) hsard hsch hG hinf hTD hW hBW Q hQ haQ
  have hcover' : {z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (J i) :=
    fun _ hz => hcover hz
  have hcenter (i : Fin n) : ∃ b : Sphere, b ∈ Gᶜ ∧ ∀ z ∈ closure (jordanInterior (J i)),
      ‖P (z : Sphere)-P b‖ < r := by
    obtain ⟨b,hb⟩ := (hdata i).2.2.2.2.2
    refine ⟨b,b.property,?_⟩
    intro z hz
    have hh := hb hz
    change dist (P (z : Sphere)) (P b) < r at hh
    simpa only [dist_eq_norm] using hh
  choose b hb hclose using hcenter
  refine ⟨n,J,γ,b,hcover',hb,?_,?_,?_⟩
  · intro i z hz
    obtain ⟨w,hw,he⟩ := (hdata i).1 hz
    exact OnePoint.coe_injective he ▸ hw
  · intro i
    refine ⟨(hdata i).2.1,(hdata i).2.2.1,(hdata i).2.2.2.1,?_⟩
    intro z hz
    exact (hdata i).2.2.2.2.1 z ((hdata i).2.2.2.1 ▸ hz)
  · intro i z hz
    simpa only [P, sphereFromPlaneFunction_coe] using hclose i z hz

end CircleDomainRigidity

end

end OAI
