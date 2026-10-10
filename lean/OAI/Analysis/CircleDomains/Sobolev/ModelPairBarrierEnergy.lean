import OAI.Analysis.CircleDomains.Modulus.ModelPairBarrier
import OAI.Analysis.CircleDomains.Topology.ModelCompactTransport
import OAI.Analysis.CircleDomains.Sobolev.ConformalSobolevEnergyIdentity
import OAI.Analysis.CircleDomains.Sobolev.LocalWeakGradientEnergy

namespace OAI

/-! The actual compact target barrier has exactly the saved local source
energy. Its gradient on the model holes and on the exterior both vanish. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem pairBarrier_energy (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (i j : Fin m) {a : ℝ} (ha : 0 < a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    {Φ θ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hsΦ : HasCompactSupport Φ)
    (hΦunit : ∀ x, Φ x ∈ Icc (0 : ℝ) 1)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hsθ : HasCompactSupport θ)
    (hθone : ∀ x ∈ closedBall 0 (64*a), θ x = 1)
    (hθsupp : tsupport θ ⊆ ball 0 ((129/2:ℝ)*a))
    (H : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair (u i x) (u j x)))
      (physicalPlaneDomain G ∩ ball 0 (65*a)))
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
      Φ (planePair (u i (complexPlaneCoordinates.symm z)) (u j (complexPlaneCoordinates.symm z))) = 0) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (M.pairBarrier i j Φ θ) univ,
      (∀ k : Fin 2, ∀ᵐ x ∂volume,
        x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) → W.weakGrad x k = 0) ∧
      (∫ x, ‖W.weakGrad x‖^2) =
        ∫ x in physicalPlaneDomain G ∩ ball 0 (65*a), ‖H.weakGrad x‖^2 := by
  obtain ⟨W,hWzero⟩ := M.pairBarrier_witness harea hG hu hs i j ha hsource
    hΦ hsΦ hΦunit hθ hsθ hθone hθsupp
  have hB := M.pairBarrier_continuous hu hs i j hΦ.continuous hθ.continuous
  have hsB : HasCompactSupport (M.pairBarrier i j Φ θ) := hsθ.mul_right
  obtain ⟨hfc,hmap,fi,hfic,hfimap,hl,hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence fi (extendAtInfinity M.function)
      (extendAtInfinity M.function '' G) G :=
    ⟨fun p hp => hfic.isSmoothSphereAt M.image_open hp,hfimap,
      fun p hp => hfc.isSmoothSphereAt hG hp,hmap,hr,hl⟩
  have hfix : fi OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using hl _ hinf
  let v := planeInverseTransport (extendAtInfinity M.function) (M.pairBarrier i j Φ θ)
  obtain ⟨K,hK⟩ := sobolev_conformal_energy_identity heq M.image_open hG
    ⟨_,hinf,rfl⟩ hfix hfic hB hsB W (v := v) (fun _ _ => rfl)
    (M.compact_target_pullback_memLp hG hinf hB hsB)
  have hnormK : (∫ x in physicalPlaneDomain G, ‖K.weakGrad x‖^2) =
      ∫ x in physicalPlaneDomain (extendAtInfinity M.function '' G), ‖W.weakGrad x‖^2 := by
    simpa only [plane_norm_sq] using hK
  have hv := M.cutoff_preserves_inner_barrier harea hG ha hsource θ hθone hθsupp
    (fun z => Φ (planePair (u i (complexPlaneCoordinates.symm z)) (u j (complexPlaneCoordinates.symm z)))) hzero
  have hlocal : (∫ x in physicalPlaneDomain G, ‖K.weakGrad x‖^2) =
      ∫ x in physicalPlaneDomain G ∩ ball 0 (65*a), ‖H.weakGrad x‖^2 := by
    apply localized_weakGradient_energy (isOpen_physicalPlaneDomain hG) K H
    · intro x hx
      change planeInverseTransport _ _ x = _
      rw [M.pairBarrier_pullback i j Φ θ hx.1]
      have hh := hv.1 (complexPlaneCoordinates x) hx.1
        (by simpa only [mem_ball,dist_zero_right,complexPlaneCoordinates_norm] using hx.2)
      simpa only [complexPlaneCoordinates.symm_apply_apply] using hh
    · intro x hx hxn
      change planeInverseTransport _ _ x = 0
      rw [M.pairBarrier_pullback i j Φ θ hx]
      have hh := hv.2 (complexPlaneCoordinates x) hx
        (by simpa only [complexPlaneCoordinates_norm] using hxn.le)
      simpa only [complexPlaneCoordinates.symm_apply_apply] using hh
  have hzE : ∀ᵐ x ∂volume,
      x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) → ‖W.weakGrad x‖^2 = 0 := by
    filter_upwards [hWzero 0,hWzero 1] with x h₀ h₁ hx
    rw [plane_norm_sq,h₀ hx,h₁ hx]
    norm_num
  refine ⟨W,hWzero,?_⟩
  exact (setIntegral_eq_integral_of_ae_compl_eq_zero hzE).symm.trans (hnormK.symm.trans hlocal)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
