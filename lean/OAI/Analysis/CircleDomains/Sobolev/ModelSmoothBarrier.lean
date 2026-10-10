import OAI.Analysis.CircleDomains.Topology.ModelCompactTransport
import OAI.Analysis.CircleDomains.Sobolev.SmoothWeakGradient
import OAI.Analysis.CircleDomains.Sobolev.CutoffEnergyAlgebra

namespace OAI

/-! A smooth compact target barrier has its actual smooth source
Sobolev witness and no greater Dirichlet energy, by conformal transport. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem smooth_barrier_pullback (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ) :
    ∃ V : DeGiorgi.MemW1pWitness 2
        (planeInverseTransport (extendAtInfinity M.function) Φ) (physicalPlaneDomain G),
      (∀ x, V.weakGrad x = planeCovectorGradient
        (fderiv ℝ (planeInverseTransport (extendAtInfinity M.function) Φ) x)) ∧
      (∫ x in physicalPlaneDomain G, ‖V.weakGrad x‖^2) ≤
        ∫ x : EuclideanPlane, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2 := by
  obtain ⟨hfc,hmap,fi,hfic,hfimap,hl,hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence fi (extendAtInfinity M.function)
      (extendAtInfinity M.function '' G) G :=
    ⟨fun p hp => hfic.isSmoothSphereAt M.image_open hp, hfimap,
      fun p hp => hfc.isSmoothSphereAt hG hp, hmap, hr, hl⟩
  have hfi : fi OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using hl _ hinf
  have hparts (i : Fin 2) : MemLp (fun x => fderiv ℝ Φ x (EuclideanSpace.single i 1)) 2 volume :=
    ((hΦ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hs.fderiv_apply (𝕜 := ℝ) _)
  obtain ⟨hF,hD,hE⟩ := smooth_plane_energy_transport heq M.image_open hG
    ⟨_,hinf,rfl⟩ hfi hfic hΦ.contDiffOn (fun i => (hparts i).restrict _)
  let V := smoothPlaneSobolevWitness (isOpen_physicalPlaneDomain hG) hF
    (M.compact_target_pullback_memLp hG hinf hΦ.continuous hs) hD
  have hv (x : EuclideanPlane) : V.weakGrad x = planeCovectorGradient
      (fderiv ℝ (planeInverseTransport (extendAtInfinity M.function) Φ) x) := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    funext i
    fin_cases i <;> simp [V, smoothPlaneSobolevWitness, planeCovectorGradient]
  have hi : Integrable (fun x : EuclideanPlane => (fderiv ℝ Φ x (EuclideanSpace.single 0 1))^2+
      (fderiv ℝ Φ x (EuclideanSpace.single 1 1))^2) volume :=
    (hparts 0).integrable_sq.add (hparts 1).integrable_sq
  refine ⟨V,hv,?_⟩
  calc
    _ = ∫ x in physicalPlaneDomain G,
        (fderiv ℝ (planeInverseTransport (extendAtInfinity M.function) Φ) x (EuclideanSpace.single 0 1))^2+
        (fderiv ℝ (planeInverseTransport (extendAtInfinity M.function) Φ) x (EuclideanSpace.single 1 1))^2 := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by dsimp only; rw [hv x, plane_norm_sq]; simp only [planeCovectorGradient,planePair_zero,planePair_one])
    _ = _ := hE
    _ ≤ ∫ x : EuclideanPlane, (fderiv ℝ Φ x (EuclideanSpace.single 0 1))^2+
        (fderiv ℝ Φ x (EuclideanSpace.single 1 1))^2 :=
      setIntegral_le_integral hi (Eventually.of_forall (fun x => add_nonneg (sq_nonneg _) (sq_nonneg _)))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by dsimp only; rw [plane_norm_sq]; simp only [planeCovectorGradient,planePair_zero,planePair_one])

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
