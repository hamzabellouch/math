import OAI.Analysis.CircleDomains.Sobolev.ModelPairBarrierEnergy

namespace OAI

/-! A saved source barrier produces an actual compact global target
barrier, with the same small energy and value one on its image contour. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_small_pair_barrier (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (i j : Fin m) {a η : ℝ} (ha : 0 < a) (hη : 0 < η)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hsΦ : HasCompactSupport Φ)
    (hΦunit : ∀ x, Φ x ∈ Icc (0 : ℝ) 1)
    (H : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair (u i x) (u j x)))
      (physicalPlaneDomain G ∩ ball 0 (65*a)))
    (hH : (eLpNorm H.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η)
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
      Φ (planePair (u i (complexPlaneCoordinates.symm z)) (u j (complexPlaneCoordinates.symm z))) = 0)
    {C : Set ℂ} (hCG : ∀ z ∈ C, (z : Sphere) ∈ G) (hCr : C ⊆ ball 0 (65*a))
    (hCone : ∀ z ∈ C,
      Φ (planePair (u i (complexPlaneCoordinates.symm z)) (u j (complexPlaneCoordinates.symm z))) = 1) :
    ∃ (v : EuclideanPlane → ℝ) (W : DeGiorgi.MemW1pWitness 2 v univ),
      Continuous v ∧ tsupport v ⊆ ball 0 (65*a) ∧
      (∀ x, v x ∈ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ C, v (complexPlaneCoordinates.symm (M.function z)) = 1) ∧
      (∫ x, ‖W.weakGrad x‖^2) < η^2 := by
  obtain ⟨θ,D,_hD,hθ,hsθ,hθsupp,hθunit,hθone,_hθD⟩ := exists_physical_disk_cutoff
    (show 64*a < (129/2:ℝ)*a by linarith)
  obtain ⟨W,_hWzero,hWE⟩ := M.pairBarrier_energy harea hG hinf hu hs i j ha hsource
    hΦ hsΦ hΦunit hθ hsθ hθone hθsupp H hzero
  refine ⟨M.pairBarrier i j Φ θ,W,M.pairBarrier_continuous hu hs i j hΦ.continuous hθ.continuous,
    ?_,?_,?_,?_⟩
  · exact tsupport_mul_subset_left.trans (hθsupp.trans (ball_subset_ball (by linarith)))
  · intro x
    exact ⟨mul_nonneg (hθunit x).1 (hΦunit _).1,
      (mul_le_mul (hθunit x).2 (hΦunit _).2 (hΦunit _).1 zero_le_one).trans_eq (one_mul 1)⟩
  · intro z hz
    have hv := (M.cutoff_preserves_inner_barrier harea hG ha hsource θ hθone hθsupp
      (fun z => Φ (planePair (u i (complexPlaneCoordinates.symm z)) (u j (complexPlaneCoordinates.symm z)))) hzero).1
      z (hCG z hz) (mem_ball_zero_iff.mp (hCr hz))
    rw [hCone z hz] at hv
    change θ (complexPlaneCoordinates.symm (M.function z))*Φ
      (planePair (sphereFromPlaneFunction (u i) (M.projection
        (planeSphere (complexPlaneCoordinates.symm (M.function z)))))
        (sphereFromPlaneFunction (u j) (M.projection
        (planeSphere (complexPlaneCoordinates.symm (M.function z)))))) = 1
    have hproj : M.projection (M.function z : Sphere) = (z : Sphere) := by
      simpa only [extendAtInfinity_coe] using M.projection_inverse (z : Sphere) (hCG z hz)
    simpa only [planeSphere,complexPlaneCoordinates.apply_symm_apply,hproj,
      sphereFromPlaneFunction_coe,hCone z hz] using hv
  · rw [hWE]
    have he : (∫ x in physicalPlaneDomain G ∩ ball 0 (65*a), ‖H.weakGrad x‖^2) =
        (eLpNorm H.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal^2 := by
      rw [integral_sq_eq_eLpNorm_toReal_sq H.weakGrad_norm_memLp,
        eLpNorm_norm _ H.weakGrad_memLp.aestronglyMeasurable]
    rw [he]
    exact (sq_lt_sq₀ ENNReal.toReal_nonneg hη.le).mpr hH

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
