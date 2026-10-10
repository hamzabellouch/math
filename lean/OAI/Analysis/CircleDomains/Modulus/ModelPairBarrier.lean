import OAI.Analysis.CircleDomains.Topology.CompactPairCutoff
import OAI.Analysis.CircleDomains.Topology.ModelOuterCutoff
import OAI.Analysis.CircleDomains.Transfer.ModelScalarPullback

namespace OAI

/-! The actual compact target barrier is built from two continued model
coordinates. Its gradient vanishes almost everywhere on every model hole. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 def pairBarrier (M : CompactScalarModel G u) (i j : Fin m)
    (Φ θ : EuclideanPlane → ℝ) (x : EuclideanPlane) : ℝ :=
  θ x*Φ (planePair (sphereFromPlaneFunction (u i) (M.projection (planeSphere x)))
    (sphereFromPlaneFunction (u j) (M.projection (planeSphere x))))

 theorem pairBarrier_continuous (M : CompactScalarModel G u)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (i j : Fin m) {Φ θ : EuclideanPlane → ℝ} (hΦ : Continuous Φ) (hθ : Continuous θ) :
    Continuous (M.pairBarrier i j Φ θ) :=
  hθ.mul (hΦ.comp (continuous_planePair (M.scalar_continuous hu hs i) (M.scalar_continuous hu hs j)))

 theorem pairBarrier_pullback (M : CompactScalarModel G u) (i j : Fin m)
    (Φ θ : EuclideanPlane → ℝ) {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain G) :
    planeInverseTransport (extendAtInfinity M.function) (M.pairBarrier i j Φ θ) x =
      θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x)))*
        Φ (planePair (u i x) (u j x)) := by
  rw [planeInverseTransport_extendAtInfinity]
  simp only [planeSphere,extendAtInfinity_coe,sphereFromPlaneFunction_coe]
  dsimp only [pairBarrier]
  have he : planeSphere (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) =
      extendAtInfinity M.function (planeSphere x) := by
    simp only [planeSphere,extendAtInfinity_coe,complexPlaneCoordinates.apply_symm_apply]
  rw [he,M.projection_inverse _ hx]
  simp only [planeSphere,sphereFromPlaneFunction_coe,complexPlaneCoordinates.symm_apply_apply]

 theorem pairBarrier_witness (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (i j : Fin m) {a : ℝ} (ha : 0 < a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    {Φ θ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hsΦ : HasCompactSupport Φ)
    (hΦunit : ∀ x, Φ x ∈ Icc (0 : ℝ) 1)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hsθ : HasCompactSupport θ)
    (hθone : ∀ x ∈ closedBall 0 (64*a), θ x = 1)
    (hθsupp : tsupport θ ⊆ ball 0 ((129/2:ℝ)*a)) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (M.pairBarrier i j Φ θ) univ,
      ∀ k : Fin 2, ∀ᵐ x ∂volume,
        x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) → W.weakGrad x k = 0 := by
  let U : Set EuclideanPlane := ball 0 (66*a)
  have hU : IsOpen U := isOpen_ball
  have hθU : tsupport θ ⊆ U := hθsupp.trans (ball_subset_ball (by linarith))
  obtain ⟨C,hC⟩ := (hsΦ.fderiv ℝ).exists_bound_of_continuous (hΦ.continuous_fderiv (by simp))
  obtain ⟨W,hW,hWzero⟩ := compact_pair_cutoff_witness hU measure_ball_lt_top.ne
    (M.scalar_continuous hu hs i) (M.scalar_continuous hu hs j) (M.witness i) (M.witness j)
    (hΦ.of_le (by simp)) (by norm_num : (0 : ℝ) ≤ 1) (le_max_right C 0)
    (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hΦunit x).1]; exact (hΦunit x).2)
    (fun x => (hC x).trans (le_max_left C 0)) hθ hsθ hθU
  have hθderiv (x : EuclideanPlane)
      (hx : x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G)) : fderiv ℝ θ x = 0 := by
    have hb := (M.uniform_omitted_and_image_bound harea hG ha hsource).1 (complexPlaneCoordinates x) hx
    have hxb : x ∈ ball 0 (64*a) := by
      rw [mem_ball_zero_iff]
      rw [complexPlaneCoordinates_norm] at hb
      linarith
    have heq : θ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
      exact hθone y (ball_subset_closedBall hy)
    rw [heq.fderiv_eq]
    simp
  refine ⟨W,?_⟩
  intro k
  have hWk := (ae_restrict_iff' hU.measurableSet).mp (hW k)
  filter_upwards [hWk,hWzero k,M.gradient_zero i k,M.gradient_zero j k] with x hx hz hpi hqi hxc
  by_cases hxU : x ∈ U
  · rw [hx hxU,hpi hxc,hqi hxc,hθderiv x hxc]
    simp
  · exact hz hxU

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
