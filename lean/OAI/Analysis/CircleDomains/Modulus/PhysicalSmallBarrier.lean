import OAI.Analysis.CircleDomains.Topology.CenteredSmallCutoffs
import OAI.Analysis.CircleDomains.Sobolev.ComplexWeakGradient

namespace OAI

/-! Actual smooth planar barriers with arbitrarily small energy and
uniform first/second differential bounds for all their translates. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_physical_small_barrier {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ (Φ : EuclideanPlane → ℝ) (r M₁ M₂ : ℝ),
      0 < r ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
      tsupport Φ ⊆ ball 0 R ∧ (∀ x, Φ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ball 0 r, Φ x = 1) ∧
      (∫ x, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2) < ε ∧
      (∀ x, ‖fderiv ℝ Φ x‖ ≤ M₁) ∧
      (∀ x y, ‖fderiv ℝ Φ x-fderiv ℝ Φ y‖ ≤ M₂*‖x-y‖) := by
  obtain ⟨f,hf,hs,hsR,hunit,hone,henergy⟩ := exists_small_energy_cutoff 0 hR hε
  let Φ := f ∘ complexPlaneCoordinates
  have hΦ : ContDiff ℝ ∞ Φ := hf.comp complexPlaneCoordinates.contDiff
  have hsΦ : HasCompactSupport Φ := hs.comp_homeomorph complexPlaneCoordinates.toHomeomorph
  have hsup : tsupport Φ ⊆ ball 0 R := by
    rw [show Φ = f ∘ complexPlaneCoordinates.toHomeomorph from rfl, tsupport_comp_eq_preimage]
    intro x hx
    have hh := hsR hx
    change complexPlaneCoordinates x ∈ ball (0 : ℂ) R at hh
    simpa only [mem_ball, dist_zero_right, complexPlaneCoordinates_norm] using hh
  have hΦone : ∀ᶠ x in 𝓝 (0 : EuclideanPlane), Φ x = 1 := by
    have ht : Tendsto complexPlaneCoordinates (𝓝 (0 : EuclideanPlane)) (𝓝 (0 : ℂ)) := by
      simpa only [map_zero] using complexPlaneCoordinates.continuous.tendsto (0 : EuclideanPlane)
    exact ht.eventually hone
  obtain ⟨r,hr,hrΦ⟩ := Metric.mem_nhds_iff.mp hΦone
  obtain ⟨C,hC⟩ := (hsΦ.fderiv ℝ).exists_bound_of_continuous (hΦ.continuous_fderiv (by simp))
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hsΦ.fderiv ℝ)
    (hΦ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)) (by simp)
  have he : (∫ x, ‖planeCovectorGradient (fderiv ℝ Φ x)‖^2) = ∫ z, ‖fderiv ℝ f z‖^2 := by
    calc
      _ = ∫ x, ‖fderiv ℝ f (complexPlaneCoordinates x)‖^2 := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          dsimp only [Φ]
          rw [fderiv_comp x (hf.differentiable (by simp) _) complexPlaneCoordinates.differentiableAt,
            complexPlaneCoordinates.fderiv, complex_plane_covector_norm])
      _ = _ := complexPlaneCoordinates_measurePreserving.integral_comp
        complexPlaneCoordinates.toHomeomorph.measurableEmbedding (fun z : ℂ => ‖fderiv ℝ f z‖^2)
  refine ⟨Φ,r,max C 0,K,hr,le_max_right _ _,K.coe_nonneg,hΦ,hsΦ,hsup,
    (fun x => hunit _),hrΦ,he.trans_lt henergy,?_,?_⟩
  · intro x
    exact (hC x).trans (le_max_left _ _)
  · intro x y
    simpa only [dist_eq_norm] using hK.dist_le_mul x y

end CircleDomainRigidity

end

end OAI
