import OAI.Analysis.CircleDomains.Sobolev.CompactSobolevHeightModulus
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing
import OAI.Analysis.CircleDomains.Sobolev.LocalComplexWitness

namespace OAI

/-! Compact cutoffs remove the global L2 hypothesis from the height
estimate while preserving the actual local weak gradient on the annulus. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem local_sobolev_height_log_bound (φ : ℂ ≃ₜ ℂ) (c : ℂ)
    (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im|^2 * Real.log (R/r) ≤
      16*Real.pi*(∫ p in complexPlaneCoordinates ⁻¹'
        {z : ℂ | r < dist z c ∧ dist z c < R}, D.imagGradient p 0^2+D.imagGradient p 1^2) := by
  let v : EuclideanPlane → ℝ := fun p => (φ (complexPlaneCoordinates p)).im
  let Ω : Set EuclideanPlane := ball 0 (‖c‖+R+1)
  let K : Set EuclideanPlane := complexPlaneCoordinates.symm '' closedBall c R
  have hΩ : IsOpen Ω := isOpen_ball
  have hK : IsCompact K := (isCompact_closedBall c R).image complexPlaneCoordinates.symm.continuous
  have hKΩ : K ⊆ Ω := by
    rintro p ⟨z, hz, rfl⟩
    have htri : ‖z‖ ≤ dist z c + ‖c‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z-c) c
    have he := complexPlaneCoordinates_norm (complexPlaneCoordinates.symm z)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at he
    change ‖complexPlaneCoordinates.symm z-0‖ < ‖c‖+R+1
    rw [sub_zero, ← he]
    exact lt_of_le_of_lt htri (by linarith [mem_closedBall.mp hz])
  obtain ⟨η, V, hη, hsη, _, hsΩ, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro p hp
    apply hsΩ
    apply subset_tsupport η
    rw [Function.mem_support, hone p hp]
    exact one_ne_zero
  have hv : Continuous v := Complex.continuous_im.comp
    (φ.continuous.comp complexPlaneCoordinates.continuous)
  let H := D.imagWitness (φ.continuous.comp complexPlaneCoordinates.continuous) (‖c‖+R+1)
  obtain ⟨W⟩ := exists_global_compact_cutoff_witness hΩ H.memW1p hη hsη hsΩ
  let A := complexPlaneCoordinates ⁻¹' {z : ℂ | r < dist z c ∧ dist z c < R}
  have hAK : A ⊆ K := by
    intro p hp
    exact ⟨complexPlaneCoordinates p, hp.2.le, complexPlaneCoordinates.symm_apply_apply p⟩
  have hAV : A ⊆ V := hAK.trans hKV
  have hgrad (i : Fin 2) :
      (fun p => W.weakGrad p i) =ᵐ[volume.restrict A] fun p => D.imagGradient p i := by
    have h := weakGrad_eq_on_cutoff_plateau hV hVΩ H W hone i
    exact h.filter_mono (ae_mono (Measure.restrict_mono hAV le_rfl))
  have heq : ∀ z ∈ closedBall c R,
      (η (complexPlaneCoordinates.symm z)*v (complexPlaneCoordinates.symm z)) = (φ z).im := by
    intro z hz
    have hpK : complexPlaneCoordinates.symm z ∈ K := by
      exact ⟨z, hz, rfl⟩
    rw [hone _ (hKV hpK), one_mul]
    simp only [v, ContinuousLinearEquiv.apply_symm_apply]
  have hb := compact_sobolev_height_log_bound φ c W (hη.continuous.mul hv)
    hsη.mul_right hr hrR heq hx hy
  have hi : (∫ p in A, W.weakGrad p 0^2+W.weakGrad p 1^2) =
      ∫ p in A, D.imagGradient p 0^2+D.imagGradient p 1^2 := by
    apply integral_congr_ae
    filter_upwards [hgrad 0, hgrad 1] with p h0 h1
    rw [h0, h1]
  change _ ≤ 16*Real.pi*(∫ p in A, _) at hb ⊢
  rwa [hi] at hb

end CircleDomainRigidity

end

end OAI
