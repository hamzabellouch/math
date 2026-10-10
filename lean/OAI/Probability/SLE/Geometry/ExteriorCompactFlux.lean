import OAI.Probability.SLE.Geometry.AnnulusPolarIntegral

namespace OAI

/-! A compactly supported test with nonpositive exterior Laplacian
integral has nonnegative inward boundary flux. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SLEExactGauge

lemma exterior_compact_flux_nonneg {v : ℂ → ℝ} {a : ℝ} (ha : 0<a)
    (hv : ∀ z : ℂ, a≤‖z‖ → ContDiffAt ℝ 2 v z)
    (hs : HasCompactSupport v)
    (hneg : (∫ z in {z : ℂ | a<‖z‖}, (Δ v) z)≤0) :
    0≤∫ θ in -Real.pi..Real.pi, radialLaplacianFlux v (a,θ) := by
  obtain ⟨M,hM,hMs⟩ := hs.isBounded.exists_pos_norm_lt
  let R := max a M+1
  have haR : a≤R := by dsimp [R]; linarith [le_max_left a M]
  have hMR : M<R := by dsimp [R]; linarith [le_max_right a M]
  have hnot (z : ℂ) (hz : R≤‖z‖) : z∉tsupport v := by
    intro hs'
    exact (hMs z hs').not_ge (hMR.le.trans hz)
  have hzero (z : ℂ) (hz : R≤‖z‖) : (Δ v) z=0 := by
    have hh := (laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp (hnot z hz))).self_of_nhds
    simpa only [Pi.zero_def,laplacian_const,Pi.zero_apply] using hh
  have hrestrict : (∫ z in {z : ℂ | a<‖z‖}, (Δ v) z)=
      ∫ z in {z : ℂ | a<‖z‖ ∧ ‖z‖<R}, (Δ v) z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_lt continuous_const continuous_norm).measurableSet
      (fun z hz => hz.1)
    intro z hz
    apply hzero z
    exact le_of_not_gt (fun h => hz.2 ⟨hz.1,h⟩)
  have hrzero (θ : ℝ) : radialLaplacianFlux v (R,θ)=0 := by
    have hn : R≤‖polarPoint R θ‖ := by
      rw [polarPoint_norm,abs_of_pos (ha.trans_le haR)]
    simp only [radialLaplacianFlux,fderiv_of_notMem_tsupport ℝ (hnot _ hn),
      zero_apply,mul_zero]
  have he := annulus_integral_laplacian_flux ha haR (fun z hz _ => hv z hz)
  rw [hrestrict,he] at hneg
  simp only [hrzero,intervalIntegral.integral_zero,zero_sub] at hneg
  linarith

end SLEExactGauge

end

end OAI
