import OAI.Analysis.Mahler.ComplexSphereIntegral

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
namespace MahlerStokes

/-- The positive radial parametrization, packaged as a homeomorphism so
change of variables is valid even before proving integrability. -/
def positiveSphereDilation (k : ℕ) (r : ℝ) (hr : 0 < r) :
    sphere (0 : EuclideanSpace ℂ (Fin k)) 1 ≃ₜ sphere (0 : EuclideanSpace ℂ (Fin k)) r := by
  refine { toEquiv := ?_, continuous_toFun := ?_, continuous_invFun := ?_ }
  · exact {
      toFun := fun z => ⟨r • (z : EuclideanSpace ℂ (Fin k)), by
        have hz : ‖(z : EuclideanSpace ℂ (Fin k))‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using z.property
        simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz]⟩
      invFun := fun z => ⟨r⁻¹ • (z : EuclideanSpace ℂ (Fin k)), by
        have hz : ‖(z : EuclideanSpace ℂ (Fin k))‖ = r := by simpa only [mem_sphere, dist_zero_right] using z.property
        simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz, hr.ne']⟩
      left_inv := fun z => Subtype.ext (by simp [smul_smul, hr.ne'])
      right_inv := fun z => Subtype.ext (by simp [smul_smul, hr.ne']) }
  · apply continuous_induced_rng.2
    change Continuous (fun z : sphere (0 : EuclideanSpace ℂ (Fin k)) 1 => r • (z : EuclideanSpace ℂ (Fin k)))
    exact (continuous_const : Continuous (fun _ : sphere (0 : EuclideanSpace ℂ (Fin k)) 1 => r)).smul continuous_subtype_val
  · apply continuous_induced_rng.2
    change Continuous (fun z : sphere (0 : EuclideanSpace ℂ (Fin k)) r => r⁻¹ • (z : EuclideanSpace ℂ (Fin k)))
    exact (continuous_const : Continuous (fun _ : sphere (0 : EuclideanSpace ℂ (Fin k)) r => r⁻¹)).smul continuous_subtype_val

/-- The actual radius-r sphere integral. Its measure is the positive dilation
of volume.toSphere with tangential Jacobian r^(2k-1), exactly the construction
used in Mahler.radiusSphereArea. No integration law is an assumption. -/
theorem sphereFlux_eq_positiveRadiusAreaIntegral {d k : ℕ} (h : d+1 = k*2)
    {r : ℝ} (hr : 0 < r)
    (ω : (Fin (d+1) → ℝ) → (Fin (d+1) → ℝ) [⋀^Fin d]→L[ℝ] ℝ)
    (hω : ContinuousOn ω {x | radiusSq x = r^2}) :
    sphereFlux r ω =
      ∫ z : sphere (0 : EuclideanSpace ℂ (Fin k)) r,
        coordinateSphereDensity r ω
          (ofLp ((complexSphereCoordinates d k h).symm (r⁻¹ • (z : EuclideanSpace ℂ (Fin k)))))
        ∂(ENNReal.ofReal (r^(2*k-1)) •
          (volume : Measure (EuclideanSpace ℂ (Fin k))).toSphere.map (positiveSphereDilation k r hr)) := by
  rw [integral_smul_measure,
    (positiveSphereDilation k r hr).measurableEmbedding.integral_map]
  have hd : 2*k-1 = d := by omega
  rw [hd, ENNReal.toReal_ofReal (pow_nonneg hr.le d)]
  simp only [smul_eq_mul]
  rw [sphereFlux_eq_complexSphereIntegral h hr ω hω]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  simp [positiveSphereDilation, smul_smul, hr.ne']

end MahlerStokes

end

end OAI
