import OAI.Geometry.Relativity.CKS.BoostIntegral

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Topology
open MeasureTheory
open CKSSphericalHarmonics (puncturedSpace surfaceMeasure)

lemma flowEnergy_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) : flowEnergy (m⁻¹ • p) 1 = e/m := by
  have hs : (e/m)^2 = 1+‖m⁻¹ • p‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm0)]
    field_simp
    nlinarith
  have hf := flowEnergy_sq (m⁻¹ • p) 1
  simp only [one_pow, one_mul] at hf
  nlinarith [flowEnergy_pos (m⁻¹ • p) 1, div_pos (energy_pos he) hm0]

lemma flowD_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) (n : E) :
    flowD (m⁻¹ • p) 1 n = denominator e m p n := by
  simp only [flowD, flowEnergy_normalized he hm0 hm, one_mul, inner_smul_left, conj_trivial, denominator]
  ring

lemma flowS_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) (n : E) :
    flowS (m⁻¹ • p) 1 n = boundarySpatial e m p n := by
  simp only [flowS, flowCoeff, flowEnergy_normalized he hm0 hm, one_pow, boundarySpatial,
    inner_smul_left, conj_trivial, smul_smul]
  congr 1
  congr 1
  field_simp

lemma flowPhi_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) (n : E) :
    flowPhi (m⁻¹ • p) 1 n = boundaryAmbient e m p n := by
  rw [flowPhi, flowD_normalized he hm0 hm, flowS_normalized he hm0 hm]
  rfl

theorem boost_area_substitution {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    ∫ n : Sphere, (denominator e m p n)⁻¹ ^2 * F (boundaryAmbient e m p n) ∂surfaceMeasure =
      ∫ n : Sphere, F n ∂surfaceMeasure := by
  have h := flow_area_substitution (m⁻¹ • p) hF 1
  simpa only [flowD_normalized he hm0 hm, flowPhi_normalized he hm0 hm] using h

lemma inverse_null_boundary (e : ℝ) (p : E) (he : ‖p‖ < e) (n : Sphere) :
    boostCLM e (mass e p) (-p) (1,(boundary e p he n:E)) =
      (denominator e (mass e p) p n)⁻¹ • ((1:ℝ),(n:E)) := by
  have h := congrArg (boostCLM e (mass e p) (-p)) (boundary_null e p he n)
  simp only [map_smul, boostCLM_apply] at h
  rw [boost_neg_inverse (mass_pos he).ne' (add_pos (energy_pos he) (mass_pos he)).ne' (mass_sq he)] at h
  rw [h, smul_smul, inv_mul_cancel₀ (denominator_pos he (mass_pos he) n).ne', one_smul]
  rfl

end
end CKSLorentz

end

end OAI
