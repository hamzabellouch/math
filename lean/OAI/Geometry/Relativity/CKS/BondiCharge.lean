import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.BoostSubstitution

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere radialExtension radialExtension_smooth radialExtension_on_sphere surfaceMeasure)

def aspectPullback (e : ℝ) (p : E) (he : ‖p‖ < e) (M : Sphere → ℝ) (n : Sphere) : ℝ :=
  (denominator e (mass e p) p n)⁻¹ ^3 * M (boundary e p he n)

lemma nullDirection_smooth : ContMDiff (𝓡 2) 𝓘(ℝ,V) ∞ nullDirection :=
by
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun _ : Sphere => (1:ℝ)) := contMDiff_const
  exact hc.prodMk_space (contMDiff_coe_sphere (E := E) (n := 2))

lemma aspectPullback_smooth (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) : SmoothSphere (aspectPullback e p he M) := by
  have hd : ContDiff ℝ ∞ (denominator e (mass e p) p) :=
    (contDiff_const.add (ContDiff.inner ℝ contDiff_const contDiff_id)).div_const _
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun n : Sphere => denominator e (mass e p) p n) :=
    hd.comp_contMDiff (contMDiff_coe_sphere (E := E) (n := 2))
  exact ((hc.inv₀ (fun n => (denominator_pos he (mass_pos he) n).ne')).pow 3).mul
    (hM.comp (boundary_smooth e p he))

lemma rawCharge_integrable {M : Sphere → ℝ} (hM : SmoothSphere M) :
    Integrable (fun n => M n • nullDirection n) surfaceMeasure :=
  (hM.continuous.smul nullDirection_smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma rawCharge_test {M : Sphere → ℝ} (hM : SmoothSphere M) (L : V →L[ℝ] ℝ) :
    L (rawCharge M) = ∫ n : Sphere, M n * L (nullDirection n) ∂surfaceMeasure := by
  rw [rawCharge, ← L.integral_comp_comm (rawCharge_integrable hM)]
  simp only [map_smul, smul_eq_mul]

lemma transformedCharge_test (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) (L : V →L[ℝ] ℝ) :
    L (rawCharge (aspectPullback e p he M)) =
      L (boostCLM e (mass e p) (-p) (rawCharge M)) := by
  let B := boostCLM e (mass e p) (-p)
  let Q : Sphere → ℝ := fun n => M n * L (B (nullDirection n))
  have hQ : SmoothSphere Q := hM.mul
    (L.contMDiff.comp (B.contMDiff.comp nullDirection_smooth))
  have hi := boost_area_substitution he (mass_pos he) (mass_sq he) (radialExtension_smooth hQ)
  have hiR : (∫ n : Sphere, radialExtension Q n ∂surfaceMeasure) =
      L (B (rawCharge M)) := by
    change _ = (L.comp B) (rawCharge M)
    rw [rawCharge_test hM (L.comp B)]
    congr 1
    funext n
    rw [radialExtension_on_sphere]
    rfl
  have hiL : (∫ n : Sphere,
      (denominator e (mass e p) p n)⁻¹ ^2 * radialExtension Q (boundaryAmbient e (mass e p) p n) ∂surfaceMeasure) =
      L (rawCharge (aspectPullback e p he M)) := by
    rw [rawCharge_test (aspectPullback_smooth e p he hM)]
    congr 1
    funext n
    change (denominator e (mass e p) p n)⁻¹ ^2 * radialExtension Q (boundary e p he n) = _
    rw [radialExtension_on_sphere]
    dsimp only [Q, B, nullDirection]
    rw [inverse_null_boundary e p he n, map_smul, smul_eq_mul]
    dsimp only [aspectPullback, nullDirection]
    ring
  rw [hiL,hiR] at hi
  exact hi

theorem rawCharge_lorentz (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) :
    rawCharge (aspectPullback e p he M) = boostCLM e (mass e p) (-p) (rawCharge M) := by
  apply Prod.ext
  · exact transformedCharge_test e p he hM (ContinuousLinearMap.fst ℝ ℝ E)
  · ext i
    exact transformedCharge_test e p he hM ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ ℝ E))

theorem bondiCharge_lorentz (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) :
    bondiCharge (aspectPullback e p he M) = boostCLM e (mass e p) (-p) (bondiCharge M) := by
  simp only [bondiCharge, rawCharge_lorentz e p he hM, map_smul]

end
end CKSLorentz

end

end OAI
