import OAI.Geometry.Relativity.CKS.SurfaceNormalization
import OAI.Geometry.Relativity.CKS.RadialTail

namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter MeasureTheory CKSSphericalHarmonics CKSSphericalChart CKSBending CKSInducedSphere
open scoped Topology ContDiff

lemma surfaceMeasure_real : surfaceMeasure.real univ = 4*Real.pi := by
  rw [← sphereArea_eq_four_pi,sphereArea,sphereIntegral_apply]
  simp

lemma canonicalF_mean (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m t : ℝ) :
    (∫ n : Sphere, canonicalF f₀ m t n ∂surfaceMeasure) = m*(4*Real.pi) := by
  let p := heatPolynomials f₀
  have hp := smoothDatum_rapid f₀ hf₀
  let q : C(Sphere,ℝ) := sphereEval (MvPolynomial.C m) + sphereHeatJet p (0,[]) t
  have he : (fun x : Sphere => canonicalF f₀ m t x) = fun x => q x := by
    funext x
    change m + jointHeatSeries p (0,[]) (t,x) = sphereEval (MvPolynomial.C m) x + sphereHeatJet p (0,[]) t x
    rw [sphereHeatJet_eq p hp]
    simp [sphereEval]
  rw [he,← sphereIntegral_apply]
  change sphereIntegral (sphereEval (MvPolynomial.C m) + sphereHeatJet p (0,[]) t) = _
  rw [map_add,sphereIntegral_constant,sphereHeatJet_mean_zero p hp (heatPolynomials_harmonic f₀),
    add_zero,sphereArea_eq_four_pi]

lemma canonicalF_continuous_sphere (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m t : ℝ) :
    Continuous (fun n : Sphere => canonicalF f₀ m t n) := by
  apply ((joint_slice (canonicalF_joint f₀ hf₀ m) t).continuousOn).comp_continuous continuous_subtype_val
  intro n
  exact ne_of_apply_ne norm (by simp)

def tailSphereMass (f₀ : C(Sphere,ℝ)) (m R r : ℝ) (n : Sphere) : ℝ :=
  paddingMass R r + canonicalF f₀ m (heatTime R r) n

lemma tailSphereMass_continuous (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R r : ℝ) :
    Continuous (tailSphereMass f₀ m R r) :=
  continuous_const.add (canonicalF_continuous_sphere f₀ hf₀ m (heatTime R r))

lemma tailSphereMass_mean (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R r : ℝ) :
    (∫ n, tailSphereMass f₀ m R r n ∂surfaceMeasure) = (m+paddingMass R r)*(4*Real.pi) := by
  unfold tailSphereMass
  rw [integral_add (integrable_const _) ((canonicalF_continuous_sphere f₀ hf₀ m _).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)),integral_const,canonicalF_mean f₀ hf₀ m,
    smul_eq_mul,surfaceMeasure_real]
  ring

lemma tailSphereMass_bound (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ R r : ℝ, 1 ≤ R → 3*R ≤ r → ∀ n : Sphere,
      |tailSphereMass f₀ m R r n| ≤ B := by
  obtain ⟨K,hK,hbound⟩ := canonical_uniform_data f₀ hf₀ m
  refine ⟨|m|+K+3,by positivity,?_⟩
  intro R r hR hr n
  have hRp : 0 < R := by linarith
  have hrp : 0 < r := by linarith
  have hc := paddingMass_bound hRp (by linarith : R ≤ r)
  have hs : 1 ≤ Real.sqrt R := by simpa using Real.sqrt_le_sqrt hR
  have ht := heatTime_nonneg hRp hrp
  have hf := (hbound (heatTime R r) ht n (by simp)).1
  have hc' : paddingMass R r ≤ 2 := hc.trans ((div_le_iff₀ (Real.sqrt_pos.mpr hRp)).mpr (by linarith))
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg (paddingMass_nonneg hRp hrp)]
  linarith

lemma denominator_lower {F B r : ℝ} (hB : 0 ≤ B) (hF : |F| ≤ B) (hr : 4*B+1 ≤ r) :
    (1:ℝ)/2 ≤ 1-2*F/r := by
  have hrp : 0 < r := by linarith
  have hf := (le_abs_self F).trans hF
  have hh : 2*F/r ≤ (1:ℝ)/2 := (div_le_iff₀ hrp).mpr (by linarith)
  linarith

lemma rational_mass_error {F B r : ℝ} (hB : 0 ≤ B) (hF : |F| ≤ B) (hr : 4*B+1 ≤ r) :
    |F/(1-2*F/r)-F| ≤ 4*B^2/r := by
  have hrp : 0 < r := by linarith
  have hd := denominator_lower hB hF hr
  have hdp : 0 < 1-2*F/r := by linarith
  have hs : F^2 ≤ B^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg F) hB).mpr hF
  have hden : r-2*F ≠ 0 := by have hh := (le_abs_self F).trans hF; linarith
  have he : F/(1-2*F/r)-F = (2*F^2/r)/(1-2*F/r) := by
    apply (eq_div_iff hdp.ne').mpr
    rw [sub_mul,div_mul_cancel₀ _ hdp.ne']
    field_simp [hrp.ne']
    ring
  rw [he,abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hdp).mpr
  have hnn : 0 ≤ 4*B^2/r := by positivity
  have hh := mul_le_mul_of_nonneg_left hd hnn
  calc
    2*F^2/r ≤ 2*B^2/r := div_le_div_of_nonneg_right (by nlinarith) hrp.le
    _ = (4*B^2/r)*((1:ℝ)/2) := by ring
    _ ≤ _ := hh

def reducedEnergy (f₀ : C(Sphere,ℝ)) (m R r : ℝ) : ℝ :=
  (4*Real.pi)⁻¹ * ∫ n : Sphere,
    tailSphereMass f₀ m R r n/(1-2*tailSphereMass f₀ m R r n/r) ∂surfaceMeasure

lemma reducedEnergy_error (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R r B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ n : Sphere, |tailSphereMass f₀ m R r n| ≤ B)
    (hr : 4*B+1 ≤ r) :
    |reducedEnergy f₀ m R r-(m+paddingMass R r)| ≤ 4*B^2/r := by
  let F := tailSphereMass f₀ m R r
  have hf : Continuous F := tailSphereMass_continuous f₀ hf₀ m R r
  have hd : ∀ n : Sphere, 1-2*F n/r ≠ 0 := fun n => ne_of_gt (by
    have hh := denominator_lower hB (hF n) hr; linarith)
  have hq : Continuous (fun n => F n/(1-2*F n/r)) :=
    hf.div (continuous_const.sub ((continuous_const.mul hf).div_const r)) hd
  have hfi : Integrable F surfaceMeasure := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hqi : Integrable (fun n => F n/(1-2*F n/r)) surfaceMeasure := hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn := norm_integral_le_of_norm_le_const (μ := surfaceMeasure)
    (f := fun n => F n/(1-2*F n/r)-F n)
    (Filter.Eventually.of_forall (fun n => by simpa only [Real.norm_eq_abs] using rational_mass_error hB (hF n) hr))
  rw [integral_sub hqi hfi,surfaceMeasure_real,Real.norm_eq_abs] at hn
  have hm : (∫ n : Sphere, F n ∂surfaceMeasure) = (m+paddingMass R r)*(4*Real.pi) := tailSphereMass_mean f₀ hf₀ m R r
  rw [hm] at hn
  have hc : 0 < 4*Real.pi := by positivity
  have he : reducedEnergy f₀ m R r-(m+paddingMass R r) =
      (4*Real.pi)⁻¹*((∫ n : Sphere, F n/(1-2*F n/r) ∂surfaceMeasure)-(m+paddingMass R r)*(4*Real.pi)) := by
    unfold reducedEnergy
    dsimp only [F]
    rw [mul_sub]
    congr 1
    field_simp
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr hc)]
  calc
    _ ≤ (4*Real.pi)⁻¹*((4*B^2/r)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hc.le)
    _ = _ := by field_simp

theorem reducedEnergy_limit (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 1 ≤ R) :
    Tendsto (reducedEnergy f₀ m R) atTop (𝓝 (m+paddingCharge R)) := by
  obtain ⟨B,hB,hbound⟩ := tailSphereMass_bound f₀ hf₀ m
  have herr : Tendsto (fun r => reducedEnergy f₀ m R r-(m+paddingMass R r)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero,Real.norm_eq_abs]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
      (g := fun r : ℝ => 4*B^2/r)
    · filter_upwards [eventually_ge_atTop (3*R),eventually_ge_atTop (4*B+1)] with r hr hlarge
      exact reducedEnergy_error f₀ hf₀ m R r B hB.le (hbound R r hR hr) hlarge
    · exact tendsto_const_nhds.div_atTop tendsto_id
  have hmean := (tendsto_const_nhds (x := m)).add (paddingCharge_limit (by linarith : 0 < R))
  have hh := herr.add hmean
  simpa only [sub_add_cancel,zero_add] using hh

end
end CKSADM

end

end OAI
