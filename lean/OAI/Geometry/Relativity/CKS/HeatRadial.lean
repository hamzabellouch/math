import OAI.Geometry.Relativity.CKS.RadialProfiles
import OAI.Geometry.Relativity.CKS.HeatChartTensor

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

lemma chartMass_radial {F : ℝ → E → ℝ} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : x ∈ positiveChart) :
    D (basis 0) (chartMass F t c) x =
      deriv c (x 0) + deriv (fun s => F s (sphereParam x)) (t (x 0)) * deriv t (x 0) := by
  have hfull := (chartMass_smooth hF ht hc).contDiffAt (positiveChart_open.mem_nhds hx)
  rw [D_line (hfull.differentiableAt (by simp))]
  have hpt := (ht.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp)
  have hpc := (hc.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp)
  have htime := (joint_time hF (sphereParam_mem x)).differentiable (by simp) (t (x 0))
  have hcomp : HasDerivAt (fun r => F (t r) (sphereParam x))
      (deriv (fun s => F s (sphereParam x)) (t (x 0)) * deriv t (x 0)) (x 0) :=
    htime.hasDerivAt.comp (x 0) hpt.hasDerivAt
  have hsum := hpc.hasDerivAt.add hcomp
  have hshift : HasDerivAt (fun s : ℝ => x 0 + s) 1 0 :=
    (hasDerivAt_id (0:ℝ)).const_add (x 0)
  have hs' : HasDerivAt (fun r => c r + F (t r) (sphereParam x))
      (deriv c (x 0) + deriv (fun s => F s (sphereParam x)) (t (x 0)) * deriv t (x 0))
      ((fun s : ℝ => x 0+s) 0) := by
    convert! hsum using 1
    simp only [add_zero]
  have hd := hs'.comp (0:ℝ) hshift
  simpa [chartMass,basis,sphereParam,Function.comp_def] using hd.deriv

lemma canonicalF_heat (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : ‖x‖ = 1) :
    deriv (fun s => canonicalF f₀ m s x) t = roundLaplacian (canonicalF f₀ m t) x := by
  have hp := smoothDatum_rapid f₀ hf₀
  unfold canonicalF
  rw [deriv_const_add,roundLaplacian_const_add,roundLaplacian_eq_Casimir
    (spatialHeat_smooth _ hp _ t) hx]
  exact spatialHeat_equation _ hp (heatPolynomials_harmonic f₀) _ ht (by intro h; simp [h] at hx)

lemma canonicalF_initial (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) (hb : Balanced f₀ m)
    (x : Sphere) : canonicalF f₀ m 0 x = f₀ x := by
  have hp := smoothDatum_rapid f₀ hf₀
  have h := sphereHeatJet_initial (radialExtension_smooth hf₀)
    (m := m) (by rwa [radial_restriction f₀ hf₀])
  rw [radial_restriction f₀ hf₀] at h
  have he := congrArg (fun q : C(Sphere,ℝ) => q x) h
  change sphereEval (MvPolynomial.C m) x + sphereHeatJet (heatPolynomials f₀) (0,[]) 0 x = f₀ x at he
  have hc : sphereEval (MvPolynomial.C m) x = m := by simp [sphereEval]
  rw [hc,sphereHeatJet_eq _ hp] at he
  exact he

def outerMass (f₀ : C(Sphere,ℝ)) (m R : ℝ) : Point → ℝ :=
  chartMass (canonicalF f₀ m) (heatTime R) (paddingMass R)
def outerA (f₀ : C(Sphere,ℝ)) (R : ℝ) : Point → ℝ :=
  chartTensorA (canonicalT f₀) (heatTime R)
def outerPhi (f₀ : C(Sphere,ℝ)) (R : ℝ) : Point → ℝ :=
  chartTensorPhi (canonicalT f₀) (heatTime R)

lemma outerMass_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (outerMass f₀ m R) positiveChart :=
  chartMass_smooth (canonicalF_joint f₀ hf₀ m) (heatTime_smooth hR) (paddingMass_smooth hR)
lemma outerA_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (outerA f₀ R) positiveChart :=
  chartTensorA_smooth (canonicalT_joint f₀ hf₀) (heatTime_smooth hR)
lemma outerPhi_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (outerPhi f₀ R) positiveChart :=
  chartTensorPhi_smooth (canonicalT_joint f₀ hf₀) (heatTime_smooth hR)

lemma outerMass_heat (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0 < R) {x : Point} (hr : 3*R ≤ x 0) (hs : Real.sin (x 1) ≠ 0) :
    D (basis 0) (outerMass f₀ m R) x =
      bendingZeta R (x 0) * (massJet (outerMass f₀ m R) x).laplace
        (Real.sin (x 1)) (Real.cos (x 1)) / (2*x 0*A (bendingV R (x 0))) +
      1/(x 0*Real.sqrt (x 0)) := by
  have hrp : 0 < x 0 := by linarith
  have ht := heatTime_smooth hR
  have hc := paddingMass_smooth hR
  have hf := canonicalF_joint f₀ hf₀ m
  unfold outerMass
  rw [chartMass_radial hf ht hc hrp,chartMass_laplace hf ht hc hrp hs,
    (paddingMass_hasDerivAt hR hrp).deriv,(heatTime_hasDerivAt hR hrp).deriv,
    canonicalF_heat f₀ hf₀ m (heatTime_nonneg hR hrp) (sphereParam_norm x),
    paddingWeight_one hR (by linarith)]
  unfold paddingDensity heatDensity A
  ring

lemma outer_divergence (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0 < R) {x : Point} (hr : 0 < x 0) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (outerA f₀ R) x + D (basis 2) (outerPhi f₀ R) x / Real.sin (x 1)^2 +
      2*Real.cos (x 1)*outerA f₀ R x / Real.sin (x 1) = D (basis 1) (outerMass f₀ m R) x) ∧
    (D (basis 1) (outerPhi f₀ R) x - D (basis 2) (outerA f₀ R) x +
      Real.cos (x 1)*outerPhi f₀ R x / Real.sin (x 1) = D (basis 2) (outerMass f₀ m R) x) :=
  canonical_chart_divergence f₀ hf₀ m (heatTime_smooth hR) (paddingMass_smooth hR) hr hs

end
end CKSSphericalChart

end

end OAI
