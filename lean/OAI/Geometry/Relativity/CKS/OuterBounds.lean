import OAI.Geometry.Relativity.CKS.HeatUniform
import OAI.Geometry.Relativity.CKS.BendingFirstJet

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending CKSLocalBending
open scoped Topology ContDiff

lemma chartMass_angular_components {F : ℝ → E → ℝ} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : 0 < x 0) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (chartMass F t c) x = fderiv ℝ (F (t (x 0))) (sphereParam x) (thetaFrame x)) ∧
    (D (basis 2) (chartMass F t c) x / Real.sin (x 1) = fderiv ℝ (F (t (x 0))) (sphereParam x) (phiUnit x)) := by
  rw [chartMass_first hF ht hc hx 1 (by decide),chartMass_first hF ht hc hx 2 (by decide),
    angular_first (joint_slice hF _) 1,angular_first (joint_slice hF _) 2]
  simp [chartVector,phiFrame,hs]

lemma paddingMass_le_two {R r : ℝ} (hR : 1 ≤ R) (hr : R ≤ r) : paddingMass R r ≤ 2 := by
  have hRp : 0 < R := by linarith
  have hs : 1 ≤ Real.sqrt R := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hR)
  exact (paddingMass_bound hRp hr).trans ((div_le_iff₀ (Real.sqrt_pos.mpr hRp)).mpr (by linarith))

theorem outer_uniform_bounds (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ M B T : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ 0 ≤ T ∧
    ∀ R : ℝ, 12 ≤ R → ∀ x : Point, 3*R ≤ x 0 → Real.sin (x 1) ≠ 0 →
      |outerMass f₀ m R x| ≤ M ∧
      |(massJet (outerMass f₀ m R) x).laplace (Real.sin (x 1)) (Real.cos (x 1))| ≤ B ∧
      ‖sphereGrad (massJet (outerMass f₀ m R) x) (Real.sin (x 1))‖ ≤ B ∧
      outerA f₀ R x ^ 2 + (outerPhi f₀ R x / Real.sin (x 1))^2 ≤ T^2 := by
  obtain ⟨K,hK,h⟩ := canonical_uniform_data f₀ hf₀ m
  refine ⟨|m|+K+2,6*K,18*K,by positivity,by positivity,by positivity,?_⟩
  intro R hR x hr hs
  have hRp : 0 < R := by linarith
  have hrp : 0 < x 0 := by linarith
  obtain ⟨hm,hΔ,hg,hT⟩ := h (heatTime R (x 0)) (heatTime_nonneg hRp hrp) (sphereParam x) (sphereParam_norm x)
  have hf := canonicalF_joint f₀ hf₀ m
  have ht := heatTime_smooth hRp
  have hc := paddingMass_smooth hRp
  have hparts := chartMass_angular_components hf ht hc hrp hs
  have htheta : |D (basis 1) (outerMass f₀ m R) x| ≤ 3*K := by
    rw [show D (basis 1) (outerMass f₀ m R) x = _ from hparts.1]
    exact fderiv_bound hK hg (thetaFrame_component x)
  have hphi : |D (basis 2) (outerMass f₀ m R) x / Real.sin (x 1)| ≤ 3*K := by
    rw [show D (basis 2) (outerMass f₀ m R) x / Real.sin (x 1) = _ from hparts.2]
    exact fderiv_bound hK hg (phiUnit_component x)
  have ha : |outerA f₀ R x| ≤ 9*K := pair_bound hK hT (thetaFrame_component x) (thetaFrame_component x)
  have hb : |outerPhi f₀ R x / Real.sin (x 1)| ≤ 9*K := by
    change |(Real.sin (x 1) * pair _ (thetaFrame x) (phiUnit x)) / Real.sin (x 1)| ≤ _
    rw [mul_div_cancel_left₀ _ hs]
    exact pair_bound hK hT (thetaFrame_component x) (phiUnit_component x)
  refine ⟨?_,?_,?_,?_⟩
  · have hc0 := paddingMass_nonneg hRp hrp
    have hc2 := paddingMass_le_two (by linarith : 1 ≤ R) (by linarith : R ≤ x 0)
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hc0]; linarith)
  · change |(massJet (chartMass (canonicalF f₀ m) (heatTime R) (paddingMass R)) x).laplace _ _| ≤ _
    rw [chartMass_laplace hf ht hc hrp hs]
    linarith
  · have ht2 := pow_le_pow_left₀ (abs_nonneg _) htheta 2
    have hp2 := pow_le_pow_left₀ (abs_nonneg _) hphi 2
    rw [sq_abs] at ht2 hp2
    have he : ‖sphereGrad (massJet (outerMass f₀ m R) x) (Real.sin (x 1))‖^2 =
        (D (basis 1) (outerMass f₀ m R) x)^2 + (D (basis 2) (outerMass f₀ m R) x / Real.sin (x 1))^2 := by
      simp [sphereGrad,massJet,WithLp.prod_norm_sq_eq_of_L2,Real.norm_eq_abs, ← abs_div]
    nlinarith [norm_nonneg (sphereGrad (massJet (outerMass f₀ m R) x) (Real.sin (x 1)))]
  · have ha2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
    have hb2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at ha2 hb2
    nlinarith [sq_nonneg K]

lemma bending_reduced_bound : ∃ V : ℝ, 0 ≤ V ∧ ∀ R : ℝ, 12 ≤ R → ∀ r : ℝ, 0 < r →
    |deriv (bendingV R) r - bendingV R r/r| / A (bendingV R r) ≤ V/r := by
  obtain ⟨V,hV,h⟩ := bendingV_first_scaled
  refine ⟨V,hV,fun R hR r hr => ?_⟩
  have hA : 0 < A (bendingV R r) := by unfold A; positivity
  have hS : Real.sqrt (A (bendingV R r)) ≤ A (bendingV R r) := by
    have hh : 1 ≤ A (bendingV R r) := by unfold A; nlinarith [sq_nonneg (bendingV R r)]
    have he := Real.sq_sqrt hA.le
    have hs := Real.sqrt_nonneg (A (bendingV R r))
    nlinarith
  have hv := (h R hR r hr).trans (mul_le_mul_of_nonneg_left hS hV)
  have he : |r*deriv (bendingV R) r - bendingV R r| =
      |deriv (bendingV R) r - bendingV R r/r| * r := by
    calc
      _ = |(deriv (bendingV R) r - bendingV R r/r)*r| := by
        congr 1
        field_simp
      _ = _ := by rw [abs_mul,abs_of_pos hr]
  rw [he] at hv
  exact (div_le_div_iff₀ hA hr).mpr hv

end
end CKSSphericalChart

end

end OAI
