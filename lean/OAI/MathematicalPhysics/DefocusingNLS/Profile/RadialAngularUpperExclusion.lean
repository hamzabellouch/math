import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularScalarEstimates
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularComplexEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialZeroEnergyDecay
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoercivityBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexBoundaryEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralPressureCalculus

namespace OAI

/-! Upper real-part exclusion in every spherical-harmonic channel of the actual profile. -/

open Set Filter Asymptotics
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

/-- The four real equations with angular eigenvalue η = ℓ(ℓ+10). -/
def HasAngularSpectralSystem (n : ℕ) (z : ProfileMatchingBall) (η σ τ : ℝ)
    (f : Fin 4 → ℝ → ℝ) : Prop := ∀ r, 0 ≤ r →
  radialAngularScalarAction n z η (radialSpectralPressure n z) (f 0) r+radialMassDensity n z r*
    radialSpectralTest n z σ (-τ) (f 2) (f 3) r=0 ∧
  radialAngularScalarAction n z η (radialSpectralPressure n z) (f 1) r+radialMassDensity n z r*
    radialSpectralTest n z σ τ (f 3) (f 2) r=0 ∧
  radialAngularScalarAction n z η (fun _ => 0) (f 2) r-radialMassDensity n z r*
    radialSpectralTest n z σ (-τ) (f 0) (f 1) r=0 ∧
  radialAngularScalarAction n z η (fun _ => 0) (f 3) r-radialMassDensity n z r*
    radialSpectralTest n z σ τ (f 1) (f 0) r=0

theorem radialMatched_angular_upper_exclusion :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ η σ τ : ℝ, 0 ≤ η → 4 ≤ σ →
      ∀ f : Fin 4 → ℝ → ℝ, (∀ j, ContDiff ℝ 2 (f j)) →
      (∀ j, HasRadialEnergyDecay (f j)) → HasAngularSpectralSystem n z η σ τ f →
      ∀ j r, 0 ≤ r → f j r=0 := by
  obtain ⟨C,_hC,hC⟩ := radialMatched_spectral_coercivity_boundary
  obtain ⟨c,hc,hW⟩ := radialMatched_uniform_deformation
  filter_upwards [hC,hW,radialMatched_weight_bigO,radialMatched_angular_density_bigO] with n hCn hWn hBn hKn z hX hz η σ τ hη hσ f hf hd hs
  let q := radialSpectralPressure n z
  let E0 := fun R => radialAngularScalarForm n z η R q (f 0) (f 0)
  let E1 := fun R => radialAngularScalarForm n z η R q (f 1) (f 1)
  let E2 := fun R => radialAngularScalarForm n z η R (fun _ => 0) (f 2) (f 2)
  let E3 := fun R => radialAngularScalarForm n z η R (fun _ => 0) (f 3) (f 3)
  let E := fun R => E0 R+E1 R+E2 R+E3 R
  let B0 := fun R => radialAngularScalarBoundary n z η R σ (-τ) q (f 0) (f 1)
  let B1 := fun R => radialAngularScalarBoundary n z η R σ τ q (f 1) (f 0)
  let B2 := fun R => radialAngularScalarBoundary n z η R σ (-τ) (fun _ => 0) (f 2) (f 3)
  let B3 := fun R => radialAngularScalarBoundary n z η R σ τ (fun _ => 0) (f 3) (f 2)
  let H0 := fun R => radialHardyFlux (radialShootingA n) R*(f 0 R)^2
  let H1 := fun R => radialHardyFlux (radialShootingA n) R*(f 1 R)^2
  let B := fun R => C*H0 R+C*H1 R-(B0 R+B1 R+B2 R+B3 R)
  have hq := radialSpectralPressure_continuous n z hX hz
  have hqn : ∀ r, 0 ≤ r → 0 ≤ q r := fun r _ => radialSpectralPressure_nonneg n z r
  have hf1 (j : Fin 4) : ContDiff ℝ 1 (f j) := (hf j).of_le (by norm_num)
  have hE0 : ∀ R, 0 ≤ R → 0 ≤ E0 R := fun R hR =>
    radialAngularScalarForm_nonneg n z η R hη hR q (f 0) (fun r hr => hqn r hr.1)
  have hE1 : ∀ R, 0 ≤ R → 0 ≤ E1 R := fun R hR =>
    radialAngularScalarForm_nonneg n z η R hη hR q (f 1) (fun r hr => hqn r hr.1)
  have hE2 : ∀ R, 0 ≤ R → 0 ≤ E2 R := fun R hR =>
    radialAngularScalarForm_nonneg n z η R hη hR (fun _ => 0) (f 2) (fun _ _ => le_rfl)
  have hE3 : ∀ R, 0 ≤ R → 0 ≤ E3 R := fun R hR =>
    radialAngularScalarForm_nonneg n z η R hη hR (fun _ => 0) (f 3) (fun _ _ => le_rfl)
  have hEn : ∀ R, 0 ≤ R → 0 ≤ E R := fun R hR =>
    add_nonneg (add_nonneg (add_nonneg (hE0 R hR) (hE1 R hR)) (hE2 R hR)) (hE3 R hR)
  have hEm : MonotoneOn E (Ici 0) :=
    (((radialAngularScalarForm_mono n z hX hz η hη q (f 0) hq hqn (hf1 0)).add
      (radialAngularScalarForm_mono n z hX hz η hη q (f 1) hq hqn (hf1 1))).add
      (radialAngularScalarForm_mono n z hX hz η hη (fun _ => 0) (f 2) continuous_const
        (fun _ _ => le_rfl) (hf1 2))).add
      (radialAngularScalarForm_mono n z hX hz η hη (fun _ => 0) (f 3) continuous_const
        (fun _ _ => le_rfl) (hf1 3))
  obtain ⟨hM,hF,hP,hH⟩ := hBn z hX hz
  have hzero : (fun _ : ℝ => (0 : ℝ)) =O[atTop] (fun r : ℝ => r^(0 : ℝ)) :=
    isBigO_zero _ _
  have hB0 : Tendsto B0 atTop (nhds 0) :=
    radialAngularScalarBoundary_tendsto n z hX hz η σ (-τ) q (f 0) (f 1) hM hF hP (hKn z) (hd 0) (hd 1)
  have hB1 : Tendsto B1 atTop (nhds 0) :=
    radialAngularScalarBoundary_tendsto n z hX hz η σ τ q (f 1) (f 0) hM hF hP (hKn z) (hd 1) (hd 0)
  have hB2 : Tendsto B2 atTop (nhds 0) :=
    radialAngularScalarBoundary_tendsto n z hX hz η σ (-τ) (fun _ => 0) (f 2) (f 3) hM hF hzero (hKn z) (hd 2) (hd 3)
  have hB3 : Tendsto B3 atTop (nhds 0) :=
    radialAngularScalarBoundary_tendsto n z hX hz η σ τ (fun _ => 0) (f 3) (f 2) hM hF hzero (hKn z) (hd 3) (hd 2)
  have hH0 : Tendsto H0 atTop (nhds 0) := radialHardyBoundary_tendsto _ _ hH (hd 0)
  have hH1 : Tendsto H1 atTop (nhds 0) := radialHardyBoundary_tendsto _ _ hH (hd 1)
  have hB : Tendsto B atTop (nhds 0) := by
    simpa only [mul_zero,add_zero,sub_zero] using
      ((hH0.const_mul C).add (hH1.const_mul C)).sub (((hB0.add hB1).add hB2).add hB3)
  have hbound : ∀ R, 0 ≤ R → (3/4 : ℝ)*E R ≤ B R := by
    intro R hR
    have hv : ∀ r ∈ Icc 0 R, 0 ≤ radialMatchedVelocityRatio n z r :=
      fun r hr => hc.le.trans (hWn z hX hz r hr.1).2
    have hbase0 := hCn z hX hz R σ hR hσ (f 0) (hf1 0)
    have hbase1 := hCn z hX hz R σ hR hσ (f 1) (hf1 1)
    have h0 := radialAngularScalarForm_coercive_of_base n z η R σ C (H0 R) hη hR hσ
      q (deriv q) (f 0) hv (by simpa only [H0,mul_assoc] using hbase0)
    have h1 := radialAngularScalarForm_coercive_of_base n z η R σ C (H1 R) hη hR hσ
      q (deriv q) (f 1) hv (by simpa only [H1,mul_assoc] using hbase1)
    have hnonpress (j : Fin 4) := radialScalarForm_coercive n z hX hz R σ hR hσ
      (fun _ => 0) (fun _ => 0) (f j) (hf1 j) (fun _ _ => le_rfl)
      (fun r hr => hc.le.trans (hWn z hX hz r hr.1).1)
      (by simpa only [mul_zero,zero_mul,intervalIntegral.integral_zero] using
        radialScalarForm_nonneg n z R hR (fun _ => 0) (f j) (fun _ _ => le_rfl))
    have h2 := radialAngularScalarForm_coercive_of_base n z η R σ 0 0 hη hR hσ
      (fun _ => 0) (fun _ => 0) (f 2) hv (by simpa using hnonpress 2)
    have h3 := radialAngularScalarForm_coercive_of_base n z η R σ 0 0 hη hR hσ
      (fun _ => 0) (fun _ => 0) (f 3) hv (by simpa using hnonpress 3)
    simp only [mul_zero,add_zero] at h2 h3
    have he := radialAngularComplexSpectral_energy_boundary n z hX hz η R σ τ hR
      q (deriv q) (fun _ => 0) (fun _ => 0) hq.continuousOn
      (radialSpectralPressure_deriv_continuousOn n z hX hz R) continuousOn_const continuousOn_const
      (fun r _ => radialSpectralPressure_hasDerivAt n z hX hz r)
      (fun r _ => hasDerivAt_const r 0) f hf (fun r hr => hs r hr.1)
    dsimp only [E,E0,E1,E2,E3,B,B0,B1,B2,B3,H0,H1,q]
    linarith only [h0,h1,h2,h3,he]
  have hEZ := nonnegative_monotone_zero_of_vanishing_bound E B (3/4) (by norm_num)
    hEn hEm hB (eventually_ge_atTop (0 : ℝ) |>.mono fun R hR => hbound R hR)
  have hlim (j : Fin 4) : Tendsto (f j) atTop (nhds 0) :=
    (hd j).1.trans_tendsto (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<8))
  have hZ0 : ∀ R, 0 ≤ R → E0 R=0 := by
    intro R hR
    have he := hEZ R hR
    dsimp only [E] at he
    linarith [hE0 R hR,hE1 R hR,hE2 R hR,hE3 R hR]
  have hZ1 : ∀ R, 0 ≤ R → E1 R=0 := by
    intro R hR
    have he := hEZ R hR
    dsimp only [E] at he
    linarith [hE0 R hR,hE1 R hR,hE2 R hR,hE3 R hR]
  have hZ2 : ∀ R, 0 ≤ R → E2 R=0 := by
    intro R hR
    have he := hEZ R hR
    dsimp only [E] at he
    linarith [hE0 R hR,hE1 R hR,hE2 R hR,hE3 R hR]
  have hZ3 : ∀ R, 0 ≤ R → E3 R=0 := by
    intro R hR
    have he := hEZ R hR
    dsimp only [E] at he
    linarith [hE0 R hR,hE1 R hR,hE2 R hR,hE3 R hR]
  intro j
  fin_cases j
  · exact radialAngularScalarForm_all_zero_of_decay n z hX hz η hη q (f 0) hqn (hf1 0) (hlim 0) hZ0
  · exact radialAngularScalarForm_all_zero_of_decay n z hX hz η hη q (f 1) hqn (hf1 1) (hlim 1) hZ1
  · exact radialAngularScalarForm_all_zero_of_decay n z hX hz η hη (fun _ => 0) (f 2)
      (fun _ _ => le_rfl) (hf1 2) (hlim 2) hZ2
  · exact radialAngularScalarForm_all_zero_of_decay n z hX hz η hη (fun _ => 0) (f 3)
      (fun _ _ => le_rfl) (hf1 3) (hlim 3) hZ3

end DefocusingNLS

end OAI
