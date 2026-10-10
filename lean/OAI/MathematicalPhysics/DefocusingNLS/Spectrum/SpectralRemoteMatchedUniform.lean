import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteExteriorSubsequence
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalNonlinearity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteMatchedCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMovingDeformation

namespace OAI

/-! The actual matched profiles supply the uniform physical coefficient
symbols used by the remote outgoing Robin estimate. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem spectralRemote_matched_uniform_coefficients
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    HasUniformLogJetBound L (-2) (fun i t =>
      spectralDiagonalCoefficient (s i+radialInnerShootingThreshold)
        (radialMatchedProfile (s i) (z i) (Real.exp t))) ∧
    HasUniformLogJetBound L (-2) (fun i t =>
      spectralCrossCoefficient (s i+radialInnerShootingThreshold)
        (radialMatchedProfile (s i) (z i) (Real.exp t))) := by
  let m := fun i => s i+radialInnerShootingThreshold
  have hms : StrictMono m := fun i j hij => Nat.add_lt_add_right (hs hij) _
  let nu := fun i => radialShootingNu (m i) (z i)
  let q := fun i t => (radialExteriorCanonical (nu i) (m i) (radialShootingM (z i))
    (Real.log innerBoundaryRadius) t).1
  have hnu : Tendsto nu atTop (𝓝 (-2*radialShootingQ z0)) :=
    radialShootingNu_subsequence_tendsto m hms z z0 hz
  have ha := continuous_radialShootingM.continuousAt.tendsto.comp hz
  obtain ⟨delta,rho,hd,hdm,hasmall,hrho,hupper,hlower⟩ := radialShooting_free_annulus z0
  obtain ⟨hq,r,hr,hr1,hqb⟩ := spectralRemote_exterior_subsequence_symbol m hms nu
    (fun i => radialShootingM (z i)) (radialShootingQ z0) (radialShootingM z0)
    (by simp [radialShootingQ]) hnu ha delta rho (Real.log innerBoundaryRadius)
    hd hdm hasmall hrho hupper hlower L hL
  have hscale : ∀ i, 2*(m i : ℝ)*(nu i).re = -2 := by
    intro i
    have he : (nu i).re = -2*radialShootingA (s i) := by
      dsimp only [nu,m]
      rw [radialShootingNu_physical]
      simp [Complex.mul_re,Complex.mul_im]
    rw [he]
    have hh := radialShootingA_power (s i) (profileMatchingParameter (z i))
    change 2*radialShootingA (s i)*(m i : ℝ) = 1 at hh
    nlinarith
  let B := ‖-2*radialShootingQ z0‖+1
  have hB : 0 ≤ B := by positivity
  have hnuB : ∀ᶠ i in atTop, |(nu i).im| ≤ B := by
    filter_upwards [hnu.norm.eventually (gt_mem_nhds
      (show ‖-2*radialShootingQ z0‖ < B from by dsimp only [B]; linarith))] with i hi
    exact (Complex.abs_im_le_norm _).trans hi.le
  obtain ⟨hD,hC⟩ := spectralRemote_physical_nonlinear_symbols hL m hms.tendsto_atTop nu
    hscale B hB hnuB q hq r hr hr1 hqb
  have heq : ∀ᶠ i in atTop, ∀ t ∈ Ioi (L i),
      Complex.exp (nu i*(t : ℂ))*q i t = radialMatchedProfile (s i) (z i) (Real.exp t) := by
    filter_upwards [hL.eventually (eventually_ge_atTop (Real.log innerBoundaryRadius))] with i hi
    intro t ht
    have hr0 : 0 < innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
    have hrt : innerBoundaryRadius < Real.exp t := by
      simpa only [Real.exp_log hr0] using Real.exp_lt_exp.mpr (hi.trans_lt ht)
    simp only [radialMatchedProfile,ite_eq_right hrt.not_ge,radialShootingExteriorProfile,
      radialPhysicalExterior,Real.log_exp,nu,m,q]
  exact ⟨hD.eventually_congr (heq.mono (fun i hi t ht => congrArg _ (hi t ht))),
    hC.eventually_congr (heq.mono (fun i hi t ht => congrArg _ (hi t ht)))⟩

end DefocusingNLS

end OAI
