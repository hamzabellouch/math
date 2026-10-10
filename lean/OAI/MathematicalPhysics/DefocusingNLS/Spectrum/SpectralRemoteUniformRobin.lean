import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalIncoming
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteReconstruction

namespace OAI

/-! Uniform physical Robin data obtained from the remote ODE and outgoing
logarithmic symbols. No endpoint condition is assumed. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_uniform_robin
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) (sigma : ℝ)
    (b eta omega : ℕ → ℝ) (c : ℕ → ℝ → Fin 2 → ℝ)
    (B : ℕ → ℝ → SpectralRemoteOperator) (Y : ℕ → ℝ → SpectralRemoteSpace)
    (hc : HasUniformLogJetBound L 0 c) (hB : HasUniformLogJetBound L 0 B)
    (hci : ∀ᶠ n in atTop, HasLogJetBound 0 (c n))
    (hBi : ∀ᶠ n in atTop, HasLogJetBound 0 (B n))
    (hYi : ∀ᶠ n in atTop, HasLogJetBound sigma (Y n))
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ k, |c n t k| ≤ 1/32)
    (hformula : ∀ n t, c n t = spectralRemoteEndpointCoefficient (omega n) (eta n) (Real.exp t))
    (hb : ∀ᶠ n in atTop, 0 ≤ b n ∧ b n ≤ 1)
    (hode : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      HasDerivAt (Y n) (((Real.exp t : ℂ)^2 • spectralRemotePhysicalLeading (c n t)+B n t) (Y n t)) t) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
      let q := spectralRemoteLiouvilleState (Real.exp t) (Y n t)
      ‖spectralPhysicalDerivativeMap q-
        homogeneousDiagonal
          (Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency 1 (b n) (eta n) (omega n) (Real.exp t)) : ℂ))
          (-Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) (b n) (eta n) (omega n) (Real.exp t)) : ℂ))
            (spectralPhysicalValueMap q)‖ ≤ A/(Real.exp t)*‖spectralPhysicalValueMap q‖ := by
  obtain ⟨m,_,I,hI,hinc⟩ := spectralRemote_physical_incoming hL sigma c B Y hc hB hci hBi hYi hsmall hode
  let Lambda := fun n t => spectralRemoteLeadingOperator (c n t) t
  let S := fun n t => spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c n t))
  let B' := spectralRemoteInitialRemainder c B
  let T := spectralRemoteReductionFrame Lambda B' spectralRemoteBlockOperator S m
  have hd := spectralRemote_root_reduction hL hc hsmall B'
    (spectralRemote_initial_remainder_symbol hc hsmall hB) m
  obtain ⟨D,hD,hDb⟩ := hd.2.2.1.bound 0
  let K := max D I
  have hK : 0 ≤ K := hD.trans (le_max_left _ _)
  have he : Tendsto (fun n => K*Real.exp (-2*L n)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (by norm_num : (-2 : ℝ) < 0)).2 hL)
    simpa only [mul_zero,Function.comp_def] using hh.const_mul K
  refine ⟨8*K+22,by positivity,?_⟩
  filter_upwards [hinc,hDb,hd.2.2.2.2,hsmall,hb,
    he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/6)),
    hL.eventually (eventually_ge_atTop (Real.log 8))] with n hin hDn hun hcn hbn hsmalln hLn
  intro t ht
  have hEt : (8 : ℝ) ≤ Real.exp t := by
    calc
      8 = Real.exp (Real.log 8) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr (hLn.trans ht.le)
  have hEs : K/(Real.exp t)^2 ≤ 1/6 := by
    rw [spectralRemote_exp_inv_sq]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left ht.le (by norm_num : (-2 : ℝ) ≤ 0))) hK).trans hsmalln.le
  have hTb : ‖T n t-1‖ ≤ K/(Real.exp t)^2 := by
    rw [spectralRemote_exp_inv_sq]
    have hh := hDn t ht
    simp only [iteratedDeriv_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left D I) (Real.exp_pos _).le)
  have hcE := hformula n t
  have hcp : |omega n/(Real.exp t)^2+eta n/(Real.exp t)^4| ≤ 1/32 := by
    have hh := hcn t ht 0
    rw [hcE] at hh
    exact hh
  have hcm : |-omega n/(Real.exp t)^2+eta n/(Real.exp t)^4| ≤ 1/32 := by
    have hh := hcn t ht 1
    rw [hcE] at hh
    exact hh
  have hZ : spectralRemotePhysicalReducedSolution c B Y m n t =
      Ring.inverse (T n t) (Ring.inverse (spectralRemoteInitialFrame
        (spectralRemoteEndpointCoefficient (omega n) (eta n) (Real.exp t))) (Y n t)) := by
    change Ring.inverse (T n t) (Ring.inverse (spectralRemoteInitialFrame (c n t)) (Y n t)) = _
    rw [hcE]
  have hi := hin t ht
  have hi' : ‖spectralPhysicalDerivativeMap
      (Ring.inverse (T n t) (Ring.inverse (spectralRemoteInitialFrame
        (spectralRemoteEndpointCoefficient (omega n) (eta n) (Real.exp t))) (Y n t)))‖ ≤
      K/(Real.exp t)^2*‖Ring.inverse (T n t) (Ring.inverse (spectralRemoteInitialFrame
        (spectralRemoteEndpointCoefficient (omega n) (eta n) (Real.exp t))) (Y n t))‖ := by
    rw [← hZ,spectralRemote_exp_inv_sq]
    exact hi.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right D I) (Real.exp_pos _).le) (norm_nonneg _))
  exact spectralRemote_physical_robin (b n) (eta n) (omega n) (Real.exp t) K (T n t) (Y n t)
    hEt hbn.1 hbn.2 hK hcp hcm (hun t ht).2.1 hEs hTb hi'

end DefocusingNLS

end OAI
