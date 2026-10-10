import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffForcingHistory
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingModeConverse

namespace OAI

/-! # The genuine sampled cutoff profile is a forced mild solution -/

open Set Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingModeRate_eq_radius (a b L t : ℝ) (hL : 0 < L) (n : frequencyLattice) :
    expandingModeRate a b L t n = -(a : ℂ) + Complex.I * ((b : ℂ) -
      ((((expandingRadius L t) ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * ((‖n‖ ^ 2 : ℝ) : ℂ)) := by
  have hR : 0 < expandingRadius L t := mul_pos hL (Real.exp_pos _)
  have hp : (expandingRadius L t) ^ (-2 : ℝ) = ((expandingRadius L t) ^ (2 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hR.le, Real.rpow_two]
  have he : ((expandingRadius L t) ^ (2 : ℕ))⁻¹ = L ^ (-2 : ℝ) * Real.exp (-t) := by
    have h := expandingRadius_residual_power 0 L t hL
    simp only [sub_zero, add_zero] at h
    rw [hp] at h
    simpa only [show -(2 : ℝ) * t / 2 = -t by ring] using h
  unfold expandingModeRate
  rw [he]
  push_cast
  ring

theorem hasDerivAt_sampledCutoffProfileHistory_coefficient (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hstationary : ∀ y, stationarySimilarityDefect a b m Q y = 0)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (n : frequencyLattice) :
    let u := sampledCutoffProfileHistory a k L T ha ha1 hk hL hT
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
    let r := sampledCutoffForcingHistory a k L T ha ha1 hk hL hT
      χ hχ hχone hχzero m Q hQ
    HasDerivAt (fun s => expandingFourierCoefficient a k (expandingRadius L s) (u s) n)
      (expandingModeRate a b L t n *
        expandingFourierCoefficient a k (expandingRadius L t) (u t) n +
        expandingFourierCoefficient a k (expandingRadius L t) (r t) n) t := by
  intro u r
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hRt : 1 ≤ expandingRadius L t := hL.trans (expandingRadius_ge L t hL ht.1.le)
  have hd := hasDerivAt_cutoffSampledMode_equation a b k L t ha ha1 hk hLp hRt
    m ham χ hχ hχone hχzero Q hQ hstationary n
  have he : (fun s => expandingFourierCoefficient a k (expandingRadius L s) (u s) n) =ᶠ[𝓝 t]
      cutoffSampledMode L (χ.postcompCLM Complex.ofRealCLM)
        (hasCompactSupport_complexCutoff χ hχ) Q hQ n := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact sampledCutoffProfileHistory_coefficient a k L T ha ha1 hk hL hT
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ s
        ⟨hs.1.le, hs.2.le⟩ n
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  rw [expandingModeRate_eq_radius a b L t hLp n,
    sampledCutoffProfileHistory_coefficient a k L T ha ha1 hk hL hT
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ)
      Q hQ t ⟨ht.1.le, ht.2.le⟩ n]
  have hforce : expandingFourierCoefficient a k (expandingRadius L t) (r t) n =
      (-Complex.I) * expandingFourierCoefficient a k (expandingRadius L t)
        (expandingOddPower a k (expandingRadius L t) ha ha1 hk hRt m (u t)) n +
      (-Complex.I) * physicalSchwartzCoefficient (expandingRadius L t) n
        (cutoffResidualSchwartz χ hχ hχone hχzero a (expandingRadius L t)
          (lt_of_lt_of_le zero_lt_one hRt) m Q hQ) := by
    change expandingCoefficientCLM a k (expandingRadius L t) n (r t) = _
    rw [show r t = _ from sampledCutoffForcingHistory_of_mem a k L T ha ha1 hk hL hT
      χ hχ hχone hχzero m Q hQ t ⟨ht.1.le, ht.2.le⟩,
      map_add, map_smul, map_smul]
    simp only [expandingCoefficientCLM_apply, smul_eq_mul]
    rw [sampledCutoffResidualHistory_of_mem a k L T ha ha1 hk hL hT
      χ hχ hχone hχzero m Q hQ t ⟨ht.1.le, ht.2.le⟩,
      schwartzTorusSample_coefficient]
    rfl
  have hu := sampledCutoffProfileHistory_of_mem a k L T ha ha1 hk hL hT
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ)
    Q hQ t ⟨ht.1.le, ht.2.le⟩
  change u t = _ at hu
  rw [hforce, hu]
  ring

theorem sampledCutoffProfile_mild (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hstationary : ∀ y, stationarySimilarityDefect a b m Q y = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    let u := sampledCutoffProfileHistory a k L T ha ha1 hk hL hT
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
    let r := sampledCutoffForcingHistory a k L T ha ha1 hk hL hT
      χ hχ hχone hχzero m Q hQ
    u t = expandingFreeStep a b k L t ha hk hL ht.1 (u 0) +
      expandingDuhamel a b k L ha hk hL t r := by
  intro u r
  exact expandingMild_of_mode_equation a b k L T ha hk hL u r
    (continuous_sampledCutoffProfileHistory a k L T ha ha1 hk hL hT
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ).continuousOn
    (continuous_sampledCutoffForcingHistory a k L T ha ha1 hk hL hT
      χ hχ hχone hχzero m Q hQ).continuousOn
    (fun s hs n => hasDerivAt_sampledCutoffProfileHistory_coefficient a b k L T
      ha ha1 hk hL hT m ham χ hχ hχone hχzero Q hQ hstationary s hs n) t ht

end DefocusingNLS

end OAI
