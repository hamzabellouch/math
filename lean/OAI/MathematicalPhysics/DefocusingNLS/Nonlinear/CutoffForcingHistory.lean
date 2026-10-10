import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffResidualDuhamel
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffApproximateMode

namespace OAI

/-! # Continuous histories for the actual approximate nonlinear solution -/

open Set
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def sampledCutoffProfileHistory (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : ℝ → FourierL2 :=
  fun t => sampledCutoffProfilePath a k L T ha ha1 hk hL χ hχ Q hQ (projIcc 0 T hT t)

theorem continuous_sampledCutoffProfileHistory (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (sampledCutoffProfileHistory a k L T ha ha1 hk hL hT χ hχ Q hQ) :=
  (sampledCutoffProfilePath a k L T ha ha1 hk hL χ hχ Q hQ).continuous.comp continuous_projIcc

theorem sampledCutoffProfileHistory_of_mem (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (t : ℝ) (ht : t ∈ Icc 0 T) :
    sampledCutoffProfileHistory a k L T ha ha1 hk hL hT χ hχ Q hQ t =
      schwartzTorusSample a k (expandingRadius L t) ha1 hk
        (hL.trans (expandingRadius_ge L t hL ht.1))
        (radianFourierKernel (cutoffProfileSchwartz (expandingRadius L t)
          (mul_pos (lt_of_lt_of_le zero_lt_one hL) (Real.exp_pos _)) χ hχ Q hQ)) := by
  unfold sampledCutoffProfileHistory
  rw [projIcc_of_mem _ ht]
  rfl

noncomputable def sampledCutoffNonlinearPath (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (m : ℕ) : C(Icc (0 : ℝ) T, FourierL2) where
  toFun t := expandingOddPower a k (expandingRadiusCurve L T hL t).1
    ha ha1 hk (expandingRadiusCurve L T hL t).2 m
      (sampledCutoffProfilePath a k L T ha ha1 hk hL χ hχ Q hQ t)
  continuous_toFun := (continuous_expandingOddPower_scale a k ha ha1 hk m).comp
    ((expandingRadiusCurve L T hL).continuous.prodMk
      (sampledCutoffProfilePath a k L T ha ha1 hk hL χ hχ Q hQ).continuous)

noncomputable def sampledCutoffForcingPath (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : C(Icc (0 : ℝ) T, FourierL2) :=
  (-Complex.I) • sampledCutoffNonlinearPath a k L T ha ha1 hk hL
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ m +
    (-Complex.I) • sampledCutoffResidualPath a k L T ha ha1 hk hL χ hχ hχone hχzero m Q hQ

noncomputable def sampledCutoffForcingHistory (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : ℝ → FourierL2 :=
  fun t => sampledCutoffForcingPath a k L T ha ha1 hk hL χ hχ hχone hχzero m Q hQ
    (projIcc 0 T hT t)

theorem continuous_sampledCutoffForcingHistory (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (sampledCutoffForcingHistory a k L T ha ha1 hk hL hT χ hχ hχone hχzero m Q hQ) :=
  (sampledCutoffForcingPath a k L T ha ha1 hk hL χ hχ hχone hχzero m Q hQ).continuous.comp
    continuous_projIcc

theorem sampledCutoffForcingHistory_of_mem (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (t : ℝ) (ht : t ∈ Icc 0 T) :
    sampledCutoffForcingHistory a k L T ha ha1 hk hL hT χ hχ hχone hχzero m Q hQ t =
      (-Complex.I) • expandingOddPower a k (expandingRadius L t) ha ha1 hk
        (hL.trans (expandingRadius_ge L t hL ht.1)) m
        (sampledCutoffProfileHistory a k L T ha ha1 hk hL hT
          (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ t) +
      (-Complex.I) • sampledCutoffResidualHistory a k L T ha ha1 hk hL hT
        χ hχ hχone hχzero m Q hQ t := by
  unfold sampledCutoffForcingHistory sampledCutoffProfileHistory sampledCutoffResidualHistory
  rw [projIcc_of_mem _ ht]
  rfl

theorem sampledCutoffProfileHistory_coefficient (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (t : ℝ) (ht : t ∈ Icc 0 T)
    (n : frequencyLattice) :
    expandingFourierCoefficient a k (expandingRadius L t)
      (sampledCutoffProfileHistory a k L T ha ha1 hk hL hT χ hχ Q hQ t) n =
      cutoffSampledMode L χ hχ Q hQ n t := by
  rw [sampledCutoffProfileHistory_of_mem a k L T ha ha1 hk hL hT χ hχ Q hQ t ht,
    schwartzTorusSample_coefficient]
  exact (cutoffSampledMode_eq_physical L (lt_of_lt_of_le zero_lt_one hL)
    χ hχ Q hQ n t).symm

theorem sampledCutoffResidualHistory_of_mem (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (t : ℝ) (ht : t ∈ Icc 0 T) :
    sampledCutoffResidualHistory a k L T ha ha1 hk hL hT χ hχ hχone hχzero m Q hQ t =
      schwartzTorusSample a k (expandingRadius L t) ha1 hk
        (hL.trans (expandingRadius_ge L t hL ht.1)) (radianFourierKernel
          (cutoffResidualSchwartz χ hχ hχone hχzero a (expandingRadius L t)
            (mul_pos (lt_of_lt_of_le zero_lt_one hL) (Real.exp_pos _)) m Q hQ)) := by
  unfold sampledCutoffResidualHistory
  rw [projIcc_of_mem _ ht]
  rfl

end DefocusingNLS

end OAI
