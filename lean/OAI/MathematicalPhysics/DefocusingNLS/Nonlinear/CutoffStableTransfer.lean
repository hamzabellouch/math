import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingStableSequence
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffProfilePhysicalLimit

namespace OAI

/-! # Uniform large-radius contraction for the actual sampled cutoff evolution -/

open Set Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def cutoffProfileCoefficient (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (L : Radius) : FourierL2 :=
  schwartzTorusSample a k L.1 ha1 hk L.2 (radianFourierKernel
    (cutoffProfileSchwartz L.1 (by linarith [L.2]) χ hχ Q hQ))

theorem sampledCutoffProfile_uniform_stable_contraction (a b k T Q C₀ c C R D η β : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 10 < k) (hT : 0 ≤ T)
    (hQ : 0 ≤ Q) (hC₀ : 0 ≤ C₀) (hc : 0 ≤ c) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hβ : 0 < β) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q₀ : HomogeneousY a k)
    (hQ₀ : ∀ y, homogeneousPhysicalCLM a k ha ha1 (by linarith) Q₀ y = Qp y)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 (by linarith) χ hχ Qp hQp L‖ ≤ Q)
    (hCb : ∀ (L : ℝ) (hL : 1 ≤ L) (f : FourierL2),
      ‖homogeneousLocalizationCLM a k L ha ha1 (by linarith) hL χ f‖ ≤ C₀ * ‖f‖)
    (π : HomogeneousY a k →L[ℝ] F) (R₀ : ℝ)
    (henergy : ∀ L : Radius, R₀ ≤ L.1 → ∀ w : FourierL2,
      -a * ‖expandingLowEnergy a k L.1 L.2 w‖ ^ 2 +
        (6 - 2 * a - k) * ‖expandingHighEnergy a k L.1 L.2 w‖ ^ 2 +
        2 * inner ℝ w (expandingLinearizedPotential a k L.1 ha ha1 (by linarith) L.2 m
          (cutoffProfileCoefficient a k ha1 (by linarith) χ hχ Qp hQp L) w) ≤
      -c * ‖w‖ ^ 2 + C * ‖expandingPhysicalBall a k L.1 R ha ha1 (by linarith) L.2 w‖ ^ 2)
    (hdecay : ∀ u : HomogeneousY a k, π u = 0 → ∀ t : Icc (0 : ℝ) T,
      ‖homogeneousLinearizedTrajectory a b k T ha ha1 (by linarith) hT m Q₀ u t‖ ≤
        D * Real.exp (-η * (t : ℝ)) * ‖u‖)
    (hsmall : escapedEnergyBound c (2 * η) 1
      (C * (‖homogeneousPhysicalCLM a k ha ha1 (by linarith)‖ * (D * C₀)) ^ 2) T < β ^ 2) :
    ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 → ∀ f : FourierL2, ‖f‖ ≤ 1 →
      π (homogeneousLocalizationCLM a k L.1 ha ha1 (by linarith) L.2 χ f) = 0 →
      ‖expandingProfileTrajectory a b k L.1 T ha ha1 (by linarith) L.2 hT m Q hQ
        (sampledCutoffProfilePath a k L.1 T ha ha1 (by linarith) L.2 χ hχ Qp hQp)
        (fun t => hqb (expandingRadiusCurve L.1 T L.2 t)) f ⟨T, hT, le_rfl⟩‖ < β := by
  classical
  have hk8 : 8 < k := by linarith
  by_contra h
  push Not at h
  choose L hL f hf hker hbad using fun n : ℕ => h (max R₀ (n : ℝ))
  have hLinf : Tendsto (fun n => (L n).1) atTop atTop :=
    tendsto_atTop_mono (fun n => (le_max_right R₀ (n : ℝ)).trans (hL n))
      tendsto_natCast_atTop_atTop
  let q := fun n => sampledCutoffProfilePath a k (L n).1 T ha ha1 hk8 (L n).2 χ hχ Qp hQp
  have hq (n : ℕ) (t : Icc (0 : ℝ) T) : ‖q n t‖ ≤ Q :=
    hqb (expandingRadiusCurve (L n).1 T (L n).2 t)
  have hqp (t : Icc (0 : ℝ) T) (y : E) :
      Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n).1 t)
        ha ha1 hk8 ((L n).2.trans (expandingRadius_ge (L n).1 t (L n).2 t.2.1)) (q n t) y)
        atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk8 Q₀ y)) := by
    rw [hQ₀]
    exact tendsto_sampledCutoffProfilePath_physical a k T ha ha1 hk8 χ hχ hχzero hχone
      Qp hQp (fun n => (L n).1) (fun n => (L n).2) hLinf t y
  have he (n : ℕ) (s : Icc (0 : ℝ) T) (w : FourierL2) :=
    henergy (expandingRadiusCurve (L n).1 T (L n).2 s)
      (((le_max_left R₀ (n : ℝ)).trans (hL n)).trans
        (expandingRadius_ge (L n).1 s (L n).2 s.2.1)) w
  have hs := expandingProfile_stable_sequence a b k T Q C₀ c C R D η β ha ha1 hk hT
    hQ hC₀ hc hC hD hβ m χ (1 / 2) (by norm_num) hχone hCb
    (fun n => (L n).1) (fun n => (L n).2) hLinf q hq f hf Q₀ π hker hqp he hdecay hsmall
  obtain ⟨n, hn⟩ := hs.exists
  exact (not_lt_of_ge (hbad n)) hn

end DefocusingNLS

end OAI
