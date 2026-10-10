import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffNonlinearStep
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffProfileEndpoint

namespace OAI

/-! # The exact linear endpoint in the nonlinear cutoff step -/

open Set
open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem cutoffStep_linear_endpoint (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk χ hχ Qp hQp L‖ ≤ Q)
    (T : ℝ≥0) (L : Radius) (f : FourierL2) (w : C(Icc (0 : ℝ) T, FourierL2))
    (hw : ∀ t : Icc (0 : ℝ) T, w t = expandingFreeStep a b k L.1 t ha hk L.2 t.2.1 f +
      expandingDuhamel a b k L.1 ha hk L.2 t
        (expandingReactionHistory T T.2
          (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L.1 T L.2)
            (sampledCutoffProfilePath a k L.1 T ha ha1 hk L.2 χ hχ Qp hQp) 0) w)) :
    w ⟨T, T.2, le_rfl⟩ = cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T L f := by
  have he := expandingProfileTrajectory_unique a b k L.1 T ha ha1 hk L.2 T.2 m Q hQ
    (sampledCutoffProfilePath a k L.1 T ha ha1 hk L.2 χ hχ Qp hQp)
    (fun t => hqb (expandingRadiusCurve L.1 T L.2 t)) f w hw
  exact congrArg (fun v : C(Icc (0 : ℝ) T, FourierL2) => v ⟨T, T.2, le_rfl⟩) he

def HasCutoffNonlinearSteps (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk χ hχ Qp hQp L‖ ≤ Q)
    (T : ℝ≥0) : Prop :=
  ∃ δ L₀ C : ℝ, 0 < δ ∧ 1 ≤ L₀ ∧ 0 < C ∧ ∀ L : Radius, L₀ ≤ L.1 →
    let q := sampledCutoffProfilePath a k L.1 T ha ha1 hk L.2 χ hχ Qp hQp
    ∃ V : {f : FourierL2 // ‖f‖ ≤ δ} → C(Icc (0 : ℝ) T, FourierL2),
    ∃ h : {f : FourierL2 // ‖f‖ ≤ δ} → FourierL2,
      (∀ f, q + V f = expandingPicard a b k L.1 T ha hk L.2 T.2
        (expandingNonlinearReaction a k L.1 T ha ha1 hk L.2 m)
        (q ⟨0, le_rfl, T.2⟩ + f.1) (q + V f)) ∧
      (∀ f, ‖V f‖ ≤ C * (‖f.1‖ + L.1 ^ (-2 - a))) ∧
      (∀ f, V f ⟨T, T.2, le_rfl⟩ =
        cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T L f.1 + h f) ∧
      (∀ f, f.1 = 0 → ‖h f‖ ≤ C * L.1 ^ (-2 - a)) ∧
      (∀ d : ℝ, 0 < d → d ≤ δ → ∀ f j, ‖f.1‖ ≤ d → ‖j.1‖ ≤ d →
        ‖h f - h j‖ ≤ C * (d + L.1 ^ (-2 - a)) * ‖f.1 - j.1‖)

theorem exists_cutoffNonlinear_steps_order (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 1 ≤ ‖x‖ → χ x = 0) (T : ℝ≥0) :
    ∃ N : ℕ, ∀ (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (B : ℝ), 0 ≤ B →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 → ‖iteratedFDeriv ℝ n Qp y‖ ≤ B * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      (∀ y, stationarySimilarityDefect a b m Qp y = 0) →
      ∀ (Q : ℝ) (hQ : 0 ≤ Q),
      ∀ hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk
        (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Qp hQp L‖ ≤ Q,
      HasCutoffNonlinearSteps a b k ha ha1 hk m (χ.postcompCLM Complex.ofRealCLM)
        (hasCompactSupport_complexCutoff χ hχ) Qp hQp Q hQ hqb T := by
  obtain ⟨N, hN⟩ := exists_cutoffNonlinear_step a b k T ha ha1 hk T.2 m ham χ hχ hχone hχzero
  refine ⟨N, ?_⟩
  intro Qp hQp B hB hsymbol hstationary Q hQ hqb
  obtain ⟨δ, L₀, C, hδ, hL₀, hC, hstep⟩ := hN Qp hQp B hB hsymbol hstationary
  refine ⟨δ, L₀, C, hδ, hL₀, hC, ?_⟩
  intro L hL
  obtain ⟨V, h, hsol, hV, hend, hzero, hlip⟩ := hstep L.1 L.2 hL
  refine ⟨V, h, hsol, hV, ?_, hzero, hlip⟩
  intro f
  obtain ⟨w, hw, he⟩ := hend f
  rw [he, cutoffStep_linear_endpoint a b k ha ha1 hk m
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ)
    Qp hQp Q hQ hqb T L f.1 w hw]

end DefocusingNLS

end OAI
