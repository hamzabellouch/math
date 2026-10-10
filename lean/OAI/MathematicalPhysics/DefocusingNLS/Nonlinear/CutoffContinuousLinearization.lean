import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffContinuousStep
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStepLinearization

namespace OAI

/-! # Continuous nonlinear cutoff steps with the exact linear endpoint -/

open Set
open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

def HasContinuousCutoffNonlinearSteps (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk χ hχ Qp hQp L‖ ≤ Q)
    (T : ℝ≥0) : Prop :=
  ∃ δ L₀ C : ℝ, 0 < δ ∧ 1 ≤ L₀ ∧ 0 < C ∧
    ∃ V : {L : ℝ // 1 ≤ L ∧ L₀ ≤ L} × {f : FourierL2 // ‖f‖ ≤ δ} →
      C(Icc (0 : ℝ) T, FourierL2),
    ∃ h : {L : ℝ // 1 ≤ L ∧ L₀ ≤ L} × {f : FourierL2 // ‖f‖ ≤ δ} → FourierL2,
      Continuous V ∧ Continuous h ∧
      (∀ z, let q := sampledCutoffProfilePath a k z.1.1 T ha ha1 hk z.1.2.1 χ hχ Qp hQp
        q + V z = expandingPicard a b k z.1.1 T ha hk z.1.2.1 T.2
          (expandingNonlinearReaction a k z.1.1 T ha ha1 hk z.1.2.1 m)
          (q ⟨0, le_rfl, T.2⟩ + z.2.1) (q + V z)) ∧
      (∀ z, ‖V z‖ ≤ C * (‖z.2.1‖ + z.1.1 ^ (-2 - a))) ∧
      (∀ z, V z ⟨T, T.2, le_rfl⟩ =
        cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T
          ⟨z.1.1, z.1.2.1⟩ z.2.1 + h z) ∧
      (∀ z, z.2.1 = 0 → ‖h z‖ ≤ C * z.1.1 ^ (-2 - a)) ∧
      (∀ d : ℝ, 0 < d → d ≤ δ → ∀ L f j, ‖f.1‖ ≤ d → ‖j.1‖ ≤ d →
        ‖h (L, f) - h (L, j)‖ ≤ C * (d + L.1 ^ (-2 - a)) * ‖f.1 - j.1‖)

theorem exists_cutoffContinuousNonlinear_steps_order (a b k : ℝ)
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
      HasContinuousCutoffNonlinearSteps a b k ha ha1 hk m (χ.postcompCLM Complex.ofRealCLM)
        (hasCompactSupport_complexCutoff χ hχ) Qp hQp Q hQ hqb T := by
  obtain ⟨N, hN⟩ := exists_cutoffNonlinear_step_continuous a b k T ha ha1 hk T.2 m ham
    χ hχ hχone hχzero
  refine ⟨N, ?_⟩
  intro Qp hQp B hB hsymbol hstationary Q hQ hqb
  obtain ⟨δ, L₀, C, hδ, hL₀, hC, V, h, hcV, hch, hsol, hV, hend, hzero, hlip⟩ :=
    hN Qp hQp B hB hsymbol hstationary
  refine ⟨δ, L₀, C, hδ, hL₀, hC, V, h, hcV, hch, hsol, hV, ?_, hzero, hlip⟩
  intro z
  obtain ⟨w, hw, he⟩ := hend z
  rw [he, cutoffStep_linear_endpoint a b k ha ha1 hk m
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ)
    Qp hQp Q hQ hqb T ⟨z.1.1, z.1.2.1⟩ z.2.1 w hw]

end DefocusingNLS

end OAI
