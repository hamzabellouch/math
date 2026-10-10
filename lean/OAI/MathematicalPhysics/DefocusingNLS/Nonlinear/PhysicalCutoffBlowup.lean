import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalCutoffOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalStartingInverse
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStableBlowup

namespace OAI

/-! # The physical open-family orbits have the asserted finite-time singularity -/

open Set Filter Topology
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

def HasFiniteTimeSelfSimilarBlowup (k : ℝ) (hk : 6 < k) (m : ℕ)
    (a : ℝ) (f : FourierL2) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ x : SchrodingerTorus, ∃ c : ℝ, 0 < c ∧
    Ico 0 T ⊆ maximalSobolevInteractionDomain k hk m f ∧
    BddAbove (maximalSobolevInteractionDomain k hk m f) ∧
    sSup (maximalSobolevInteractionDomain k hk m f) = T ∧
    Tendsto (fun t => (T - t) ^ a *
      ‖sobolevTorusFunction k (maximalSobolevSchrodingerFlow k hk m f t) x‖)
      (𝓝[<] T) (𝓝 c) ∧
    ¬ ContinuousWithinAt (maximalSobolevSchrodingerFlow k hk m f) (Iio T) T

attribute [local irreducible] physicalStartingOperator expandingPhysicalInitialEquiv
  maximalSobolevSchrodingerFlow maximalSobolevInteractionDomain

theorem HasPhysicalCutoffOrbit.blowup (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (ham : 2 * a * m = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ y : E, ‖y‖ < 1 / 2 → χ y = 1)
    (hχzero : ∀ y : E, 2 < ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (hQzero : Q 0 ≠ 0)
    (f : FourierL2)
    (h : HasPhysicalCutoffOrbit a b k ha ha1 hk m
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ f) :
    HasFiniteTimeSelfSimilarBlowup k (by linarith) m a f := by
  obtain ⟨L, θ, x, u, hu, hu0, hsol, hdecay⟩ := h
  let g := expandingPhysicalInitialEquiv a k L.1 ha ha1 hk L.2 (u 0)
  let phase := Circle.exp (-θ)
  have hg : g = sobolevPhase phase (sobolevTranslation x f) := by
    dsimp only [g]
    rw [hu0, expandingPhysicalInitial_physicalStarting]
    rfl
  have hdom : maximalSobolevInteractionDomain k (by linarith) m g =
      maximalSobolevInteractionDomain k (by linarith) m f := by
    rw [hg, maximalSobolevInteractionDomain_phase, maximalSobolevInteractionDomain_translation]
  obtain ⟨hbounded, hend, hlimit⟩ := cutoffGlobal_blowup a b k L.1 ha ha1 hk L.2 m ham
    χ hχ hχone hχzero Q hQ hQzero u hu hsol hdecay
  change BddAbove (maximalSobolevInteractionDomain k (by linarith) m g) at hbounded
  change sSup (maximalSobolevInteractionDomain k (by linarith) m g) = L.1 ^ (-2 : ℝ) at hend
  change Tendsto (fun t => (L.1 ^ (-2 : ℝ) - t) ^ a *
    ‖sobolevTorusFunction k (maximalSobolevSchrodingerFlow k (by linarith) m g t) 0‖)
      (𝓝[<] (L.1 ^ (-2 : ℝ))) (𝓝 ‖Q 0‖) at hlimit
  have hT : 0 < L.1 ^ (-2 : ℝ) := Real.rpow_pos_of_pos (by linarith [L.2]) _
  have hsub : Ico 0 (L.1 ^ (-2 : ℝ)) ⊆ maximalSobolevInteractionDomain k (by linarith) m f := by
    intro t ht
    rw [← hdom]
    exact expandingGlobal_mem_maximal a b k L.1 ha ha1 hk L.2 m ham u hu hsol t ht
  have hlim : Tendsto (fun t => (L.1 ^ (-2 : ℝ) - t) ^ a *
      ‖sobolevTorusFunction k (maximalSobolevSchrodingerFlow k (by linarith) m f t) x‖)
      (𝓝[<] (L.1 ^ (-2 : ℝ))) (𝓝 ‖Q 0‖) := by
    apply hlimit.congr'
    filter_upwards [Ioo_mem_nhdsLT hT] with t ht
    rw [hg, maximalSobolev_phase_translation_norm k (by linarith) m phase x f t (hsub ⟨ht.1.le, ht.2⟩)]
  refine ⟨L.1 ^ (-2 : ℝ), hT, x, ‖Q 0‖, norm_pos_iff.mpr hQzero,
    hsub, ?_, ?_, hlim, ?_⟩
  · rwa [← hdom]
  · rwa [← hdom]
  · exact no_continuous_extension_of_positive_rescaled_norm
      (maximalSobolevSchrodingerFlow k (by linarith) m f)
      (sobolevPointEvaluation k (by linarith) x) _ a ‖Q 0‖ ha (norm_pos_iff.mpr hQzero)
      (sobolevPointEvaluation k (by linarith) x).continuous
      (by simpa only [sobolevTorusFunction_apply k (by linarith)] using hlim)

end DefocusingNLS

end OAI
