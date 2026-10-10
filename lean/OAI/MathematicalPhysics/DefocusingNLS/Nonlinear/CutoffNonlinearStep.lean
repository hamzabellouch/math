import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingStepMap
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStepForcing

namespace OAI

/-! # The nonlinear step for the actual sampled cutoff profile

The fixed-step bounds follow from a smooth stationary profile with finitely
many symbol estimates.
-/

open Set
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_cutoffNonlinear_step (a b k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hM : 0 ≤ M)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχsupport : ∀ x : E, 1 ≤ ‖x‖ → χ x = 0) :
    ∃ N : ℕ, ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      (∀ y, stationarySimilarityDefect a b m Q y = 0) →
      ∃ δ L₀ C : ℝ, 0 < δ ∧ 1 ≤ L₀ ∧ 0 < C ∧ ∀ (L : ℝ) (hL : 1 ≤ L), L₀ ≤ L →
        let q := sampledCutoffProfilePath a k L M ha ha1 hk hL
          (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
        ∃ (V : {f : FourierL2 // ‖f‖ ≤ δ} → C(Icc (0 : ℝ) M, FourierL2))
          (h : {f : FourierL2 // ‖f‖ ≤ δ} → FourierL2),
          (∀ f, q + V f = expandingPicard a b k L M ha hk hL hM
            (expandingNonlinearReaction a k L M ha ha1 hk hL m)
            (q ⟨0, le_rfl, hM⟩ + f.1) (q + V f)) ∧
          (∀ f, ‖V f‖ ≤ C * (‖f.1‖ + L ^ (-2 - a))) ∧
          (∀ f, ∃ w : C(Icc (0 : ℝ) M, FourierL2),
            (∀ t : Icc (0 : ℝ) M, w t = expandingFreeStep a b k L t ha hk hL t.2.1 f.1 +
              expandingDuhamel a b k L ha hk hL t
                (expandingReactionHistory M hM
                  (expandingProfileReaction a k M ha ha1 hk m (expandingRadiusCurve L M hL) q 0) w)) ∧
            V f ⟨M, hM, le_rfl⟩ = w ⟨M, hM, le_rfl⟩ + h f) ∧
          (∀ z, z.1 = 0 → ‖h z‖ ≤ C * L ^ (-2 - a)) ∧
          (∀ d : ℝ, 0 < d → d ≤ δ → ∀ f j, ‖f.1‖ ≤ d → ‖j.1‖ ≤ d →
            ‖h f - h j‖ ≤ C * (d + L ^ (-2 - a)) * ‖f.1 - j.1‖) := by
  let hχzero := fun x : E => fun hx : 2 < ‖x‖ => hχsupport x (by linarith)
  obtain ⟨N, hN⟩ := exists_cutoffStep_profile_forcing_bounds a k ha ha1 hk m χ hχ hχone hχsupport
  refine ⟨N, ?_⟩
  intro Q hQ D hD hsymbol hstationary
  obtain ⟨R, B, hR, hB, hbounds⟩ := hN Q hQ D hD hsymbol
  obtain ⟨δ, A, hδ, hA, hstep⟩ := exists_expandingNonlinear_stepMap a b k M ha ha1 hk hM m R hR
  obtain ⟨L₀, hL₀, hsmall⟩ := exists_cutoffResidual_small_scale a B δ ha hδ
  let C := A * (1 + B)
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; nlinarith [mul_nonneg hA.le hB]
  have hABC : A * B ≤ C := by dsimp [C]; nlinarith
  refine ⟨δ, L₀, C, hδ, hL₀, hC, ?_⟩
  intro L hL hLlarge q
  let g := sampledCutoffDefectPath a k L M ha ha1 hk hL χ hχ hχone hχzero m Q hQ
  let G := B * L ^ (-2 - a)
  have hpow : 0 ≤ L ^ (-2 - a) := Real.rpow_nonneg (by linarith) _
  have hG : 0 ≤ G := mul_nonneg hB hpow
  have hGδ : G ≤ δ := hsmall L hLlarge
  have hq : ∀ t, ‖q t‖ ≤ R := fun t => (hbounds L M hL t).1
  have hg : ∀ t, ‖g t‖ ≤ G := fun t => (hbounds L M hL t).2
  obtain ⟨V, h, hV, hV_bound, hEnd, hZero, hLip⟩ := hstep L hL q g G hG hGδ hq hg
  have hcoeff (x : ℝ) (hx : 0 ≤ x) : A * (x + G) ≤ C * (x + L ^ (-2 - a)) := by
    calc
      A * (x + G) = A * x + (A * B) * L ^ (-2 - a) := by dsimp [G]; ring
      _ ≤ C * x + C * L ^ (-2 - a) := add_le_add
        (mul_le_mul_of_nonneg_right hAC hx) (mul_le_mul_of_nonneg_right hABC hpow)
      _ = C * (x + L ^ (-2 - a)) := by ring
  refine ⟨V, h, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    exact expandingPerturbation_add_mild a b k L M ha ha1 hk hL hM m q g (V f)
      (q ⟨0, le_rfl, hM⟩) f.1
      (sampledCutoffProfile_forced_mild a b k L M ha ha1 hk hL hM m ham
        χ hχ hχone hχzero Q hQ hstationary) (hV f)
  · intro f
    exact (hV_bound f).trans (hcoeff _ (norm_nonneg _))
  · intro f
    refine ⟨expandingProfileTrajectory a b k L M ha ha1 hk hL hM m R hR q hq f.1,
      expandingProfileTrajectory_eq a b k L M ha ha1 hk hL hM m R hR q hq f.1, hEnd f⟩
  · intro z hz
    exact (hZero z hz).trans (by
      change A * (B * L ^ (-2 - a)) ≤ C * L ^ (-2 - a)
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hABC hpow)
  · intro d hd hdδ f j hf hj
    exact (hLip d hd hdδ f j hf hj).trans
      (mul_le_mul_of_nonneg_right (hcoeff d hd.le) (norm_nonneg _))

end DefocusingNLS

end OAI
