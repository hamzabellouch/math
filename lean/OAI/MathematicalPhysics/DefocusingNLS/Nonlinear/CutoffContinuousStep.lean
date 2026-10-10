import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingStepMapContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffPathContinuity

namespace OAI

/-! # The continuous nonlinear step for the actual cutoff profile

The same family has the exact unforced mild equation, a continuous endpoint
remainder, and the scale-dependent remainder estimates.  The stationary
profile and its finite symbol bounds are the hypotheses for the step
estimates.
-/

open Set
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] expandingPicard expandingPerturbationReaction
  expandingProfileTrajectory sampledCutoffProfilePath sampledCutoffDefectPath

theorem exists_cutoffNonlinear_step_continuous (a b k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχsupport : ∀ x : E, 1 ≤ ‖x‖ → χ x = 0) :
    ∃ N : ℕ, ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      (∀ y, stationarySimilarityDefect a b m Q y = 0) →
      ∃ δ L₀ C : ℝ, 0 < δ ∧ 1 ≤ L₀ ∧ 0 < C ∧
        let q := fun L : {L : ℝ // 1 ≤ L ∧ L₀ ≤ L} =>
          sampledCutoffProfilePath a k L.1 T ha ha1 hk L.2.1
            (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
        ∃ (V : {L : ℝ // 1 ≤ L ∧ L₀ ≤ L} × {f : FourierL2 // ‖f‖ ≤ δ} →
            C(Icc (0 : ℝ) T, FourierL2))
          (h : {L : ℝ // 1 ≤ L ∧ L₀ ≤ L} × {f : FourierL2 // ‖f‖ ≤ δ} → FourierL2),
          Continuous V ∧ Continuous h ∧
          (∀ z, q z.1 + V z = expandingPicard a b k z.1.1 T ha hk z.1.2.1 hT
            (expandingNonlinearReaction a k z.1.1 T ha ha1 hk z.1.2.1 m)
            (q z.1 ⟨0, le_rfl, hT⟩ + z.2.1) (q z.1 + V z)) ∧
          (∀ z, ‖V z‖ ≤ C * (‖z.2.1‖ + z.1.1 ^ (-2 - a))) ∧
          (∀ z, ∃ w : C(Icc (0 : ℝ) T, FourierL2),
            (∀ t : Icc (0 : ℝ) T, w t =
              expandingFreeStep a b k z.1.1 t ha hk z.1.2.1 t.2.1 z.2.1 +
                expandingDuhamel a b k z.1.1 ha hk z.1.2.1 t
                  (expandingReactionHistory T hT
                    (expandingProfileReaction a k T ha ha1 hk m
                      (expandingRadiusCurve z.1.1 T z.1.2.1) (q z.1) 0) w)) ∧
            V z ⟨T, hT, le_rfl⟩ = w ⟨T, hT, le_rfl⟩ + h z) ∧
          (∀ z, z.2.1 = 0 → ‖h z‖ ≤ C * z.1.1 ^ (-2 - a)) ∧
          (∀ d : ℝ, 0 < d → d ≤ δ → ∀ L f j, ‖f.1‖ ≤ d → ‖j.1‖ ≤ d →
            ‖h (L, f) - h (L, j)‖ ≤ C * (d + L.1 ^ (-2 - a)) * ‖f.1 - j.1‖) := by
  let hχzero := fun x : E => fun hx : 2 < ‖x‖ => hχsupport x (by linarith)
  obtain ⟨N, hN⟩ := exists_cutoffStep_profile_forcing_bounds a k ha ha1 hk m χ hχ hχone hχsupport
  refine ⟨N, ?_⟩
  intro Q hQ D hD hsymbol hstationary
  obtain ⟨R, B, hR, hB, hbounds⟩ := hN Q hQ D hD hsymbol
  obtain ⟨δ, A, hδ, hA, hstep⟩ :=
    exists_expandingNonlinear_stepMap_continuous a b k T ha ha1 hk hT m R hR
  obtain ⟨L₀, hL₀, hsmall⟩ := exists_cutoffResidual_small_scale a B δ ha hδ
  let P := {L : ℝ // 1 ≤ L ∧ L₀ ≤ L}
  let l : P → {L : ℝ // 1 ≤ L} := fun L => ⟨L.1, L.2.1⟩
  have hl : Continuous l := continuous_subtype_val.subtype_mk _
  let q : P → C(Icc (0 : ℝ) T, FourierL2) := fun L =>
    sampledCutoffProfilePath a k L.1 T ha ha1 hk L.2.1
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
  let g : P → C(Icc (0 : ℝ) T, FourierL2) := fun L =>
    sampledCutoffDefectPath a k L.1 T ha ha1 hk L.2.1 χ hχ hχone hχzero m Q hQ
  let G : P → ℝ := fun L => B * L.1 ^ (-2 - a)
  have hq : Continuous q := (continuous_sampledCutoffProfilePath a k T ha ha1 hk
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ).comp hl
  have hg : Continuous g := (continuous_sampledCutoffDefectPath a k T ha ha1 hk
    χ hχ hχone hχzero m Q hQ).comp hl
  have hqb : ∀ L t, ‖q L t‖ ≤ R := fun L t => (hbounds L.1 T L.2.1 t).1
  have hgb : ∀ L t, ‖g L t‖ ≤ G L := fun L t => (hbounds L.1 T L.2.1 t).2
  have hG : ∀ L : P, 0 ≤ G L :=
    fun L => mul_nonneg hB (Real.rpow_nonneg (by linarith [L.2.1]) _)
  have hGδ : ∀ L : P, G L ≤ δ := fun L => hsmall L.1 L.2.2
  specialize hstep P l q g G hl hq hg hG hGδ hqb hgb
  obtain ⟨V, h, hcV, hch, hV, hVbound, hEnd, hzero, hlip⟩ := hstep
  let C := A * (1 + B)
  have hC : 0 < C := by dsimp [C]; positivity
  have hcoeff (L : P) (x : ℝ) (hx : 0 ≤ x) :
      A * (x + G L) ≤ C * (x + L.1 ^ (-2 - a)) := by
    have hp : 0 ≤ L.1 ^ (-2 - a) := Real.rpow_nonneg (by linarith [L.2.1]) _
    have hAA : A ≤ C := by dsimp [C]; nlinarith [mul_nonneg hA.le hB]
    have hAB : A * B ≤ C := by dsimp [C]; nlinarith
    calc
      A * (x + G L) = A * x + (A * B) * L.1 ^ (-2 - a) := by dsimp [G]; ring
      _ ≤ C * x + C * L.1 ^ (-2 - a) := add_le_add
        (mul_le_mul_of_nonneg_right hAA hx) (mul_le_mul_of_nonneg_right hAB hp)
      _ = C * (x + L.1 ^ (-2 - a)) := by ring
  refine ⟨δ, L₀, C, hδ, hL₀, hC, V, h, hcV, hch, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact expandingPerturbation_add_mild a b k z.1.1 T ha ha1 hk z.1.2.1 hT m
      (q z.1) (g z.1) (V z) (q z.1 ⟨0, le_rfl, hT⟩) z.2.1
      (sampledCutoffProfile_forced_mild a b k z.1.1 T ha ha1 hk z.1.2.1 hT m ham
        χ hχ hχone hχzero Q hQ hstationary) (hV z)
  · intro z
    exact (hVbound z).trans (hcoeff z.1 _ (norm_nonneg _))
  · intro z
    refine ⟨expandingProfileTrajectory a b k z.1.1 T ha ha1 hk z.1.2.1 hT
      m R hR (q z.1) (hqb z.1) z.2.1, ?_, hEnd z⟩
    exact expandingProfileTrajectory_eq a b k z.1.1 T ha ha1 hk z.1.2.1 hT
      m R hR (q z.1) (hqb z.1) z.2.1
  · intro z hz
    have hb := hcoeff z.1 0 (by norm_num)
    simp only [zero_add] at hb
    exact (hzero z hz).trans hb
  · intro d hd hdδ L f j hf hj
    exact (hlip d hd hdδ L f j hf hj).trans
      (mul_le_mul_of_nonneg_right (hcoeff L d hd.le) (norm_nonneg _))

end DefocusingNLS

end OAI
